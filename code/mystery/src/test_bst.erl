-module(test_bst).

-import(bst, [empty/0, insert/3, delete/2, find/2, union/2]).
-import(bst, [valid/1, to_sorted_list/1, keys/1]).

-include_lib("eqc/include/eqc.hrl").

%% The following two lines are super bad style, except during development
-compile(nowarn_export_all).
-compile(export_all).


%%% A non-symbolic generator for bst, parameterised by key and value generators
% bst(Key, Value) ->
%     ?LET(KVS, eqc_gen:list({Key, Value}),
%          lists:foldl(fun({K,V}, T) -> insert(K, V, T) end,
%                      empty(),
%                      KVS)).

% example key and value generators
int_key() -> eqc_gen:int().
atom_key() -> eqc_gen:elements([a,b,c,d,e,f,g,h]).

int_value() -> eqc_gen:int().

%%% symbolic generator for bst
bst(Key, Value) ->
    ?LET(KVS, eqc_gen:list({Key, Value}),
         %{call, lists, foldl, [...]}
         %lists:foldl(
         {call, lists, foldl, [            
                    fun({K,V}, T) -> {call, bst, insert, [K, V, T]} end,
                     {call, bst, empty, []},
                     KVS]}
                    ).

%implement quality check for gen
%perhaps also letshrink


%%% we are unsure why eval needs to be used twice in the properties
%%% we think it might be because of the nested symbolic call inside the genereator

%%% invariant properties

% all generated bst are valid
prop_arbitrary_valid() ->
    ?FORALL(T, bst(atom_key(), int_value()),
            valid(eval(eval(T)))).

% if we insert into a valid tree it stays valid
prop_insert_valid() ->
    ?FORALL({K, V, T}, {atom_key(), int_value(), bst(atom_key(), int_value())},
            valid (insert(eval(eval(K)), eval(eval(V)), eval(eval(T))))).

%should also stay valid for other operations



%%% -- postcondition properties

% For two given keys they are either equal and you find the value one of them has inserted or they are different
% and you output the result of a search (which will be nothing) 
prop_insert_post() ->
    ?FORALL({K1, K2, V, T},
            {atom_key(), atom_key(), int_value(), bst(atom_key(), int_value())},
            eqc:equals(find(eval(eval(K2)), insert(eval(eval(K1)), eval(eval(V)), eval(eval(T)))),
                       case eval(eval(K1)) =:= eval(eval(K2)) of
                           true ->  {found, eval(eval(V))};
                           false -> find(eval(eval(K2)), eval(eval(T)))
                       end)).


% Find the value of a key that was just inserted
prop_find_post_present() ->
  % ∀ k v t. find k (insert k v t) === {found, v}
    ?FORALL({K, V, T}, {atom_key(), int_value(), bst(atom_key(), int_value())},
            eqc:equals(find(eval(eval(K)), insert(eval(eval(K)), eval(eval(V)), eval(eval(T)))),
                       {found, eval(eval(V))})).

% When you search for a key after you have deleted it, it should result nothing
prop_find_post_absent() ->
    % ∀ k t. find k (delete k t) === nothing
    ?FORALL({K, T},
            {atom_key(), bst(atom_key(), int_value())},
            eqc:equals(find(eval(eval(K)), delete(eval(eval(K)), eval(eval(T)))), nothing)).


%%% -- metamorphic properties

%% the size is larger after an insert
prop_size_insert() ->
    % ∀ k v t. size (insert k v t) >= size t
    ?FORALL({K, V, T}, {atom_key(), int_value(), bst(atom_key(), int_value())},
            bst:size(insert(eval(eval(K)), eval(eval(V)), eval(eval(T)))) >= bst:size(eval(eval(T)))).

prop_size_empty() ->
    % size (empty()) == 0
    eqc:equals(bst:size(eval(eval(empty()))), 0).

prop_size_delete() ->
    % ∀ k t. size (delete k t) == (size t) -1
    ?FORALL({K, T}, {atom_key(), bst(atom_key(), int_value())},
        % eqc:equals(bst:size(delete(eval(eval(K)), eval(eval(T)))),
        %                case bst:size(eval(eval(T))) =:= bst:size(eval(eval(empty()))) of
        %                    true ->  0;
        %                    false -> bst:size(eval(eval(T)))-1
        %                end)).
            eqc:equals(bst:size(eval(eval(T))) - 1, bst:size(delete(eval(eval(K)), eval(eval(T)))))).

obs_equals(T1, T2) ->
     eqc:equals(to_sorted_list(eval(eval(T1))), to_sorted_list(eval(eval(T2)))).

prop_insert_insert() ->
    ?FORALL({K1, K2, V1, V2, T},
            {atom_key(), atom_key(), int_value(), int_value(),
             bst(atom_key(), int_value())},
            obs_equals(insert(eval(eval(K1)), eval(eval(V1)), insert(eval(eval(K2)), eval(eval(V2)), eval(eval(T)))),
                       case eval(eval(K1)) =:= eval(eval(K2)) of
                           true ->  insert(eval(eval(K1)), eval(eval(V1)), eval(eval(T)));
                           false -> insert(eval(eval(K2)), eval(eval(V2)), insert(eval(eval(K1)), eval(eval(V1)), eval(eval(T))))
                       end)).



%%% -- Model based properties
%model({found, _}) -> [];
model(T) -> to_sorted_list(T).

prop_insert_model() ->
    ?FORALL({K, V, T}, {atom_key(), int_value(), bst(atom_key(), int_value())},
            equals(model(insert(eval(eval(K)), eval(eval(V)), eval(eval(T)))),
                   sorted_insert(eval(eval(K)), eval(eval(V)), delete_key(eval(eval(K)), model(eval(eval(T))))))).

%should use model(find...)
prop_find_model() -> 
    ?FORALL({K, T}, {atom_key(), bst(atom_key(), int_value())},
        equals(find(eval(eval(K)), eval(eval(T))),
        sorted_find(eval(eval(K)), model(eval(eval(T)))))).

prop_empty_model() -> 
        eqc:equals(model(empty()), model(sorted_empty())).

prop_delete_model() -> 
    ?FORALL({K, T}, {atom_key(), bst(atom_key(), int_value())},
        equals(model(delete(eval(eval(K)), eval(eval(T)))),
        sorted_delete(eval(eval(K)), model(eval(eval(T)))))).

% prop_union_model() -> 
%     ?FORALL({T2, T1}, {bst(atom_key(), int_value()), bst(atom_key(), int_value())},
%         equals(model(union(eval(eval(T1)), eval(eval(T2)))),
%         sorted_union(model(eval(eval(T1))), model(eval(eval(T2)))))).



-spec delete_key(Key, [{Key, Value}]) -> [{Key, Value}].
delete_key(Key, KVS) -> [ {K, V} || {K, V} <- KVS, K =/= Key ].

-spec sorted_insert(Key, Value, [{Key, Value}]) -> nonempty_list({Key, Value}).
sorted_insert(Key, Value, [{K, V} | Rest]) when K < Key ->
    [{K, V} | sorted_insert(Key, Value, Rest)];
sorted_insert(Key, Value, KVS) -> [{Key, Value} | KVS].

sorted_find(_, []) -> nothing;
sorted_find(Key, [X|Xs]) ->
    case X of
        {Key, Value} -> {found, Value};
        _ -> sorted_find(Key, Xs)
    end.

sorted_empty() -> leaf. %[].

sorted_delete(Key, L) ->
    [{K, V} || {K, V} <- L, K =/= Key].

sorted_union(T1, []) -> T1;
sorted_union(T1, [{Key, Value}|Xs]) -> sorted_union(sorted_insert(Key, Value, sorted_delete(Key, T1)), Xs).




%% -- Test all properties in the module: eqc:module(test_bst)
