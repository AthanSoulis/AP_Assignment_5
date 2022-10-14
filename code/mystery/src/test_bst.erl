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

%%% fully symbolic generator for bst
bst(Key, Value) ->
    ?LAZY(eqc_gen:frequency([
        {1,{call,bst,empty,[]}},
        {4,?LETSHRINK([D], [bst(Key, Value)], {call,bst,insert,[atom_key(),int_value(), D]})}
    ])).



% checking the quality of our generators
prop_measure() ->
    ?FORALL({T}, {bst(atom_key(), int_value())},
        eqc:collect(bst:size(eval(T)), true)).

prop_aggregate() ->
    ?FORALL({T}, {bst(atom_key(), int_value())},
        eqc:aggregate(eqc_symbolic:call_names(T), true)).



%%% invariant properties

% all generated bst are valid
prop_arbitrary_valid() ->
    ?FORALL(T, bst(atom_key(), int_value()),
            valid(eval(T))).

prop_empty_valid() ->
    valid(empty()).

% operations on valid trees should produce valid trees
prop_insert_valid() ->
    ?FORALL({K, V, T}, {atom_key(), int_value(), bst(atom_key(), int_value())},
            valid (insert(eval(K), eval(V), eval(T)))).

prop_delete_valid() ->
    ?FORALL({K, T}, {atom_key(), bst(atom_key(), int_value())},
            valid (delete(eval(K), eval(T)))).

prop_union_valid() ->
    ?FORALL({T1, T2}, {bst(atom_key(), int_value()), bst(atom_key(), int_value())},
        valid(union (eval(T1), eval(T2)))).



%%% -- postcondition properties

% For two given keys they are either equal and you find the value one of them has inserted or they are different
% and you output the result of a search (which will be nothing) 
prop_insert_post() ->
    ?FORALL({K1, K2, V, T},
            {atom_key(), atom_key(), int_value(), bst(atom_key(), int_value())},
            eqc:equals(find(eval(K2), insert(eval(K1), eval(V), eval(T))),
                       case eval(K1) =:= eval(K2) of
                           true ->  {found, eval(V)};
                           false -> find(eval(K2), eval(T))
                       end)).

prop_delete_post() ->
    ?FORALL({K1, K2, T},
            {atom_key(), atom_key(), bst(atom_key(), int_value())},
            eqc:equals(find(eval(K2), delete(eval(K1), eval(T))),
                       case eval(K1) =:= eval(K2) of
                           true -> nothing;
                           false -> find(eval(K2), eval(T))
                       end)).


% Find the value of a key that was just inserted
prop_find_post_present() ->
  % ∀ k v t. find k (insert k v t) === {found, v}
    ?FORALL({K, V, T}, {atom_key(), int_value(), bst(atom_key(), int_value())},
            eqc:equals(find(eval(K), insert(eval(K), eval(V), eval(T))),
                       {found, eval(V)})).

% When you search for a key after you have deleted it, it should result nothing
prop_find_post_absent() ->
    % ∀ k t. find k (delete k t) === nothing
    ?FORALL({K, T},
            {atom_key(), bst(atom_key(), int_value())},
            eqc:equals(find(eval(K), delete(eval(K), eval(T))), nothing)).

% unionized tree should contain all and only all unique elements from both trees
prop_union_post() -> 
    ?FORALL({T1, T2}, {bst(atom_key(), int_value()), bst(atom_key(), int_value())},
        begin
            L1 = to_sorted_list(eval(T1)),
            L2 = to_sorted_list(eval(T2)),
            T3 = union(eval(T1), eval(T2)),
            L3 = to_sorted_list(T3),
            %not sure if this is allowed since this is kinda mixing model based testing into it
            %but it's considerably easier to do than writing it "properly"
            equals(L3, sorted_union(L2, L1))
        end).



%%% -- metamorphic properties

%% the size is larger after an insert
prop_size_insert_soft() ->
    % ∀ k v t. size (insert k v t) >= size t
    ?FORALL({K, V, T}, {atom_key(), int_value(), bst(atom_key(), int_value())},
            bst:size(insert(eval(K), eval(V), eval(T))) >= bst:size(eval(T))).

% exact size calculation, stronger than above property
prop_size_insert_strong() -> 
    ?FORALL({K,V, T}, {atom_key(), int_value(), bst(atom_key(), int_value())},
        case find(eval(K), eval(T)) of 
            nothing -> bst:size(insert(eval(K), eval(V), eval(T))) == bst:size(eval(T)) + 1;
            _ -> eqc:equals(bst:size(insert(eval(K), eval(V), eval(T))), bst:size(eval(T)))
        end).

% size of an empty bst is zero
prop_size_empty() ->
    eqc:equals(bst:size(eval(empty())), 0).

% size of a bst after a deletion is smaller or equal (no key found) than before
prop_size_delete_soft() ->
    ?FORALL({K, T}, {atom_key(), bst(atom_key(), int_value())},
        bst:size(delete(eval(K), eval(T))) =< bst:size(eval(T))).

% exact size calculation, stronger than above property
prop_size_delete_strong() ->
    ?FORALL({K, T}, {atom_key(), bst(atom_key(), int_value())},
                case find(eval(K), eval(T)) of 
                    nothing -> bst:size(delete(eval(K), eval(T))) == bst:size(eval(T));
                    _ -> eqc:equals(bst:size(delete(eval(K), eval(T))), bst:size(eval(T))-1)
                end).

% size of a bst after a union is smaller (common entries) or equal than the sum of the sizes of both bsts
prop_size_union_soft() ->
    ?FORALL({T1, T2}, {bst(atom_key(), int_value()), bst(atom_key(), int_value())},
        bst:size(union(eval(T1), eval(T2))) =< bst:size(eval(T1)) + bst:size(eval(T2))
    ).

% exact size calculation, stronger than above property
prop_size_union_strong() ->
    ?FORALL({T1, T2}, {bst(atom_key(), int_value()), bst(atom_key(), int_value())},
        begin
            L1 = keys(eval(T1)),
            L2 = keys(eval(T2)),
            Common = [ X || X <- L1, lists:member(X, L2) ],
            T3 = union(eval(T1), eval(T2)),
            equals( bst:size(eval(T3)), bst:size(eval(T1)) + bst:size(eval(T2)) - length(Common))
        end).

obs_equals(T1, T2) ->
     eqc:equals(to_sorted_list(eval(T1)), to_sorted_list(eval(T2))).

% assert that inserting a {key, value} will either update or add to the bst
prop_insert_insert() ->
    ?FORALL({K1, K2, V1, V2, T},
            {atom_key(), atom_key(), int_value(), int_value(),
             bst(atom_key(), int_value())},
            obs_equals(insert(eval(K1), eval(V1), insert(eval(K2), eval(V2), eval(T))),
                       case eval(K1) =:= eval(K2) of
                           true ->  insert(eval(K1), eval(V1), eval(T));
                           false -> insert(eval(K2), eval(V2), insert(eval(K1), eval(V1), eval(T)))
                       end)).

% assert that after deleting a key from the bst we either cannot delete it again if we try, or a new key is deleted
prop_delete_delete() ->
    ?FORALL({K1, K2, T},
            {atom_key(), atom_key(), bst(atom_key(), int_value())},
            obs_equals(delete(eval(K1), delete(eval(K2), eval(T))),
                       case eval(K1) =:= eval(K2) of
                           true ->  delete(eval(K1), eval(T));
                           false -> delete(eval(K2), delete(eval(K1), eval(T)))
                       end)).



%%% -- Model based properties

% while model based testing generally produces strong properties
% we had to write the model ourselves, too. thus, mistakes in the
% model could fail to reveal bugs in the implementations.
model(T) -> to_sorted_list(T).

prop_insert_model() ->
    ?FORALL({K, V, T}, {atom_key(), int_value(), bst(atom_key(), int_value())},
            equals(model(insert(eval(K), eval(V), eval(T))),
                   sorted_insert(eval(K), eval(V), delete_key(eval(K), model(eval(T)))))).

%should perhaps use model(find...)
prop_find_model() -> 
    ?FORALL({K, T}, {atom_key(), bst(atom_key(), int_value())},
        equals(find(eval(K), eval(T)),
        sorted_find(eval(K), model(eval(T))))).

prop_empty_model() -> 
        equals(model(empty()), 
        sorted_empty()).

prop_delete_model() -> 
    ?FORALL({K, T}, {atom_key(), bst(atom_key(), int_value())},
        equals(model(delete(eval(K), eval(T))),
        sorted_delete(eval(K), model(eval(T))))).

prop_union_model() -> 
    ?FORALL({T1, T2}, {bst(atom_key(), int_value()), bst(atom_key(), int_value())},
        equals(model(union(eval(T2), eval(T1))),
        sorted_union(model(eval(T1)), model(eval(T2))))).



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

sorted_empty() -> [].

sorted_delete(Key, L) ->
    [{K, V} || {K, V} <- L, K =/= Key].

sorted_union(T1, []) -> T1;
sorted_union(T1, [{Key, Value}|Xs]) -> sorted_union(sorted_insert(Key, Value, sorted_delete(Key, T1)), Xs).




%% -- Test all properties in the module: eqc:module(test_bst)
