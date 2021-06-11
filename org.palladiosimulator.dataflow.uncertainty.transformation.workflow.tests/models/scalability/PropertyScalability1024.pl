:-discontiguous(actor/1).
:-discontiguous(characteristic/6).
:-discontiguous(characteristic/7).
:-discontiguous(characteristicType/1).
:-discontiguous(characteristicTypeTrust/3).
:-discontiguous(characteristicTypeValue/3).
:-discontiguous(dataflow/5).
:-discontiguous(findAllInputPins/2).
:-discontiguous(findAllInputPins/3).
:-discontiguous(flowTree/3).
:-discontiguous(flowTree/4).
:-discontiguous(flowTreeForFlows/4).
:-discontiguous(inputFlow/5).
:-discontiguous(inputFlowSelection/3).
:-discontiguous(inputFlowsSelection/2).
:-discontiguous(inputPin/2).
:-discontiguous(inputPinsFlowSelection/2).
:-discontiguous(involvesNode/2).
:-discontiguous(nodeCharacteristic/4).
:-discontiguous(nomatch/6).
:-discontiguous(outputPin/2).
:-discontiguous(process/1).
:-discontiguous(setof_characteristic_trust/6).
:-discontiguous(setof_characteristics/6).
:-discontiguous(setof_characteristics_with_trust/6).
:-discontiguous(store/1).
:-discontiguous(traversedNode/2).

% ============================
% HELPER: input flow selection
% ============================
% Select the input flow (FLOW) for the pin (PIN) of node (P) from a set of available flows (AVAILABLE_FLOWS) but do not pick a flow listed in already visited flows (VISITED).
% Assumption: the set contains exactly one flow for the pin
inputFlow(P, PIN, AVAILABLE_FLOWS, FLOW, VISITED) :-
	inputPin(P, PIN),
	inputFlowsSelection(P, AVAILABLE_FLOWS),
	inputFlowSelection(PIN, AVAILABLE_FLOWS, FLOW),
	intersection(VISITED, [FLOW], []).

% ===========================
% HELPER: find all input pins
% ===========================
% Finds all input pins PINS for a given node N. The list of pins is sorted.
% The sorted list containing all possible pins is the only result of the clause. No subsets or unsorted lists are returned.
findAllInputPins(N, PINS) :-
	findAllInputPins(N, [], PINS),
	sort(PINS, PINS).
findAllInputPins(N, PINS, RESULT) :-
	inputPin(N, PIN),
	intersection(PINS, [PIN], []),
	findAllInputPins(N, [PIN | PINS], RESULT).
findAllInputPins(N, PINS, PINS) :-
	\+ (
		inputPin(N, PIN),
		intersection(PINS, [PIN], [])
	).

% Find one arbitrary set of flows (SELECTED_FLOWS) for a given node (P) in a way that for every input pin, there is exactly one input flow.
% Using this rule in conjunction with findall would yield all possible combinations of input flows that meet the described condition.
% This rule is non-deterministic because inputPinsFlowSelection/3 is non-deterministic.
inputFlowsSelection(P, SELECTED_FLOWS) :-
	findAllInputPins(P, INPUT_PINS),
	inputPinsFlowSelection(INPUT_PINS, SELECTED_FLOWS).

% Find one arbitrary set of flows for a given set of input pins in a way that for every input pin, there is exactly one input flow.
% This rule is non-deterministic because it succeeds many times if there are multiple possible combinations that meet the described condition.
inputPinsFlowSelection([], []).
inputPinsFlowSelection([PIN | T], [FLOW_TO_PIN | RECURSE_FLOWS]) :-
	dataflow(FLOW_TO_PIN, _, _, _, PIN),
	inputPinsFlowSelection(T, RECURSE_FLOWS).

% Select the input flow (FLOW) for the pin (PIN) from a set of available flows. Here: list head matches.
inputFlowSelection(PIN, [FLOW | _], FLOW) :-
	dataflow(FLOW, _, _, _, PIN),
	!.

% Select the input flow (FLOW) for the pin (PIN) from a set of available flows. Here: use an entry of list tail.
inputFlowSelection(PIN, [H | T], FLOW) :-
	dataflow(H, _, _, _, PIN2),
	PIN \= PIN2,
	inputFlowSelection(PIN, T, FLOW).

% ==============================
% HELPER: create valid flow tree
% ==============================
flowTree(N, PIN, S) :-
	flowTree(N, PIN, S, []).
flowTree(N, PIN, [], _) :-
	actor(N),
	outputPin(N, PIN),
	!.
flowTree(N, PIN, S, VISITED) :-
	inputPin(N, PIN),
	dataflow(F, NSRC, PINSRC, N, PIN),
	flowTree(NSRC, PINSRC, TMP, [F | VISITED]),
	S = [F | TMP].
flowTree(N, PIN, S, VISITED) :-
	outputPin(N, PIN),
	(
		process(N);
		store(N)
	),
	inputFlowsSelection(N, FLOWS),
	flowTreeForFlows(N, S, FLOWS, VISITED).
flowTreeForFlows(_, [], [], _).
flowTreeForFlows(N, S, [F | T], VISITED) :-
	intersection([F], VISITED, []),
	flowTreeForFlows(N, STAIL, T, VISITED),
	dataflow(F, NSRC, PINSRC, _, _),
	flowTree(NSRC, PINSRC, TMP, [F | VISITED]),
	SHEAD = [F | TMP],
	S = [SHEAD | STAIL].

% ===========================================
% HELPER: find traversed nodes from flow tree
% ===========================================
traversedNode(S, N) :-
	flatten(S, SFLAT),
	list_to_set(SFLAT, FLOWS),
	involvesNode(FLOWS, N),
	!.
involvesNode([F | _], N) :-
	dataflow(F, N, _, _, _),
	!.
involvesNode([F | _], N) :-
	dataflow(F, _, _, N, _),
	!.
involvesNode([_ | T], N) :-
	involvesNode(T, N).

% ======================================
% HELPER: Shortcuts for common use cases
% ======================================
% Shortcut for characteristic queries
characteristic(N, PIN, CT, V, T, S) :-
	characteristic(N, PIN, CT, V, T, S, []).

% ==================================================
% HELPER: collect all available data characteristics
% ==================================================
setof_characteristics(N, PIN, CT, RESULT, T, S) :-
	flowTree(N, PIN, S),
	setof(V, characteristic(N, PIN, CT, V, T, S), RESULT).

% ===================================================================================
% HELPER: collect all available data characteristics that have a specific trust value
% ===================================================================================
setof_characteristics_with_trust(N, PIN, CT, RESULT, T, S) :-
	flowTree(N, PIN, S),
	setof(V, characteristic(N, PIN, CT, V, T, S), RESULT).

% ===================================================================================
% HELPER: collect all available trust values for a specific data characteristic value
% ===================================================================================
setof_characteristic_trust(N, PIN, CT, V, RESULT, S) :-
	flowTree(N, PIN, S),
	setof(T, characteristic(N, PIN, CT, V, T, S), RESULT).

% ============================================================================================
% HELPER: collects all characteristic trusts and compares if there is no match in trust values
% ============================================================================================
nomatch(P, PIN, NODECHARTYPE, DATACHARTYPE, S, V) :-
	setof(T1, nodeCharacteristic(P, NODECHARTYPE, V, T1), NODETRUST),
	setof_characteristic_trust(P, PIN, DATACHARTYPE, V, DATATRUST, S),
	intersection(NODETRUST, DATATRUST, []).

% ==================================
% HELPER: find input characteristics
% ==================================
characteristic(N, PIN, CT, V, T, [F | S], VISITED) :-
	inputPin(N, PIN),
	dataflow(F, NSRC, PINSRC, N, PIN),
	intersection([F], VISITED, []),
	characteristic(NSRC, PINSRC, CT, V, T, S, [F | VISITED]).

% ====================
% Characteristic types
% ====================
characteristicType('Location (_o7_1k9VeEeqRbpVUMz5XAQ)').
characteristicTypeValue('Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location0 (_cW03wMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location0 (_cW03wMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location0 (_cW03wMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location0 (_cW03wMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location0 (_cW03wMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location0 (_cW03wMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location0 (_cW03wMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1 (_cW3UAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1 (_cW3UAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1 (_cW3UAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1 (_cW3UAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1 (_cW3UAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1 (_cW3UAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1 (_cW3UAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location10 (_cW37IsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location10 (_cW37IsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location10 (_cW37IsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location10 (_cW37IsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location10 (_cW37IsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location10 (_cW37IsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location10 (_cW37IsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location100 (_cXeYAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location100 (_cXeYAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location100 (_cXeYAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location100 (_cXeYAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location100 (_cXeYAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location100 (_cXeYAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location100 (_cXeYAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1000 (_c_pLQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1000 (_c_pLQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1000 (_c_pLQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1000 (_c_pLQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1000 (_c_pLQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1000 (_c_pLQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1000 (_c_pLQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1001 (_c_uq0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1001 (_c_uq0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1001 (_c_uq0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1001 (_c_uq0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1001 (_c_uq0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1001 (_c_uq0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1001 (_c_uq0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1002 (_c_y8QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1002 (_c_y8QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1002 (_c_y8QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1002 (_c_y8QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1002 (_c_y8QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1002 (_c_y8QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1002 (_c_y8QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1003 (_c_30wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1003 (_c_30wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1003 (_c_30wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1003 (_c_30wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1003 (_c_30wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1003 (_c_30wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1003 (_c_30wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1004 (_c_8tQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1004 (_c_8tQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1004 (_c_8tQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1004 (_c_8tQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1004 (_c_8tQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1004 (_c_8tQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1004 (_c_8tQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1005 (_dABlwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1005 (_dABlwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1005 (_dABlwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1005 (_dABlwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1005 (_dABlwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1005 (_dABlwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1005 (_dABlwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1006 (_dAGeQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1006 (_dAGeQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1006 (_dAGeQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1006 (_dAGeQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1006 (_dAGeQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1006 (_dAGeQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1006 (_dAGeQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1007 (_dAL90crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1007 (_dAL90crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1007 (_dAL90crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1007 (_dAL90crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1007 (_dAL90crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1007 (_dAL90crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1007 (_dAL90crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1008 (_dAQPQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1008 (_dAQPQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1008 (_dAQPQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1008 (_dAQPQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1008 (_dAQPQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1008 (_dAQPQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1008 (_dAQPQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1009 (_dAVHwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1009 (_dAVHwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1009 (_dAVHwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1009 (_dAVHwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1009 (_dAVHwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1009 (_dAVHwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1009 (_dAVHwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location101 (_cXe_EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location101 (_cXe_EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location101 (_cXe_EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location101 (_cXe_EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location101 (_cXe_EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location101 (_cXe_EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location101 (_cXe_EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1010 (_dAaAQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1010 (_dAaAQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1010 (_dAaAQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1010 (_dAaAQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1010 (_dAaAQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1010 (_dAaAQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1010 (_dAaAQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1011 (_dAe4wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1011 (_dAe4wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1011 (_dAe4wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1011 (_dAe4wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1011 (_dAe4wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1011 (_dAe4wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1011 (_dAe4wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1012 (_dAjxQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1012 (_dAjxQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1012 (_dAjxQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1012 (_dAjxQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1012 (_dAjxQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1012 (_dAjxQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1012 (_dAjxQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1013 (_dApQ0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1013 (_dApQ0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1013 (_dApQ0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1013 (_dApQ0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1013 (_dApQ0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1013 (_dApQ0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1013 (_dApQ0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1014 (_dAvXccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1014 (_dAvXccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1014 (_dAvXccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1014 (_dAvXccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1014 (_dAvXccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1014 (_dAvXccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1014 (_dAvXccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1015 (_dA0P8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1015 (_dA0P8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1015 (_dA0P8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1015 (_dA0P8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1015 (_dA0P8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1015 (_dA0P8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1015 (_dA0P8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1016 (_dA5IccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1016 (_dA5IccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1016 (_dA5IccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1016 (_dA5IccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1016 (_dA5IccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1016 (_dA5IccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1016 (_dA5IccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1017 (_dA-oAMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1017 (_dA-oAMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1017 (_dA-oAMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1017 (_dA-oAMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1017 (_dA-oAMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1017 (_dA-oAMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1017 (_dA-oAMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1018 (_dBC5ccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1018 (_dBC5ccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1018 (_dBC5ccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1018 (_dBC5ccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1018 (_dBC5ccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1018 (_dBC5ccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1018 (_dBC5ccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1019 (_dBIZAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1019 (_dBIZAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1019 (_dBIZAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1019 (_dBIZAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1019 (_dBIZAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1019 (_dBIZAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1019 (_dBIZAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location102 (_cXe_FcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location102 (_cXe_FcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location102 (_cXe_FcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location102 (_cXe_FcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location102 (_cXe_FcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location102 (_cXe_FcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location102 (_cXe_FcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1020 (_dBNRgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1020 (_dBNRgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1020 (_dBNRgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1020 (_dBNRgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1020 (_dBNRgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1020 (_dBNRgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1020 (_dBNRgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1021 (_dBSKAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1021 (_dBSKAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1021 (_dBSKAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1021 (_dBSKAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1021 (_dBSKAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1021 (_dBSKAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1021 (_dBSKAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1022 (_dBXCgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1022 (_dBXCgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1022 (_dBXCgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1022 (_dBXCgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1022 (_dBXCgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1022 (_dBXCgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1022 (_dBXCgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1023 (_dBb7AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1023 (_dBb7AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1023 (_dBb7AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1023 (_dBb7AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1023 (_dBb7AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1023 (_dBb7AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1023 (_dBb7AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location103 (_cXfmI8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location103 (_cXfmI8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location103 (_cXfmI8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location103 (_cXfmI8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location103 (_cXfmI8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location103 (_cXfmI8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location103 (_cXfmI8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location104 (_cXgNM8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location104 (_cXgNM8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location104 (_cXgNM8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location104 (_cXgNM8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location104 (_cXgNM8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location104 (_cXgNM8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location104 (_cXgNM8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location105 (_cXg0Q8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location105 (_cXg0Q8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location105 (_cXg0Q8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location105 (_cXg0Q8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location105 (_cXg0Q8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location105 (_cXg0Q8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location105 (_cXg0Q8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location106 (_cXhbU8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location106 (_cXhbU8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location106 (_cXhbU8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location106 (_cXhbU8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location106 (_cXhbU8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location106 (_cXhbU8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location106 (_cXhbU8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location107 (_cXiCY8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location107 (_cXiCY8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location107 (_cXiCY8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location107 (_cXiCY8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location107 (_cXiCY8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location107 (_cXiCY8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location107 (_cXiCY8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location108 (_cXipcsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location108 (_cXipcsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location108 (_cXipcsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location108 (_cXipcsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location108 (_cXipcsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location108 (_cXipcsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location108 (_cXipcsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location109 (_cXjQg8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location109 (_cXjQg8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location109 (_cXjQg8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location109 (_cXjQg8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location109 (_cXjQg8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location109 (_cXjQg8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location109 (_cXjQg8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location11 (_cW4iI8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location11 (_cW4iI8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location11 (_cW4iI8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location11 (_cW4iI8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location11 (_cW4iI8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location11 (_cW4iI8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location11 (_cW4iI8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location110 (_cXkeocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location110 (_cXkeocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location110 (_cXkeocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location110 (_cXkeocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location110 (_cXkeocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location110 (_cXkeocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location110 (_cXkeocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location111 (_cXlFscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location111 (_cXlFscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location111 (_cXlFscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location111 (_cXlFscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location111 (_cXlFscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location111 (_cXlFscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location111 (_cXlFscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location112 (_cXlswsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location112 (_cXlswsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location112 (_cXlswsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location112 (_cXlswsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location112 (_cXlswsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location112 (_cXlswsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location112 (_cXlswsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location113 (_cXm64crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location113 (_cXm64crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location113 (_cXm64crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location113 (_cXm64crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location113 (_cXm64crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location113 (_cXm64crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location113 (_cXm64crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location114 (_cXnh8srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location114 (_cXnh8srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location114 (_cXnh8srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location114 (_cXnh8srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location114 (_cXnh8srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location114 (_cXnh8srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location114 (_cXnh8srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location115 (_cXowEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location115 (_cXowEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location115 (_cXowEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location115 (_cXowEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location115 (_cXowEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location115 (_cXowEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location115 (_cXowEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location116 (_cXpXIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location116 (_cXpXIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location116 (_cXpXIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location116 (_cXpXIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location116 (_cXpXIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location116 (_cXpXIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location116 (_cXpXIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location117 (_cXqlQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location117 (_cXqlQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location117 (_cXqlQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location117 (_cXqlQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location117 (_cXqlQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location117 (_cXqlQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location117 (_cXqlQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location118 (_cXrMUsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location118 (_cXrMUsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location118 (_cXrMUsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location118 (_cXrMUsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location118 (_cXrMUsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location118 (_cXrMUsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location118 (_cXrMUsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location119 (_cXsaccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location119 (_cXsaccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location119 (_cXsaccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location119 (_cXsaccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location119 (_cXsaccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location119 (_cXsaccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location119 (_cXsaccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location12 (_cW4iJ8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location12 (_cW4iJ8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location12 (_cW4iJ8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location12 (_cW4iJ8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location12 (_cW4iJ8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location12 (_cW4iJ8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location12 (_cW4iJ8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location120 (_cXtBgsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location120 (_cXtBgsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location120 (_cXtBgsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location120 (_cXtBgsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location120 (_cXtBgsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location120 (_cXtBgsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location120 (_cXtBgsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location121 (_cXuPocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location121 (_cXuPocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location121 (_cXuPocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location121 (_cXuPocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location121 (_cXuPocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location121 (_cXuPocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location121 (_cXuPocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location122 (_cXu2ssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location122 (_cXu2ssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location122 (_cXu2ssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location122 (_cXu2ssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location122 (_cXu2ssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location122 (_cXu2ssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location122 (_cXu2ssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location123 (_cXvdw8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location123 (_cXvdw8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location123 (_cXvdw8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location123 (_cXvdw8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location123 (_cXvdw8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location123 (_cXvdw8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location123 (_cXvdw8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location124 (_cXwr4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location124 (_cXwr4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location124 (_cXwr4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location124 (_cXwr4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location124 (_cXwr4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location124 (_cXwr4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location124 (_cXwr4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location125 (_cXx6AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location125 (_cXx6AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location125 (_cXx6AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location125 (_cXx6AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location125 (_cXx6AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location125 (_cXx6AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location125 (_cXx6AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location126 (_cXyhEsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location126 (_cXyhEsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location126 (_cXyhEsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location126 (_cXyhEsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location126 (_cXyhEsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location126 (_cXyhEsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location126 (_cXyhEsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location127 (_cXzvMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location127 (_cXzvMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location127 (_cXzvMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location127 (_cXzvMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location127 (_cXzvMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location127 (_cXzvMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location127 (_cXzvMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location128 (_cX09UcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location128 (_cX09UcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location128 (_cX09UcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location128 (_cX09UcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location128 (_cX09UcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location128 (_cX09UcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location128 (_cX09UcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location129 (_cX1kYsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location129 (_cX1kYsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location129 (_cX1kYsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location129 (_cX1kYsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location129 (_cX1kYsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location129 (_cX1kYsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location129 (_cX1kYsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location13 (_cW4iK8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location13 (_cW4iK8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location13 (_cW4iK8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location13 (_cW4iK8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location13 (_cW4iK8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location13 (_cW4iK8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location13 (_cW4iK8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location130 (_cX2ygcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location130 (_cX2ygcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location130 (_cX2ygcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location130 (_cX2ygcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location130 (_cX2ygcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location130 (_cX2ygcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location130 (_cX2ygcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location131 (_cX3ZksrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location131 (_cX3ZksrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location131 (_cX3ZksrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location131 (_cX3ZksrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location131 (_cX3ZksrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location131 (_cX3ZksrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location131 (_cX3ZksrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location132 (_cX4Ao8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location132 (_cX4Ao8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location132 (_cX4Ao8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location132 (_cX4Ao8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location132 (_cX4Ao8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location132 (_cX4Ao8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location132 (_cX4Ao8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location133 (_cX5OwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location133 (_cX5OwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location133 (_cX5OwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location133 (_cX5OwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location133 (_cX5OwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location133 (_cX5OwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location133 (_cX5OwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location134 (_cX6c4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location134 (_cX6c4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location134 (_cX6c4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location134 (_cX6c4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location134 (_cX6c4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location134 (_cX6c4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location134 (_cX6c4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location135 (_cX7rAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location135 (_cX7rAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location135 (_cX7rAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location135 (_cX7rAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location135 (_cX7rAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location135 (_cX7rAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location135 (_cX7rAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location136 (_cX85IcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location136 (_cX85IcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location136 (_cX85IcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location136 (_cX85IcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location136 (_cX85IcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location136 (_cX85IcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location136 (_cX85IcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location137 (_cX-HQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location137 (_cX-HQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location137 (_cX-HQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location137 (_cX-HQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location137 (_cX-HQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location137 (_cX-HQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location137 (_cX-HQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location138 (_cX_VYMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location138 (_cX_VYMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location138 (_cX_VYMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location138 (_cX_VYMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location138 (_cX_VYMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location138 (_cX_VYMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location138 (_cX_VYMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location139 (_cYAjgMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location139 (_cYAjgMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location139 (_cYAjgMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location139 (_cYAjgMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location139 (_cYAjgMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location139 (_cYAjgMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location139 (_cYAjgMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location14 (_cW4iL8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location14 (_cW4iL8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location14 (_cW4iL8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location14 (_cW4iL8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location14 (_cW4iL8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location14 (_cW4iL8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location14 (_cW4iL8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location140 (_cYBxoMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location140 (_cYBxoMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location140 (_cYBxoMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location140 (_cYBxoMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location140 (_cYBxoMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location140 (_cYBxoMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location140 (_cYBxoMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location141 (_cYCYssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location141 (_cYCYssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location141 (_cYCYssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location141 (_cYCYssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location141 (_cYCYssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location141 (_cYCYssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location141 (_cYCYssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location142 (_cYDm0srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location142 (_cYDm0srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location142 (_cYDm0srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location142 (_cYDm0srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location142 (_cYDm0srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location142 (_cYDm0srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location142 (_cYDm0srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location143 (_cYFcAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location143 (_cYFcAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location143 (_cYFcAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location143 (_cYFcAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location143 (_cYFcAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location143 (_cYFcAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location143 (_cYFcAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location144 (_cYGqIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location144 (_cYGqIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location144 (_cYGqIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location144 (_cYGqIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location144 (_cYGqIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location144 (_cYGqIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location144 (_cYGqIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location145 (_cYH4QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location145 (_cYH4QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location145 (_cYH4QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location145 (_cYH4QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location145 (_cYH4QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location145 (_cYH4QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location145 (_cYH4QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location146 (_cYJGYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location146 (_cYJGYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location146 (_cYJGYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location146 (_cYJGYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location146 (_cYJGYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location146 (_cYJGYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location146 (_cYJGYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location147 (_cYKUgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location147 (_cYKUgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location147 (_cYKUgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location147 (_cYKUgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location147 (_cYKUgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location147 (_cYKUgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location147 (_cYKUgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location148 (_cYLiocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location148 (_cYLiocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location148 (_cYLiocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location148 (_cYLiocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location148 (_cYLiocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location148 (_cYLiocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location148 (_cYLiocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location149 (_cYMwwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location149 (_cYMwwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location149 (_cYMwwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location149 (_cYMwwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location149 (_cYMwwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location149 (_cYMwwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location149 (_cYMwwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location15 (_cW5JM8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location15 (_cW5JM8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location15 (_cW5JM8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location15 (_cW5JM8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location15 (_cW5JM8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location15 (_cW5JM8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location15 (_cW5JM8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location150 (_cYN-4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location150 (_cYN-4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location150 (_cYN-4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location150 (_cYN-4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location150 (_cYN-4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location150 (_cYN-4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location150 (_cYN-4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location151 (_cYPNAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location151 (_cYPNAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location151 (_cYPNAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location151 (_cYPNAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location151 (_cYPNAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location151 (_cYPNAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location151 (_cYPNAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location152 (_cYQbIsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location152 (_cYQbIsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location152 (_cYQbIsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location152 (_cYQbIsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location152 (_cYQbIsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location152 (_cYQbIsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location152 (_cYQbIsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location153 (_cYSQUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location153 (_cYSQUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location153 (_cYSQUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location153 (_cYSQUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location153 (_cYSQUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location153 (_cYSQUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location153 (_cYSQUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location154 (_cYTeccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location154 (_cYTeccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location154 (_cYTeccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location154 (_cYTeccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location154 (_cYTeccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location154 (_cYTeccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location154 (_cYTeccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location155 (_cYUskcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location155 (_cYUskcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location155 (_cYUskcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location155 (_cYUskcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location155 (_cYUskcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location155 (_cYUskcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location155 (_cYUskcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location156 (_cYV6ssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location156 (_cYV6ssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location156 (_cYV6ssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location156 (_cYV6ssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location156 (_cYV6ssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location156 (_cYV6ssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location156 (_cYV6ssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location157 (_cYXv4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location157 (_cYXv4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location157 (_cYXv4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location157 (_cYXv4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location157 (_cYXv4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location157 (_cYXv4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location157 (_cYXv4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location158 (_cYY-AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location158 (_cYY-AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location158 (_cYY-AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location158 (_cYY-AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location158 (_cYY-AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location158 (_cYY-AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location158 (_cYY-AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location159 (_cYazMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location159 (_cYazMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location159 (_cYazMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location159 (_cYazMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location159 (_cYazMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location159 (_cYazMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location159 (_cYazMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location16 (_cW5JN8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location16 (_cW5JN8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location16 (_cW5JN8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location16 (_cW5JN8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location16 (_cW5JN8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location16 (_cW5JN8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location16 (_cW5JN8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location160 (_cYcBUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location160 (_cYcBUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location160 (_cYcBUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location160 (_cYcBUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location160 (_cYcBUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location160 (_cYcBUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location160 (_cYcBUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location161 (_cYdPccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location161 (_cYdPccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location161 (_cYdPccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location161 (_cYdPccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location161 (_cYdPccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location161 (_cYdPccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location161 (_cYdPccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location162 (_cYfEocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location162 (_cYfEocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location162 (_cYfEocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location162 (_cYfEocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location162 (_cYfEocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location162 (_cYfEocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location162 (_cYfEocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location163 (_cYgSwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location163 (_cYgSwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location163 (_cYgSwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location163 (_cYgSwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location163 (_cYgSwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location163 (_cYgSwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location163 (_cYgSwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location164 (_cYiH8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location164 (_cYiH8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location164 (_cYiH8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location164 (_cYiH8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location164 (_cYiH8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location164 (_cYiH8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location164 (_cYiH8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location165 (_cYjWEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location165 (_cYjWEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location165 (_cYjWEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location165 (_cYjWEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location165 (_cYjWEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location165 (_cYjWEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location165 (_cYjWEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location166 (_cYkkMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location166 (_cYkkMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location166 (_cYkkMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location166 (_cYkkMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location166 (_cYkkMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location166 (_cYkkMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location166 (_cYkkMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location167 (_cYmZYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location167 (_cYmZYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location167 (_cYmZYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location167 (_cYmZYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location167 (_cYmZYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location167 (_cYmZYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location167 (_cYmZYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location168 (_cYnAcsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location168 (_cYnAcsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location168 (_cYnAcsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location168 (_cYnAcsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location168 (_cYnAcsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location168 (_cYnAcsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location168 (_cYnAcsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location169 (_cYoOkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location169 (_cYoOkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location169 (_cYoOkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location169 (_cYoOkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location169 (_cYoOkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location169 (_cYoOkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location169 (_cYoOkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location17 (_cW5JO8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location17 (_cW5JO8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location17 (_cW5JO8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location17 (_cW5JO8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location17 (_cW5JO8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location17 (_cW5JO8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location17 (_cW5JO8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location170 (_cYo1osrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location170 (_cYo1osrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location170 (_cYo1osrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location170 (_cYo1osrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location170 (_cYo1osrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location170 (_cYo1osrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location170 (_cYo1osrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location171 (_cYqDwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location171 (_cYqDwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location171 (_cYqDwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location171 (_cYqDwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location171 (_cYqDwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location171 (_cYqDwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location171 (_cYqDwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location172 (_cYqq0srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location172 (_cYqq0srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location172 (_cYqq0srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location172 (_cYqq0srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location172 (_cYqq0srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location172 (_cYqq0srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location172 (_cYqq0srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location173 (_cYr48crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location173 (_cYr48crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location173 (_cYr48crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location173 (_cYr48crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location173 (_cYr48crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location173 (_cYr48crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location173 (_cYr48crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location174 (_cYsgAsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location174 (_cYsgAsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location174 (_cYsgAsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location174 (_cYsgAsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location174 (_cYsgAsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location174 (_cYsgAsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location174 (_cYsgAsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location175 (_cYtuIsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location175 (_cYtuIsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location175 (_cYtuIsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location175 (_cYtuIsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location175 (_cYtuIsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location175 (_cYtuIsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location175 (_cYtuIsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location176 (_cYu8QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location176 (_cYu8QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location176 (_cYu8QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location176 (_cYu8QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location176 (_cYu8QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location176 (_cYu8QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location176 (_cYu8QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location177 (_cYvjUsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location177 (_cYvjUsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location177 (_cYvjUsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location177 (_cYvjUsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location177 (_cYvjUsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location177 (_cYvjUsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location177 (_cYvjUsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location178 (_cYwxccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location178 (_cYwxccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location178 (_cYwxccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location178 (_cYwxccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location178 (_cYwxccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location178 (_cYwxccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location178 (_cYwxccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location179 (_cYxYgsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location179 (_cYxYgsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location179 (_cYxYgsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location179 (_cYxYgsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location179 (_cYxYgsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location179 (_cYxYgsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location179 (_cYxYgsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location18 (_cW5wQsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location18 (_cW5wQsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location18 (_cW5wQsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location18 (_cW5wQsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location18 (_cW5wQsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location18 (_cW5wQsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location18 (_cW5wQsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location180 (_cYymocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location180 (_cYymocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location180 (_cYymocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location180 (_cYymocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location180 (_cYymocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location180 (_cYymocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location180 (_cYymocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location181 (_cYzNssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location181 (_cYzNssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location181 (_cYzNssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location181 (_cYzNssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location181 (_cYzNssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location181 (_cYzNssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location181 (_cYzNssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location182 (_cY0b0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location182 (_cY0b0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location182 (_cY0b0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location182 (_cY0b0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location182 (_cY0b0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location182 (_cY0b0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location182 (_cY0b0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location183 (_cY1C4srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location183 (_cY1C4srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location183 (_cY1C4srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location183 (_cY1C4srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location183 (_cY1C4srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location183 (_cY1C4srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location183 (_cY1C4srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location184 (_cY1p8srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location184 (_cY1p8srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location184 (_cY1p8srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location184 (_cY1p8srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location184 (_cY1p8srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location184 (_cY1p8srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location184 (_cY1p8srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location185 (_cY24EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location185 (_cY24EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location185 (_cY24EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location185 (_cY24EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location185 (_cY24EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location185 (_cY24EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location185 (_cY24EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location186 (_cY4GMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location186 (_cY4GMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location186 (_cY4GMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location186 (_cY4GMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location186 (_cY4GMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location186 (_cY4GMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location186 (_cY4GMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location187 (_cY57YcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location187 (_cY57YcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location187 (_cY57YcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location187 (_cY57YcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location187 (_cY57YcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location187 (_cY57YcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location187 (_cY57YcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location188 (_cY7wkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location188 (_cY7wkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location188 (_cY7wkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location188 (_cY7wkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location188 (_cY7wkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location188 (_cY7wkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location188 (_cY7wkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location189 (_cY8-scrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location189 (_cY8-scrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location189 (_cY8-scrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location189 (_cY8-scrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location189 (_cY8-scrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location189 (_cY8-scrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location189 (_cY8-scrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location19 (_cW5wRsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location19 (_cW5wRsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location19 (_cW5wRsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location19 (_cW5wRsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location19 (_cW5wRsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location19 (_cW5wRsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location19 (_cW5wRsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location190 (_cY-z4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location190 (_cY-z4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location190 (_cY-z4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location190 (_cY-z4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location190 (_cY-z4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location190 (_cY-z4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location190 (_cY-z4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location191 (_cZACAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location191 (_cZACAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location191 (_cZACAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location191 (_cZACAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location191 (_cZACAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location191 (_cZACAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location191 (_cZACAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location192 (_cZBQIsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location192 (_cZBQIsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location192 (_cZBQIsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location192 (_cZBQIsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location192 (_cZBQIsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location192 (_cZBQIsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location192 (_cZBQIsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location193 (_cZDFUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location193 (_cZDFUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location193 (_cZDFUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location193 (_cZDFUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location193 (_cZDFUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location193 (_cZDFUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location193 (_cZDFUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location194 (_cZE6gcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location194 (_cZE6gcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location194 (_cZE6gcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location194 (_cZE6gcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location194 (_cZE6gcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location194 (_cZE6gcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location194 (_cZE6gcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location195 (_cZGIocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location195 (_cZGIocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location195 (_cZGIocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location195 (_cZGIocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location195 (_cZGIocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location195 (_cZGIocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location195 (_cZGIocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location196 (_cZH90crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location196 (_cZH90crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location196 (_cZH90crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location196 (_cZH90crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location196 (_cZH90crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location196 (_cZH90crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location196 (_cZH90crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location197 (_cZIk4srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location197 (_cZIk4srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location197 (_cZIk4srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location197 (_cZIk4srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location197 (_cZIk4srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location197 (_cZIk4srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location197 (_cZIk4srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location198 (_cZJzAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location198 (_cZJzAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location198 (_cZJzAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location198 (_cZJzAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location198 (_cZJzAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location198 (_cZJzAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location198 (_cZJzAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location199 (_cZLBIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location199 (_cZLBIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location199 (_cZLBIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location199 (_cZLBIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location199 (_cZLBIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location199 (_cZLBIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location199 (_cZLBIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location2 (_cW3UBcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location2 (_cW3UBcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location2 (_cW3UBcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location2 (_cW3UBcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location2 (_cW3UBcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location2 (_cW3UBcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location2 (_cW3UBcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location20 (_cW5wSsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location20 (_cW5wSsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location20 (_cW5wSsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location20 (_cW5wSsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location20 (_cW5wSsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location20 (_cW5wSsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location20 (_cW5wSsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location200 (_cZMPQsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location200 (_cZMPQsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location200 (_cZMPQsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location200 (_cZMPQsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location200 (_cZMPQsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location200 (_cZMPQsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location200 (_cZMPQsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location201 (_cZNdYsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location201 (_cZNdYsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location201 (_cZNdYsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location201 (_cZNdYsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location201 (_cZNdYsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location201 (_cZNdYsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location201 (_cZNdYsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location202 (_cZPSkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location202 (_cZPSkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location202 (_cZPSkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location202 (_cZPSkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location202 (_cZPSkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location202 (_cZPSkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location202 (_cZPSkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location203 (_cZQgscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location203 (_cZQgscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location203 (_cZQgscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location203 (_cZQgscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location203 (_cZQgscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location203 (_cZQgscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location203 (_cZQgscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location204 (_cZRu0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location204 (_cZRu0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location204 (_cZRu0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location204 (_cZRu0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location204 (_cZRu0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location204 (_cZRu0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location204 (_cZRu0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location205 (_cZSV4srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location205 (_cZSV4srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location205 (_cZSV4srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location205 (_cZSV4srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location205 (_cZSV4srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location205 (_cZSV4srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location205 (_cZSV4srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location206 (_cZTkAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location206 (_cZTkAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location206 (_cZTkAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location206 (_cZTkAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location206 (_cZTkAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location206 (_cZTkAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location206 (_cZTkAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location207 (_cZVZMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location207 (_cZVZMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location207 (_cZVZMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location207 (_cZVZMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location207 (_cZVZMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location207 (_cZVZMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location207 (_cZVZMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location208 (_cZWnUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location208 (_cZWnUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location208 (_cZWnUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location208 (_cZWnUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location208 (_cZWnUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location208 (_cZWnUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location208 (_cZWnUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location209 (_cZX1ccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location209 (_cZX1ccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location209 (_cZX1ccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location209 (_cZX1ccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location209 (_cZX1ccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location209 (_cZX1ccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location209 (_cZX1ccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location21 (_cW6XUsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location21 (_cW6XUsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location21 (_cW6XUsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location21 (_cW6XUsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location21 (_cW6XUsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location21 (_cW6XUsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location21 (_cW6XUsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location210 (_cZZDkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location210 (_cZZDkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location210 (_cZZDkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location210 (_cZZDkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location210 (_cZZDkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location210 (_cZZDkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location210 (_cZZDkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location211 (_cZaRscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location211 (_cZaRscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location211 (_cZaRscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location211 (_cZaRscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location211 (_cZaRscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location211 (_cZaRscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location211 (_cZaRscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location212 (_cZbf0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location212 (_cZbf0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location212 (_cZbf0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location212 (_cZbf0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location212 (_cZbf0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location212 (_cZbf0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location212 (_cZbf0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location213 (_cZcG4srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location213 (_cZcG4srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location213 (_cZcG4srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location213 (_cZcG4srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location213 (_cZcG4srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location213 (_cZcG4srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location213 (_cZcG4srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location214 (_cZdVAsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location214 (_cZdVAsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location214 (_cZdVAsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location214 (_cZdVAsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location214 (_cZdVAsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location214 (_cZdVAsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location214 (_cZdVAsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location215 (_cZejIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location215 (_cZejIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location215 (_cZejIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location215 (_cZejIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location215 (_cZejIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location215 (_cZejIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location215 (_cZejIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location216 (_cZfxQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location216 (_cZfxQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location216 (_cZfxQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location216 (_cZfxQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location216 (_cZfxQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location216 (_cZfxQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location216 (_cZfxQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location217 (_cZg_YsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location217 (_cZg_YsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location217 (_cZg_YsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location217 (_cZg_YsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location217 (_cZg_YsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location217 (_cZg_YsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location217 (_cZg_YsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location218 (_cZi0kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location218 (_cZi0kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location218 (_cZi0kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location218 (_cZi0kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location218 (_cZi0kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location218 (_cZi0kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location218 (_cZi0kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location219 (_cZkCscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location219 (_cZkCscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location219 (_cZkCscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location219 (_cZkCscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location219 (_cZkCscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location219 (_cZkCscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location219 (_cZkCscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location22 (_cW6XVsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location22 (_cW6XVsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location22 (_cW6XVsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location22 (_cW6XVsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location22 (_cW6XVsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location22 (_cW6XVsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location22 (_cW6XVsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location220 (_cZlQ0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location220 (_cZlQ0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location220 (_cZlQ0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location220 (_cZlQ0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location220 (_cZlQ0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location220 (_cZlQ0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location220 (_cZlQ0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location221 (_cZme8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location221 (_cZme8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location221 (_cZme8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location221 (_cZme8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location221 (_cZme8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location221 (_cZme8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location221 (_cZme8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location222 (_cZntEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location222 (_cZntEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location222 (_cZntEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location222 (_cZntEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location222 (_cZntEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location222 (_cZntEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location222 (_cZntEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location223 (_cZo7McrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location223 (_cZo7McrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location223 (_cZo7McrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location223 (_cZo7McrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location223 (_cZo7McrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location223 (_cZo7McrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location223 (_cZo7McrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location224 (_cZqJUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location224 (_cZqJUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location224 (_cZqJUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location224 (_cZqJUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location224 (_cZqJUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location224 (_cZqJUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location224 (_cZqJUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location225 (_cZrXccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location225 (_cZrXccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location225 (_cZrXccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location225 (_cZrXccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location225 (_cZrXccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location225 (_cZrXccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location225 (_cZrXccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location226 (_cZtMocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location226 (_cZtMocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location226 (_cZtMocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location226 (_cZtMocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location226 (_cZtMocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location226 (_cZtMocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location226 (_cZtMocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location227 (_cZuawcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location227 (_cZuawcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location227 (_cZuawcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location227 (_cZuawcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location227 (_cZuawcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location227 (_cZuawcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location227 (_cZuawcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location228 (_cZvo4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location228 (_cZvo4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location228 (_cZvo4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location228 (_cZvo4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location228 (_cZvo4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location228 (_cZvo4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location228 (_cZvo4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location229 (_cZw3AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location229 (_cZw3AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location229 (_cZw3AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location229 (_cZw3AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location229 (_cZw3AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location229 (_cZw3AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location229 (_cZw3AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location23 (_cW6XWsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location23 (_cW6XWsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location23 (_cW6XWsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location23 (_cW6XWsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location23 (_cW6XWsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location23 (_cW6XWsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location23 (_cW6XWsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location230 (_cZyFIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location230 (_cZyFIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location230 (_cZyFIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location230 (_cZyFIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location230 (_cZyFIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location230 (_cZyFIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location230 (_cZyFIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location231 (_cZysMsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location231 (_cZysMsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location231 (_cZysMsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location231 (_cZysMsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location231 (_cZysMsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location231 (_cZysMsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location231 (_cZysMsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location232 (_cZ0hYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location232 (_cZ0hYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location232 (_cZ0hYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location232 (_cZ0hYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location232 (_cZ0hYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location232 (_cZ0hYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location232 (_cZ0hYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location233 (_cZ1vgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location233 (_cZ1vgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location233 (_cZ1vgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location233 (_cZ1vgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location233 (_cZ1vgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location233 (_cZ1vgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location233 (_cZ1vgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location234 (_cZ29ocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location234 (_cZ29ocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location234 (_cZ29ocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location234 (_cZ29ocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location234 (_cZ29ocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location234 (_cZ29ocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location234 (_cZ29ocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location235 (_cZ4LwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location235 (_cZ4LwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location235 (_cZ4LwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location235 (_cZ4LwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location235 (_cZ4LwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location235 (_cZ4LwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location235 (_cZ4LwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location236 (_cZ5Z4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location236 (_cZ5Z4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location236 (_cZ5Z4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location236 (_cZ5Z4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location236 (_cZ5Z4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location236 (_cZ5Z4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location236 (_cZ5Z4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location237 (_cZ6oAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location237 (_cZ6oAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location237 (_cZ6oAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location237 (_cZ6oAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location237 (_cZ6oAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location237 (_cZ6oAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location237 (_cZ6oAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location238 (_cZ72IcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location238 (_cZ72IcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location238 (_cZ72IcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location238 (_cZ72IcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location238 (_cZ72IcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location238 (_cZ72IcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location238 (_cZ72IcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location239 (_cZ9EQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location239 (_cZ9EQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location239 (_cZ9EQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location239 (_cZ9EQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location239 (_cZ9EQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location239 (_cZ9EQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location239 (_cZ9EQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location24 (_cW6-Y8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location24 (_cW6-Y8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location24 (_cW6-Y8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location24 (_cW6-Y8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location24 (_cW6-Y8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location24 (_cW6-Y8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location24 (_cW6-Y8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location240 (_cZ-SYsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location240 (_cZ-SYsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location240 (_cZ-SYsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location240 (_cZ-SYsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location240 (_cZ-SYsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location240 (_cZ-SYsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location240 (_cZ-SYsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location241 (_caAHkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location241 (_caAHkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location241 (_caAHkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location241 (_caAHkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location241 (_caAHkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location241 (_caAHkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location241 (_caAHkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location242 (_caBVscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location242 (_caBVscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location242 (_caBVscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location242 (_caBVscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location242 (_caBVscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location242 (_caBVscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location242 (_caBVscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location243 (_caCj0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location243 (_caCj0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location243 (_caCj0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location243 (_caCj0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location243 (_caCj0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location243 (_caCj0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location243 (_caCj0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location244 (_caDx8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location244 (_caDx8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location244 (_caDx8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location244 (_caDx8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location244 (_caDx8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location244 (_caDx8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location244 (_caDx8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location245 (_caFAEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location245 (_caFAEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location245 (_caFAEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location245 (_caFAEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location245 (_caFAEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location245 (_caFAEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location245 (_caFAEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location246 (_caGOMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location246 (_caGOMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location246 (_caGOMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location246 (_caGOMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location246 (_caGOMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location246 (_caGOMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location246 (_caGOMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location247 (_caHcUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location247 (_caHcUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location247 (_caHcUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location247 (_caHcUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location247 (_caHcUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location247 (_caHcUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location247 (_caHcUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location248 (_caIqccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location248 (_caIqccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location248 (_caIqccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location248 (_caIqccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location248 (_caIqccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location248 (_caIqccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location248 (_caIqccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location249 (_caKfocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location249 (_caKfocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location249 (_caKfocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location249 (_caKfocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location249 (_caKfocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location249 (_caKfocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location249 (_caKfocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location25 (_cW6-Z8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location25 (_cW6-Z8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location25 (_cW6-Z8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location25 (_cW6-Z8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location25 (_cW6-Z8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location25 (_cW6-Z8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location25 (_cW6-Z8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location250 (_caLtwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location250 (_caLtwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location250 (_caLtwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location250 (_caLtwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location250 (_caLtwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location250 (_caLtwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location250 (_caLtwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location251 (_caM74crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location251 (_caM74crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location251 (_caM74crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location251 (_caM74crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location251 (_caM74crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location251 (_caM74crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location251 (_caM74crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location252 (_caOKAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location252 (_caOKAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location252 (_caOKAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location252 (_caOKAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location252 (_caOKAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location252 (_caOKAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location252 (_caOKAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location253 (_caPYIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location253 (_caPYIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location253 (_caPYIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location253 (_caPYIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location253 (_caPYIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location253 (_caPYIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location253 (_caPYIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location254 (_caP_MsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location254 (_caP_MsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location254 (_caP_MsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location254 (_caP_MsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location254 (_caP_MsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location254 (_caP_MsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location254 (_caP_MsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location255 (_caRNUsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location255 (_caRNUsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location255 (_caRNUsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location255 (_caRNUsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location255 (_caRNUsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location255 (_caRNUsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location255 (_caRNUsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location256 (_caTCgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location256 (_caTCgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location256 (_caTCgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location256 (_caTCgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location256 (_caTCgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location256 (_caTCgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location256 (_caTCgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location257 (_caU3sMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location257 (_caU3sMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location257 (_caU3sMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location257 (_caU3sMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location257 (_caU3sMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location257 (_caU3sMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location257 (_caU3sMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location258 (_caWF0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location258 (_caWF0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location258 (_caWF0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location258 (_caWF0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location258 (_caWF0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location258 (_caWF0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location258 (_caWF0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location259 (_caXT8srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location259 (_caXT8srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location259 (_caXT8srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location259 (_caXT8srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location259 (_caXT8srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location259 (_caXT8srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location259 (_caXT8srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location26 (_cW7lc8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location26 (_cW7lc8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location26 (_cW7lc8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location26 (_cW7lc8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location26 (_cW7lc8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location26 (_cW7lc8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location26 (_cW7lc8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location260 (_caZJIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location260 (_caZJIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location260 (_caZJIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location260 (_caZJIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location260 (_caZJIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location260 (_caZJIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location260 (_caZJIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location261 (_caa-UcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location261 (_caa-UcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location261 (_caa-UcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location261 (_caa-UcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location261 (_caa-UcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location261 (_caa-UcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location261 (_caa-UcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location262 (_cacMccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location262 (_cacMccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location262 (_cacMccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location262 (_cacMccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location262 (_cacMccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location262 (_cacMccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location262 (_cacMccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location263 (_caeBocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location263 (_caeBocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location263 (_caeBocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location263 (_caeBocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location263 (_caeBocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location263 (_caeBocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location263 (_caeBocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location264 (_cagd4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location264 (_cagd4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location264 (_cagd4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location264 (_cagd4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location264 (_cagd4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location264 (_cagd4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location264 (_cagd4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location265 (_cahsAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location265 (_cahsAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location265 (_cahsAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location265 (_cahsAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location265 (_cahsAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location265 (_cahsAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location265 (_cahsAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location266 (_cai6IcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location266 (_cai6IcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location266 (_cai6IcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location266 (_cai6IcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location266 (_cai6IcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location266 (_cai6IcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location266 (_cai6IcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location267 (_cakvUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location267 (_cakvUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location267 (_cakvUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location267 (_cakvUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location267 (_cakvUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location267 (_cakvUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location267 (_cakvUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location268 (_cal9ccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location268 (_cal9ccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location268 (_cal9ccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location268 (_cal9ccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location268 (_cal9ccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location268 (_cal9ccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location268 (_cal9ccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location269 (_canyocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location269 (_canyocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location269 (_canyocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location269 (_canyocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location269 (_canyocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location269 (_canyocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location269 (_canyocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location27 (_cW7ld8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location27 (_cW7ld8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location27 (_cW7ld8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location27 (_cW7ld8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location27 (_cW7ld8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location27 (_cW7ld8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location27 (_cW7ld8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location270 (_capn0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location270 (_capn0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location270 (_capn0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location270 (_capn0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location270 (_capn0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location270 (_capn0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location270 (_capn0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location271 (_caq18crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location271 (_caq18crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location271 (_caq18crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location271 (_caq18crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location271 (_caq18crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location271 (_caq18crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location271 (_caq18crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location272 (_casEEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location272 (_casEEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location272 (_casEEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location272 (_casEEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location272 (_casEEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location272 (_casEEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location272 (_casEEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location273 (_catSMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location273 (_catSMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location273 (_catSMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location273 (_catSMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location273 (_catSMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location273 (_catSMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location273 (_catSMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location274 (_caugUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location274 (_caugUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location274 (_caugUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location274 (_caugUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location274 (_caugUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location274 (_caugUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location274 (_caugUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location275 (_cavuccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location275 (_cavuccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location275 (_cavuccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location275 (_cavuccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location275 (_cavuccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location275 (_cavuccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location275 (_cavuccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location276 (_caxjocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location276 (_caxjocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location276 (_caxjocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location276 (_caxjocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location276 (_caxjocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location276 (_caxjocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location276 (_caxjocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location277 (_cayxwsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location277 (_cayxwsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location277 (_cayxwsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location277 (_cayxwsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location277 (_cayxwsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location277 (_cayxwsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location277 (_cayxwsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location278 (_ca0m8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location278 (_ca0m8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location278 (_ca0m8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location278 (_ca0m8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location278 (_ca0m8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location278 (_ca0m8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location278 (_ca0m8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location279 (_ca11EsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location279 (_ca11EsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location279 (_ca11EsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location279 (_ca11EsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location279 (_ca11EsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location279 (_ca11EsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location279 (_ca11EsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location28 (_cW8MgsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location28 (_cW8MgsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location28 (_cW8MgsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location28 (_cW8MgsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location28 (_cW8MgsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location28 (_cW8MgsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location28 (_cW8MgsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location280 (_ca4RUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location280 (_ca4RUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location280 (_ca4RUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location280 (_ca4RUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location280 (_ca4RUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location280 (_ca4RUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location280 (_ca4RUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location281 (_ca6GgMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location281 (_ca6GgMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location281 (_ca6GgMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location281 (_ca6GgMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location281 (_ca6GgMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location281 (_ca6GgMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location281 (_ca6GgMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location282 (_ca7UocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location282 (_ca7UocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location282 (_ca7UocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location282 (_ca7UocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location282 (_ca7UocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location282 (_ca7UocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location282 (_ca7UocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location283 (_ca9J0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location283 (_ca9J0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location283 (_ca9J0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location283 (_ca9J0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location283 (_ca9J0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location283 (_ca9J0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location283 (_ca9J0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location284 (_ca-_AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location284 (_ca-_AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location284 (_ca-_AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location284 (_ca-_AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location284 (_ca-_AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location284 (_ca-_AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location284 (_ca-_AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location285 (_cbANIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location285 (_cbANIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location285 (_cbANIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location285 (_cbANIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location285 (_cbANIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location285 (_cbANIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location285 (_cbANIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location286 (_cbBbQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location286 (_cbBbQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location286 (_cbBbQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location286 (_cbBbQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location286 (_cbBbQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location286 (_cbBbQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location286 (_cbBbQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location287 (_cbCpYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location287 (_cbCpYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location287 (_cbCpYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location287 (_cbCpYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location287 (_cbCpYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location287 (_cbCpYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location287 (_cbCpYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location288 (_cbD3gcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location288 (_cbD3gcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location288 (_cbD3gcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location288 (_cbD3gcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location288 (_cbD3gcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location288 (_cbD3gcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location288 (_cbD3gcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location289 (_cbFsscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location289 (_cbFsscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location289 (_cbFsscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location289 (_cbFsscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location289 (_cbFsscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location289 (_cbFsscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location289 (_cbFsscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location29 (_cW8MhsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location29 (_cW8MhsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location29 (_cW8MhsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location29 (_cW8MhsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location29 (_cW8MhsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location29 (_cW8MhsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location29 (_cW8MhsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location290 (_cbHh4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location290 (_cbHh4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location290 (_cbHh4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location290 (_cbHh4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location290 (_cbHh4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location290 (_cbHh4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location290 (_cbHh4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location291 (_cbJXEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location291 (_cbJXEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location291 (_cbJXEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location291 (_cbJXEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location291 (_cbJXEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location291 (_cbJXEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location291 (_cbJXEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location292 (_cbKlMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location292 (_cbKlMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location292 (_cbKlMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location292 (_cbKlMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location292 (_cbKlMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location292 (_cbKlMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location292 (_cbKlMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location293 (_cbLzUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location293 (_cbLzUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location293 (_cbLzUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location293 (_cbLzUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location293 (_cbLzUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location293 (_cbLzUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location293 (_cbLzUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location294 (_cbNBccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location294 (_cbNBccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location294 (_cbNBccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location294 (_cbNBccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location294 (_cbNBccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location294 (_cbNBccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location294 (_cbNBccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location295 (_cbOPksrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location295 (_cbOPksrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location295 (_cbOPksrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location295 (_cbOPksrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location295 (_cbOPksrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location295 (_cbOPksrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location295 (_cbOPksrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location296 (_cbQr0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location296 (_cbQr0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location296 (_cbQr0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location296 (_cbQr0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location296 (_cbQr0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location296 (_cbQr0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location296 (_cbQr0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location297 (_cbShAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location297 (_cbShAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location297 (_cbShAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location297 (_cbShAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location297 (_cbShAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location297 (_cbShAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location297 (_cbShAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location298 (_cbUWMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location298 (_cbUWMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location298 (_cbUWMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location298 (_cbUWMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location298 (_cbUWMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location298 (_cbUWMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location298 (_cbUWMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location299 (_cbWLYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location299 (_cbWLYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location299 (_cbWLYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location299 (_cbWLYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location299 (_cbWLYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location299 (_cbWLYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location299 (_cbWLYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location3 (_cW3UCcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location3 (_cW3UCcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location3 (_cW3UCcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location3 (_cW3UCcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location3 (_cW3UCcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location3 (_cW3UCcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location3 (_cW3UCcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location30 (_cW8zksrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location30 (_cW8zksrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location30 (_cW8zksrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location30 (_cW8zksrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location30 (_cW8zksrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location30 (_cW8zksrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location30 (_cW8zksrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location300 (_cbYAkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location300 (_cbYAkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location300 (_cbYAkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location300 (_cbYAkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location300 (_cbYAkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location300 (_cbYAkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location300 (_cbYAkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location301 (_cbZOscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location301 (_cbZOscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location301 (_cbZOscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location301 (_cbZOscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location301 (_cbZOscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location301 (_cbZOscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location301 (_cbZOscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location302 (_cbbD4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location302 (_cbbD4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location302 (_cbbD4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location302 (_cbbD4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location302 (_cbbD4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location302 (_cbbD4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location302 (_cbbD4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location303 (_cbc5EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location303 (_cbc5EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location303 (_cbc5EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location303 (_cbc5EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location303 (_cbc5EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location303 (_cbc5EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location303 (_cbc5EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location304 (_cbeHMsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location304 (_cbeHMsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location304 (_cbeHMsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location304 (_cbeHMsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location304 (_cbeHMsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location304 (_cbeHMsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location304 (_cbeHMsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location305 (_cbf8YcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location305 (_cbf8YcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location305 (_cbf8YcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location305 (_cbf8YcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location305 (_cbf8YcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location305 (_cbf8YcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location305 (_cbf8YcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location306 (_cbhKgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location306 (_cbhKgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location306 (_cbhKgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location306 (_cbhKgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location306 (_cbhKgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location306 (_cbhKgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location306 (_cbhKgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location307 (_cbiYocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location307 (_cbiYocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location307 (_cbiYocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location307 (_cbiYocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location307 (_cbiYocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location307 (_cbiYocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location307 (_cbiYocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location308 (_cbkN0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location308 (_cbkN0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location308 (_cbkN0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location308 (_cbkN0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location308 (_cbkN0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location308 (_cbkN0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location308 (_cbkN0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location309 (_cbmDAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location309 (_cbmDAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location309 (_cbmDAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location309 (_cbmDAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location309 (_cbmDAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location309 (_cbmDAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location309 (_cbmDAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location31 (_cW8zlsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location31 (_cW8zlsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location31 (_cW8zlsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location31 (_cW8zlsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location31 (_cW8zlsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location31 (_cW8zlsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location31 (_cW8zlsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location310 (_cbn4McrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location310 (_cbn4McrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location310 (_cbn4McrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location310 (_cbn4McrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location310 (_cbn4McrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location310 (_cbn4McrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location310 (_cbn4McrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location311 (_cbpGUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location311 (_cbpGUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location311 (_cbpGUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location311 (_cbpGUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location311 (_cbpGUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location311 (_cbpGUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location311 (_cbpGUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location312 (_cbqUcsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location312 (_cbqUcsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location312 (_cbqUcsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location312 (_cbqUcsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location312 (_cbqUcsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location312 (_cbqUcsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location312 (_cbqUcsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location313 (_cbsJocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location313 (_cbsJocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location313 (_cbsJocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location313 (_cbsJocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location313 (_cbsJocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location313 (_cbsJocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location313 (_cbsJocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location314 (_cbtXwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location314 (_cbtXwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location314 (_cbtXwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location314 (_cbtXwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location314 (_cbtXwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location314 (_cbtXwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location314 (_cbtXwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location315 (_cbvM8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location315 (_cbvM8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location315 (_cbvM8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location315 (_cbvM8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location315 (_cbvM8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location315 (_cbvM8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location315 (_cbvM8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location316 (_cbxCIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location316 (_cbxCIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location316 (_cbxCIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location316 (_cbxCIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location316 (_cbxCIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location316 (_cbxCIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location316 (_cbxCIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location317 (_cby3UcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location317 (_cby3UcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location317 (_cby3UcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location317 (_cby3UcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location317 (_cby3UcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location317 (_cby3UcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location317 (_cby3UcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location318 (_cb0FccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location318 (_cb0FccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location318 (_cb0FccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location318 (_cb0FccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location318 (_cb0FccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location318 (_cb0FccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location318 (_cb0FccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location319 (_cb16ocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location319 (_cb16ocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location319 (_cb16ocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location319 (_cb16ocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location319 (_cb16ocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location319 (_cb16ocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location319 (_cb16ocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location32 (_cW9aosrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location32 (_cW9aosrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location32 (_cW9aosrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location32 (_cW9aosrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location32 (_cW9aosrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location32 (_cW9aosrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location32 (_cW9aosrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location320 (_cb3IwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location320 (_cb3IwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location320 (_cb3IwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location320 (_cb3IwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location320 (_cb3IwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location320 (_cb3IwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location320 (_cb3IwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location321 (_cb5lAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location321 (_cb5lAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location321 (_cb5lAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location321 (_cb5lAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location321 (_cb5lAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location321 (_cb5lAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location321 (_cb5lAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location322 (_cb7aMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location322 (_cb7aMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location322 (_cb7aMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location322 (_cb7aMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location322 (_cb7aMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location322 (_cb7aMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location322 (_cb7aMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location323 (_cb8oUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location323 (_cb8oUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location323 (_cb8oUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location323 (_cb8oUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location323 (_cb8oUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location323 (_cb8oUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location323 (_cb8oUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location324 (_cb-dgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location324 (_cb-dgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location324 (_cb-dgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location324 (_cb-dgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location324 (_cb-dgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location324 (_cb-dgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location324 (_cb-dgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location325 (_cb_rocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location325 (_cb_rocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location325 (_cb_rocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location325 (_cb_rocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location325 (_cb_rocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location325 (_cb_rocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location325 (_cb_rocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location326 (_ccA5wsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location326 (_ccA5wsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location326 (_ccA5wsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location326 (_ccA5wsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location326 (_ccA5wsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location326 (_ccA5wsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location326 (_ccA5wsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location327 (_ccDWAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location327 (_ccDWAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location327 (_ccDWAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location327 (_ccDWAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location327 (_ccDWAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location327 (_ccDWAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location327 (_ccDWAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location328 (_ccFLMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location328 (_ccFLMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location328 (_ccFLMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location328 (_ccFLMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location328 (_ccFLMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location328 (_ccFLMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location328 (_ccFLMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location329 (_ccHAYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location329 (_ccHAYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location329 (_ccHAYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location329 (_ccHAYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location329 (_ccHAYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location329 (_ccHAYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location329 (_ccHAYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location33 (_cW9apsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location33 (_cW9apsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location33 (_cW9apsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location33 (_cW9apsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location33 (_cW9apsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location33 (_cW9apsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location33 (_cW9apsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location330 (_ccIOgsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location330 (_ccIOgsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location330 (_ccIOgsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location330 (_ccIOgsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location330 (_ccIOgsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location330 (_ccIOgsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location330 (_ccIOgsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location331 (_ccKDscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location331 (_ccKDscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location331 (_ccKDscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location331 (_ccKDscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location331 (_ccKDscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location331 (_ccKDscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location331 (_ccKDscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location332 (_ccLR0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location332 (_ccLR0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location332 (_ccLR0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location332 (_ccLR0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location332 (_ccLR0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location332 (_ccLR0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location332 (_ccLR0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location333 (_ccNuEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location333 (_ccNuEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location333 (_ccNuEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location333 (_ccNuEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location333 (_ccNuEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location333 (_ccNuEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location333 (_ccNuEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location334 (_ccPjQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location334 (_ccPjQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location334 (_ccPjQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location334 (_ccPjQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location334 (_ccPjQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location334 (_ccPjQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location334 (_ccPjQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location335 (_ccQxYsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location335 (_ccQxYsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location335 (_ccQxYsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location335 (_ccQxYsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location335 (_ccQxYsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location335 (_ccQxYsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location335 (_ccQxYsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location336 (_ccSmkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location336 (_ccSmkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location336 (_ccSmkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location336 (_ccSmkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location336 (_ccSmkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location336 (_ccSmkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location336 (_ccSmkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location337 (_ccT0ssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location337 (_ccT0ssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location337 (_ccT0ssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location337 (_ccT0ssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location337 (_ccT0ssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location337 (_ccT0ssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location337 (_ccT0ssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location338 (_ccVp4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location338 (_ccVp4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location338 (_ccVp4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location338 (_ccVp4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location338 (_ccVp4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location338 (_ccVp4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location338 (_ccVp4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location339 (_ccYGIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location339 (_ccYGIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location339 (_ccYGIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location339 (_ccYGIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location339 (_ccYGIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location339 (_ccYGIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location339 (_ccYGIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location34 (_cW-Bs8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location34 (_cW-Bs8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location34 (_cW-Bs8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location34 (_cW-Bs8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location34 (_cW-Bs8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location34 (_cW-Bs8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location34 (_cW-Bs8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location340 (_ccaiYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location340 (_ccaiYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location340 (_ccaiYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location340 (_ccaiYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location340 (_ccaiYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location340 (_ccaiYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location340 (_ccaiYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location341 (_cccXkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location341 (_cccXkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location341 (_cccXkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location341 (_cccXkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location341 (_cccXkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location341 (_cccXkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location341 (_cccXkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location342 (_cceMwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location342 (_cceMwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location342 (_cceMwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location342 (_cceMwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location342 (_cceMwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location342 (_cceMwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location342 (_cceMwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location343 (_ccgB8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location343 (_ccgB8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location343 (_ccgB8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location343 (_ccgB8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location343 (_ccgB8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location343 (_ccgB8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location343 (_ccgB8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location344 (_ccieMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location344 (_ccieMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location344 (_ccieMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location344 (_ccieMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location344 (_ccieMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location344 (_ccieMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location344 (_ccieMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location345 (_cckTYsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location345 (_cckTYsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location345 (_cckTYsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location345 (_cckTYsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location345 (_cckTYsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location345 (_cckTYsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location345 (_cckTYsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location346 (_ccmIkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location346 (_ccmIkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location346 (_ccmIkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location346 (_ccmIkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location346 (_ccmIkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location346 (_ccmIkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location346 (_ccmIkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location347 (_ccn9wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location347 (_ccn9wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location347 (_ccn9wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location347 (_ccn9wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location347 (_ccn9wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location347 (_ccn9wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location347 (_ccn9wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location348 (_ccpy8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location348 (_ccpy8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location348 (_ccpy8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location348 (_ccpy8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location348 (_ccpy8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location348 (_ccpy8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location348 (_ccpy8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location349 (_ccroIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location349 (_ccroIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location349 (_ccroIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location349 (_ccroIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location349 (_ccroIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location349 (_ccroIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location349 (_ccroIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location35 (_cW-Bt8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location35 (_cW-Bt8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location35 (_cW-Bt8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location35 (_cW-Bt8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location35 (_cW-Bt8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location35 (_cW-Bt8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location35 (_cW-Bt8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location350 (_ccuEYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location350 (_ccuEYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location350 (_ccuEYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location350 (_ccuEYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location350 (_ccuEYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location350 (_ccuEYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location350 (_ccuEYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location351 (_ccvSgsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location351 (_ccvSgsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location351 (_ccvSgsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location351 (_ccvSgsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location351 (_ccvSgsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location351 (_ccvSgsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location351 (_ccvSgsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location352 (_ccxHscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location352 (_ccxHscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location352 (_ccxHscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location352 (_ccxHscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location352 (_ccxHscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location352 (_ccxHscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location352 (_ccxHscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location353 (_ccy84crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location353 (_ccy84crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location353 (_ccy84crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location353 (_ccy84crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location353 (_ccy84crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location353 (_ccy84crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location353 (_ccy84crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location354 (_cc0yEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location354 (_cc0yEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location354 (_cc0yEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location354 (_cc0yEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location354 (_cc0yEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location354 (_cc0yEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location354 (_cc0yEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location355 (_cc2nQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location355 (_cc2nQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location355 (_cc2nQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location355 (_cc2nQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location355 (_cc2nQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location355 (_cc2nQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location355 (_cc2nQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location356 (_cc4ccsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location356 (_cc4ccsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location356 (_cc4ccsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location356 (_cc4ccsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location356 (_cc4ccsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location356 (_cc4ccsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location356 (_cc4ccsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location357 (_cc6RocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location357 (_cc6RocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location357 (_cc6RocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location357 (_cc6RocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location357 (_cc6RocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location357 (_cc6RocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location357 (_cc6RocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location358 (_cc8G0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location358 (_cc8G0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location358 (_cc8G0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location358 (_cc8G0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location358 (_cc8G0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location358 (_cc8G0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location358 (_cc8G0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location359 (_cc98AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location359 (_cc98AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location359 (_cc98AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location359 (_cc98AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location359 (_cc98AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location359 (_cc98AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location359 (_cc98AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location36 (_cW-ow8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location36 (_cW-ow8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location36 (_cW-ow8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location36 (_cW-ow8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location36 (_cW-ow8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location36 (_cW-ow8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location36 (_cW-ow8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location360 (_cdAYQMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location360 (_cdAYQMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location360 (_cdAYQMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location360 (_cdAYQMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location360 (_cdAYQMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location360 (_cdAYQMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location360 (_cdAYQMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location361 (_cdCNccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location361 (_cdCNccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location361 (_cdCNccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location361 (_cdCNccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location361 (_cdCNccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location361 (_cdCNccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location361 (_cdCNccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location362 (_cdECocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location362 (_cdECocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location362 (_cdECocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location362 (_cdECocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location362 (_cdECocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location362 (_cdECocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location362 (_cdECocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location363 (_cdF30crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location363 (_cdF30crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location363 (_cdF30crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location363 (_cdF30crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location363 (_cdF30crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location363 (_cdF30crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location363 (_cdF30crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location364 (_cdHF8srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location364 (_cdHF8srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location364 (_cdHF8srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location364 (_cdHF8srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location364 (_cdHF8srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location364 (_cdHF8srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location364 (_cdHF8srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location365 (_cdJiMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location365 (_cdJiMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location365 (_cdJiMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location365 (_cdJiMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location365 (_cdJiMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location365 (_cdJiMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location365 (_cdJiMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location366 (_cdLXYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location366 (_cdLXYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location366 (_cdLXYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location366 (_cdLXYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location366 (_cdLXYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location366 (_cdLXYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location366 (_cdLXYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location367 (_cdNzocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location367 (_cdNzocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location367 (_cdNzocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location367 (_cdNzocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location367 (_cdNzocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location367 (_cdNzocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location367 (_cdNzocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location368 (_cdPo0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location368 (_cdPo0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location368 (_cdPo0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location368 (_cdPo0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location368 (_cdPo0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location368 (_cdPo0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location368 (_cdPo0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location369 (_cdQ28crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location369 (_cdQ28crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location369 (_cdQ28crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location369 (_cdQ28crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location369 (_cdQ28crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location369 (_cdQ28crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location369 (_cdQ28crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location37 (_cW_P0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location37 (_cW_P0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location37 (_cW_P0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location37 (_cW_P0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location37 (_cW_P0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location37 (_cW_P0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location37 (_cW_P0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location370 (_cdTTMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location370 (_cdTTMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location370 (_cdTTMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location370 (_cdTTMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location370 (_cdTTMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location370 (_cdTTMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location370 (_cdTTMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location371 (_cdVvccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location371 (_cdVvccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location371 (_cdVvccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location371 (_cdVvccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location371 (_cdVvccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location371 (_cdVvccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location371 (_cdVvccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location372 (_cdXkocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location372 (_cdXkocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location372 (_cdXkocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location372 (_cdXkocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location372 (_cdXkocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location372 (_cdXkocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location372 (_cdXkocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location373 (_cdZZ0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location373 (_cdZZ0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location373 (_cdZZ0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location373 (_cdZZ0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location373 (_cdZZ0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location373 (_cdZZ0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location373 (_cdZZ0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location374 (_cdan8srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location374 (_cdan8srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location374 (_cdan8srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location374 (_cdan8srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location374 (_cdan8srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location374 (_cdan8srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location374 (_cdan8srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location375 (_cddEMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location375 (_cddEMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location375 (_cddEMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location375 (_cddEMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location375 (_cddEMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location375 (_cddEMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location375 (_cddEMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location376 (_cdfgccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location376 (_cdfgccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location376 (_cdfgccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location376 (_cdfgccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location376 (_cdfgccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location376 (_cdfgccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location376 (_cdfgccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location377 (_cdhVocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location377 (_cdhVocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location377 (_cdhVocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location377 (_cdhVocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location377 (_cdhVocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location377 (_cdhVocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location377 (_cdhVocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location378 (_cdjK0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location378 (_cdjK0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location378 (_cdjK0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location378 (_cdjK0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location378 (_cdjK0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location378 (_cdjK0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location378 (_cdjK0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location379 (_cdlAAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location379 (_cdlAAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location379 (_cdlAAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location379 (_cdlAAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location379 (_cdlAAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location379 (_cdlAAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location379 (_cdlAAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location38 (_cW_P1crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location38 (_cW_P1crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location38 (_cW_P1crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location38 (_cW_P1crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location38 (_cW_P1crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location38 (_cW_P1crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location38 (_cW_P1crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location380 (_cdm1McrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location380 (_cdm1McrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location380 (_cdm1McrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location380 (_cdm1McrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location380 (_cdm1McrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location380 (_cdm1McrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location380 (_cdm1McrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location381 (_cdpRccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location381 (_cdpRccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location381 (_cdpRccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location381 (_cdpRccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location381 (_cdpRccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location381 (_cdpRccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location381 (_cdpRccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location382 (_cdrGocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location382 (_cdrGocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location382 (_cdrGocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location382 (_cdrGocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location382 (_cdrGocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location382 (_cdrGocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location382 (_cdrGocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location383 (_cds70crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location383 (_cds70crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location383 (_cds70crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location383 (_cds70crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location383 (_cds70crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location383 (_cds70crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location383 (_cds70crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location384 (_cduxAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location384 (_cduxAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location384 (_cduxAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location384 (_cduxAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location384 (_cduxAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location384 (_cduxAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location384 (_cduxAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location385 (_cdwmMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location385 (_cdwmMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location385 (_cdwmMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location385 (_cdwmMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location385 (_cdwmMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location385 (_cdwmMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location385 (_cdwmMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location386 (_cdzCccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location386 (_cdzCccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location386 (_cdzCccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location386 (_cdzCccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location386 (_cdzCccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location386 (_cdzCccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location386 (_cdzCccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location387 (_cd1escrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location387 (_cd1escrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location387 (_cd1escrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location387 (_cd1escrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location387 (_cd1escrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location387 (_cd1escrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location387 (_cd1escrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location388 (_cd3T4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location388 (_cd3T4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location388 (_cd3T4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location388 (_cd3T4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location388 (_cd3T4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location388 (_cd3T4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location388 (_cd3T4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location389 (_cd5JEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location389 (_cd5JEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location389 (_cd5JEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location389 (_cd5JEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location389 (_cd5JEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location389 (_cd5JEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location389 (_cd5JEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location39 (_cW_248rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location39 (_cW_248rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location39 (_cW_248rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location39 (_cW_248rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location39 (_cW_248rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location39 (_cW_248rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location39 (_cW_248rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location390 (_cd6-QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location390 (_cd6-QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location390 (_cd6-QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location390 (_cd6-QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location390 (_cd6-QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location390 (_cd6-QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location390 (_cd6-QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location391 (_cd9agcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location391 (_cd9agcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location391 (_cd9agcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location391 (_cd9agcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location391 (_cd9agcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location391 (_cd9agcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location391 (_cd9agcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location392 (_cd_2wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location392 (_cd_2wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location392 (_cd_2wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location392 (_cd_2wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location392 (_cd_2wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location392 (_cd_2wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location392 (_cd_2wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location393 (_ceC6EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location393 (_ceC6EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location393 (_ceC6EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location393 (_ceC6EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location393 (_ceC6EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location393 (_ceC6EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location393 (_ceC6EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location394 (_ceEvQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location394 (_ceEvQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location394 (_ceEvQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location394 (_ceEvQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location394 (_ceEvQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location394 (_ceEvQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location394 (_ceEvQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location395 (_ceHLgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location395 (_ceHLgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location395 (_ceHLgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location395 (_ceHLgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location395 (_ceHLgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location395 (_ceHLgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location395 (_ceHLgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location396 (_ceJnwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location396 (_ceJnwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location396 (_ceJnwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location396 (_ceJnwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location396 (_ceJnwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location396 (_ceJnwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location396 (_ceJnwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location397 (_ceLc8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location397 (_ceLc8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location397 (_ceLc8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location397 (_ceLc8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location397 (_ceLc8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location397 (_ceLc8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location397 (_ceLc8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location398 (_ceN5MMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location398 (_ceN5MMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location398 (_ceN5MMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location398 (_ceN5MMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location398 (_ceN5MMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location398 (_ceN5MMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location398 (_ceN5MMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location399 (_cePuYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location399 (_cePuYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location399 (_cePuYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location399 (_cePuYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location399 (_cePuYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location399 (_cePuYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location399 (_cePuYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location4 (_cW3UDcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location4 (_cW3UDcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location4 (_cW3UDcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location4 (_cW3UDcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location4 (_cW3UDcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location4 (_cW3UDcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location4 (_cW3UDcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location40 (_cXAd8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location40 (_cXAd8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location40 (_cXAd8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location40 (_cXAd8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location40 (_cXAd8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location40 (_cXAd8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location40 (_cXAd8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location400 (_ceSKocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location400 (_ceSKocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location400 (_ceSKocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location400 (_ceSKocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location400 (_ceSKocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location400 (_ceSKocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location400 (_ceSKocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location401 (_ceUm4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location401 (_ceUm4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location401 (_ceUm4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location401 (_ceUm4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location401 (_ceUm4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location401 (_ceUm4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location401 (_ceUm4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location402 (_ceWcEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location402 (_ceWcEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location402 (_ceWcEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location402 (_ceWcEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location402 (_ceWcEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location402 (_ceWcEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location402 (_ceWcEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location403 (_ceYRQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location403 (_ceYRQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location403 (_ceYRQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location403 (_ceYRQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location403 (_ceYRQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location403 (_ceYRQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location403 (_ceYRQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location404 (_ceatgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location404 (_ceatgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location404 (_ceatgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location404 (_ceatgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location404 (_ceatgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location404 (_ceatgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location404 (_ceatgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location405 (_cedw0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location405 (_cedw0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location405 (_cedw0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location405 (_cedw0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location405 (_cedw0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location405 (_cedw0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location405 (_cedw0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location406 (_cegNEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location406 (_cegNEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location406 (_cegNEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location406 (_cegNEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location406 (_cegNEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location406 (_cegNEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location406 (_cegNEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location407 (_ceiCQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location407 (_ceiCQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location407 (_ceiCQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location407 (_ceiCQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location407 (_ceiCQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location407 (_ceiCQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location407 (_ceiCQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location408 (_cekegcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location408 (_cekegcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location408 (_cekegcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location408 (_cekegcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location408 (_cekegcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location408 (_cekegcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location408 (_cekegcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location409 (_cem6wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location409 (_cem6wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location409 (_cem6wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location409 (_cem6wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location409 (_cem6wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location409 (_cem6wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location409 (_cem6wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location41 (_cXAd9crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location41 (_cXAd9crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location41 (_cXAd9crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location41 (_cXAd9crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location41 (_cXAd9crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location41 (_cXAd9crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location41 (_cXAd9crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location410 (_cepXAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location410 (_cepXAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location410 (_cepXAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location410 (_cepXAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location410 (_cepXAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location410 (_cepXAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location410 (_cepXAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location411 (_cerMMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location411 (_cerMMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location411 (_cerMMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location411 (_cerMMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location411 (_cerMMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location411 (_cerMMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location411 (_cerMMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location412 (_cetoccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location412 (_cetoccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location412 (_cetoccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location412 (_cetoccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location412 (_cetoccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location412 (_cetoccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location412 (_cetoccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location413 (_cevdocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location413 (_cevdocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location413 (_cevdocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location413 (_cevdocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location413 (_cevdocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location413 (_cevdocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location413 (_cevdocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location414 (_cexS0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location414 (_cexS0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location414 (_cexS0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location414 (_cexS0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location414 (_cexS0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location414 (_cexS0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location414 (_cexS0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location415 (_cezIAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location415 (_cezIAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location415 (_cezIAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location415 (_cezIAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location415 (_cezIAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location415 (_cezIAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location415 (_cezIAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location416 (_ce1kQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location416 (_ce1kQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location416 (_ce1kQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location416 (_ce1kQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location416 (_ce1kQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location416 (_ce1kQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location416 (_ce1kQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location417 (_ce3ZccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location417 (_ce3ZccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location417 (_ce3ZccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location417 (_ce3ZccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location417 (_ce3ZccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location417 (_ce3ZccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location417 (_ce3ZccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location418 (_ce5OocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location418 (_ce5OocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location418 (_ce5OocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location418 (_ce5OocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location418 (_ce5OocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location418 (_ce5OocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location418 (_ce5OocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location419 (_ce7D0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location419 (_ce7D0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location419 (_ce7D0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location419 (_ce7D0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location419 (_ce7D0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location419 (_ce7D0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location419 (_ce7D0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location42 (_cXBFA8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location42 (_cXBFA8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location42 (_cXBFA8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location42 (_cXBFA8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location42 (_cXBFA8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location42 (_cXBFA8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location42 (_cXBFA8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location420 (_ce85AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location420 (_ce85AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location420 (_ce85AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location420 (_ce85AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location420 (_ce85AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location420 (_ce85AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location420 (_ce85AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location421 (_ce-uMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location421 (_ce-uMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location421 (_ce-uMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location421 (_ce-uMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location421 (_ce-uMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location421 (_ce-uMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location421 (_ce-uMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location422 (_cfBKccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location422 (_cfBKccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location422 (_cfBKccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location422 (_cfBKccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location422 (_cfBKccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location422 (_cfBKccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location422 (_cfBKccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location423 (_cfC_ocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location423 (_cfC_ocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location423 (_cfC_ocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location423 (_cfC_ocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location423 (_cfC_ocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location423 (_cfC_ocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location423 (_cfC_ocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location424 (_cfFb4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location424 (_cfFb4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location424 (_cfFb4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location424 (_cfFb4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location424 (_cfFb4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location424 (_cfFb4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location424 (_cfFb4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location425 (_cfHREcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location425 (_cfHREcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location425 (_cfHREcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location425 (_cfHREcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location425 (_cfHREcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location425 (_cfHREcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location425 (_cfHREcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location426 (_cfJtUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location426 (_cfJtUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location426 (_cfJtUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location426 (_cfJtUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location426 (_cfJtUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location426 (_cfJtUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location426 (_cfJtUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location427 (_cfLigcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location427 (_cfLigcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location427 (_cfLigcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location427 (_cfLigcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location427 (_cfLigcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location427 (_cfLigcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location427 (_cfLigcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location428 (_cfN-wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location428 (_cfN-wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location428 (_cfN-wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location428 (_cfN-wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location428 (_cfN-wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location428 (_cfN-wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location428 (_cfN-wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location429 (_cfQbAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location429 (_cfQbAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location429 (_cfQbAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location429 (_cfQbAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location429 (_cfQbAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location429 (_cfQbAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location429 (_cfQbAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location43 (_cXBsEsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location43 (_cXBsEsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location43 (_cXBsEsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location43 (_cXBsEsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location43 (_cXBsEsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location43 (_cXBsEsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location43 (_cXBsEsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location430 (_cfTeUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location430 (_cfTeUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location430 (_cfTeUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location430 (_cfTeUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location430 (_cfTeUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location430 (_cfTeUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location430 (_cfTeUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location431 (_cfVTgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location431 (_cfVTgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location431 (_cfVTgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location431 (_cfVTgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location431 (_cfVTgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location431 (_cfVTgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location431 (_cfVTgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location432 (_cfXvwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location432 (_cfXvwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location432 (_cfXvwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location432 (_cfXvwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location432 (_cfXvwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location432 (_cfXvwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location432 (_cfXvwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location433 (_cfZk8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location433 (_cfZk8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location433 (_cfZk8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location433 (_cfZk8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location433 (_cfZk8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location433 (_cfZk8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location433 (_cfZk8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location434 (_cfbaIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location434 (_cfbaIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location434 (_cfbaIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location434 (_cfbaIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location434 (_cfbaIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location434 (_cfbaIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location434 (_cfbaIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location435 (_cfd2YcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location435 (_cfd2YcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location435 (_cfd2YcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location435 (_cfd2YcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location435 (_cfd2YcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location435 (_cfd2YcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location435 (_cfd2YcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location436 (_cfgSocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location436 (_cfgSocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location436 (_cfgSocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location436 (_cfgSocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location436 (_cfgSocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location436 (_cfgSocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location436 (_cfgSocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location437 (_cfiH0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location437 (_cfiH0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location437 (_cfiH0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location437 (_cfiH0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location437 (_cfiH0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location437 (_cfiH0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location437 (_cfiH0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location438 (_cfj9AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location438 (_cfj9AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location438 (_cfj9AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location438 (_cfj9AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location438 (_cfj9AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location438 (_cfj9AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location438 (_cfj9AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location439 (_cfmZQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location439 (_cfmZQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location439 (_cfmZQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location439 (_cfmZQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location439 (_cfmZQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location439 (_cfmZQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location439 (_cfmZQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location44 (_cXCTIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location44 (_cXCTIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location44 (_cXCTIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location44 (_cXCTIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location44 (_cXCTIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location44 (_cXCTIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location44 (_cXCTIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location440 (_cfo1gcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location440 (_cfo1gcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location440 (_cfo1gcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location440 (_cfo1gcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location440 (_cfo1gcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location440 (_cfo1gcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location440 (_cfo1gcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location441 (_cfqqscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location441 (_cfqqscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location441 (_cfqqscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location441 (_cfqqscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location441 (_cfqqscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location441 (_cfqqscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location441 (_cfqqscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location442 (_cftG8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location442 (_cftG8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location442 (_cftG8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location442 (_cftG8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location442 (_cftG8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location442 (_cftG8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location442 (_cftG8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location443 (_cfu8IcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location443 (_cfu8IcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location443 (_cfu8IcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location443 (_cfu8IcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location443 (_cfu8IcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location443 (_cfu8IcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location443 (_cfu8IcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location444 (_cfxYYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location444 (_cfxYYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location444 (_cfxYYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location444 (_cfxYYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location444 (_cfxYYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location444 (_cfxYYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location444 (_cfxYYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location445 (_cfzNkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location445 (_cfzNkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location445 (_cfzNkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location445 (_cfzNkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location445 (_cfzNkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location445 (_cfzNkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location445 (_cfzNkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location446 (_cf1p0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location446 (_cf1p0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location446 (_cf1p0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location446 (_cf1p0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location446 (_cf1p0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location446 (_cf1p0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location446 (_cf1p0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location447 (_cf3fAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location447 (_cf3fAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location447 (_cf3fAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location447 (_cf3fAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location447 (_cf3fAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location447 (_cf3fAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location447 (_cf3fAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location448 (_cf57QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location448 (_cf57QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location448 (_cf57QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location448 (_cf57QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location448 (_cf57QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location448 (_cf57QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location448 (_cf57QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location449 (_cf8XgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location449 (_cf8XgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location449 (_cf8XgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location449 (_cf8XgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location449 (_cf8XgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location449 (_cf8XgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location449 (_cf8XgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location45 (_cXCTJcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location45 (_cXCTJcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location45 (_cXCTJcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location45 (_cXCTJcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location45 (_cXCTJcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location45 (_cXCTJcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location45 (_cXCTJcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location450 (_cf-MscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location450 (_cf-MscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location450 (_cf-MscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location450 (_cf-MscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location450 (_cf-MscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location450 (_cf-MscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location450 (_cf-MscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location451 (_cgAo8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location451 (_cgAo8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location451 (_cgAo8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location451 (_cgAo8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location451 (_cgAo8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location451 (_cgAo8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location451 (_cgAo8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location452 (_cgDFMMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location452 (_cgDFMMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location452 (_cgDFMMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location452 (_cgDFMMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location452 (_cgDFMMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location452 (_cgDFMMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location452 (_cgDFMMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location453 (_cgE6YcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location453 (_cgE6YcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location453 (_cgE6YcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location453 (_cgE6YcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location453 (_cgE6YcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location453 (_cgE6YcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location453 (_cgE6YcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location454 (_cgHWocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location454 (_cgHWocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location454 (_cgHWocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location454 (_cgHWocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location454 (_cgHWocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location454 (_cgHWocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location454 (_cgHWocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location455 (_cgJL0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location455 (_cgJL0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location455 (_cgJL0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location455 (_cgJL0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location455 (_cgJL0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location455 (_cgJL0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location455 (_cgJL0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location456 (_cgLoEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location456 (_cgLoEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location456 (_cgLoEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location456 (_cgLoEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location456 (_cgLoEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location456 (_cgLoEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location456 (_cgLoEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location457 (_cgOEUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location457 (_cgOEUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location457 (_cgOEUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location457 (_cgOEUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location457 (_cgOEUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location457 (_cgOEUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location457 (_cgOEUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location458 (_cgP5gcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location458 (_cgP5gcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location458 (_cgP5gcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location458 (_cgP5gcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location458 (_cgP5gcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location458 (_cgP5gcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location458 (_cgP5gcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location459 (_cgSVwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location459 (_cgSVwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location459 (_cgSVwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location459 (_cgSVwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location459 (_cgSVwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location459 (_cgSVwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location459 (_cgSVwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location46 (_cXHyscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location46 (_cXHyscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location46 (_cXHyscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location46 (_cXHyscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location46 (_cXHyscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location46 (_cXHyscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location46 (_cXHyscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location460 (_cgUyAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location460 (_cgUyAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location460 (_cgUyAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location460 (_cgUyAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location460 (_cgUyAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location460 (_cgUyAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location460 (_cgUyAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location461 (_cgWnMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location461 (_cgWnMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location461 (_cgWnMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location461 (_cgWnMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location461 (_cgWnMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location461 (_cgWnMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location461 (_cgWnMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location462 (_cgZDccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location462 (_cgZDccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location462 (_cgZDccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location462 (_cgZDccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location462 (_cgZDccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location462 (_cgZDccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location462 (_cgZDccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location463 (_cgbfscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location463 (_cgbfscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location463 (_cgbfscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location463 (_cgbfscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location463 (_cgbfscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location463 (_cgbfscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location463 (_cgbfscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location464 (_cgd78crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location464 (_cgd78crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location464 (_cgd78crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location464 (_cgd78crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location464 (_cgd78crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location464 (_cgd78crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location464 (_cgd78crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location465 (_cggYMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location465 (_cggYMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location465 (_cggYMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location465 (_cggYMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location465 (_cggYMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location465 (_cggYMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location465 (_cggYMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location466 (_cgi0ccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location466 (_cgi0ccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location466 (_cgi0ccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location466 (_cgi0ccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location466 (_cgi0ccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location466 (_cgi0ccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location466 (_cgi0ccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location467 (_cglQscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location467 (_cglQscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location467 (_cglQscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location467 (_cglQscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location467 (_cglQscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location467 (_cglQscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location467 (_cglQscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location468 (_cgns8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location468 (_cgns8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location468 (_cgns8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location468 (_cgns8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location468 (_cgns8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location468 (_cgns8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location468 (_cgns8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location469 (_cgqJMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location469 (_cgqJMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location469 (_cgqJMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location469 (_cgqJMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location469 (_cgqJMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location469 (_cgqJMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location469 (_cgqJMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location47 (_cXIZwsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location47 (_cXIZwsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location47 (_cXIZwsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location47 (_cXIZwsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location47 (_cXIZwsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location47 (_cXIZwsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location47 (_cXIZwsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location470 (_cgslccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location470 (_cgslccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location470 (_cgslccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location470 (_cgslccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location470 (_cgslccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location470 (_cgslccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location470 (_cgslccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location471 (_cgvBscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location471 (_cgvBscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location471 (_cgvBscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location471 (_cgvBscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location471 (_cgvBscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location471 (_cgvBscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location471 (_cgvBscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location472 (_cgw24crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location472 (_cgw24crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location472 (_cgw24crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location472 (_cgw24crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location472 (_cgw24crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location472 (_cgw24crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location472 (_cgw24crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location473 (_cgzTIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location473 (_cgzTIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location473 (_cgzTIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location473 (_cgzTIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location473 (_cgzTIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location473 (_cgzTIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location473 (_cgzTIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location474 (_cg1vYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location474 (_cg1vYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location474 (_cg1vYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location474 (_cg1vYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location474 (_cg1vYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location474 (_cg1vYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location474 (_cg1vYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location475 (_cg4LocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location475 (_cg4LocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location475 (_cg4LocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location475 (_cg4LocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location475 (_cg4LocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location475 (_cg4LocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location475 (_cg4LocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location476 (_cg6A0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location476 (_cg6A0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location476 (_cg6A0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location476 (_cg6A0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location476 (_cg6A0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location476 (_cg6A0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location476 (_cg6A0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location477 (_cg8dEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location477 (_cg8dEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location477 (_cg8dEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location477 (_cg8dEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location477 (_cg8dEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location477 (_cg8dEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location477 (_cg8dEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location478 (_chAHccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location478 (_chAHccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location478 (_chAHccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location478 (_chAHccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location478 (_chAHccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location478 (_chAHccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location478 (_chAHccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location479 (_chDKwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location479 (_chDKwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location479 (_chDKwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location479 (_chDKwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location479 (_chDKwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location479 (_chDKwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location479 (_chDKwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location48 (_cXIZxsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location48 (_cXIZxsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location48 (_cXIZxsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location48 (_cXIZxsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location48 (_cXIZxsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location48 (_cXIZxsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location48 (_cXIZxsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location480 (_chFnAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location480 (_chFnAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location480 (_chFnAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location480 (_chFnAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location480 (_chFnAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location480 (_chFnAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location480 (_chFnAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location481 (_chIDQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location481 (_chIDQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location481 (_chIDQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location481 (_chIDQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location481 (_chIDQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location481 (_chIDQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location481 (_chIDQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location482 (_chKfgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location482 (_chKfgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location482 (_chKfgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location482 (_chKfgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location482 (_chKfgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location482 (_chKfgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location482 (_chKfgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location483 (_chM7wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location483 (_chM7wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location483 (_chM7wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location483 (_chM7wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location483 (_chM7wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location483 (_chM7wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location483 (_chM7wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location484 (_chOw8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location484 (_chOw8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location484 (_chOw8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location484 (_chOw8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location484 (_chOw8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location484 (_chOw8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location484 (_chOw8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location485 (_chRNMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location485 (_chRNMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location485 (_chRNMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location485 (_chRNMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location485 (_chRNMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location485 (_chRNMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location485 (_chRNMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location486 (_chTpccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location486 (_chTpccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location486 (_chTpccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location486 (_chTpccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location486 (_chTpccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location486 (_chTpccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location486 (_chTpccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location487 (_chWFscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location487 (_chWFscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location487 (_chWFscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location487 (_chWFscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location487 (_chWFscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location487 (_chWFscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location487 (_chWFscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location488 (_chYh8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location488 (_chYh8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location488 (_chYh8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location488 (_chYh8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location488 (_chYh8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location488 (_chYh8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location488 (_chYh8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location489 (_chblQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location489 (_chblQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location489 (_chblQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location489 (_chblQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location489 (_chblQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location489 (_chblQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location489 (_chblQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location49 (_cXJA08rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location49 (_cXJA08rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location49 (_cXJA08rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location49 (_cXJA08rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location49 (_cXJA08rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location49 (_cXJA08rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location49 (_cXJA08rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location490 (_cheokcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location490 (_cheokcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location490 (_cheokcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location490 (_cheokcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location490 (_cheokcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location490 (_cheokcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location490 (_cheokcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location491 (_chhr4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location491 (_chhr4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location491 (_chhr4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location491 (_chhr4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location491 (_chhr4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location491 (_chhr4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location491 (_chhr4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location492 (_chkIIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location492 (_chkIIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location492 (_chkIIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location492 (_chkIIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location492 (_chkIIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location492 (_chkIIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location492 (_chkIIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location493 (_chnLccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location493 (_chnLccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location493 (_chnLccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location493 (_chnLccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location493 (_chnLccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location493 (_chnLccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location493 (_chnLccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location494 (_chqOwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location494 (_chqOwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location494 (_chqOwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location494 (_chqOwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location494 (_chqOwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location494 (_chqOwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location494 (_chqOwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location495 (_chsrAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location495 (_chsrAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location495 (_chsrAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location495 (_chsrAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location495 (_chsrAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location495 (_chsrAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location495 (_chsrAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location496 (_chvuUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location496 (_chvuUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location496 (_chvuUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location496 (_chvuUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location496 (_chvuUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location496 (_chvuUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location496 (_chvuUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location497 (_chyKkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location497 (_chyKkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location497 (_chyKkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location497 (_chyKkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location497 (_chyKkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location497 (_chyKkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location497 (_chyKkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location498 (_ch1N4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location498 (_ch1N4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location498 (_ch1N4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location498 (_ch1N4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location498 (_ch1N4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location498 (_ch1N4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location498 (_ch1N4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location499 (_ch4RMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location499 (_ch4RMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location499 (_ch4RMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location499 (_ch4RMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location499 (_ch4RMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location499 (_ch4RMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location499 (_ch4RMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location5 (_cW3UEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location5 (_cW3UEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location5 (_cW3UEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location5 (_cW3UEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location5 (_cW3UEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location5 (_cW3UEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location5 (_cW3UEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location50 (_cXJA18rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location50 (_cXJA18rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location50 (_cXJA18rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location50 (_cXJA18rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location50 (_cXJA18rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location50 (_cXJA18rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location50 (_cXJA18rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location500 (_ch6tccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location500 (_ch6tccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location500 (_ch6tccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location500 (_ch6tccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location500 (_ch6tccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location500 (_ch6tccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location500 (_ch6tccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location501 (_ch9JscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location501 (_ch9JscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location501 (_ch9JscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location501 (_ch9JscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location501 (_ch9JscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location501 (_ch9JscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location501 (_ch9JscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location502 (_ch_l8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location502 (_ch_l8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location502 (_ch_l8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location502 (_ch_l8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location502 (_ch_l8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location502 (_ch_l8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location502 (_ch_l8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location503 (_ciCCMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location503 (_ciCCMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location503 (_ciCCMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location503 (_ciCCMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location503 (_ciCCMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location503 (_ciCCMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location503 (_ciCCMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location504 (_ciEeccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location504 (_ciEeccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location504 (_ciEeccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location504 (_ciEeccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location504 (_ciEeccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location504 (_ciEeccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location504 (_ciEeccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location505 (_ciG6scrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location505 (_ciG6scrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location505 (_ciG6scrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location505 (_ciG6scrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location505 (_ciG6scrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location505 (_ciG6scrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location505 (_ciG6scrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location506 (_ciJW8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location506 (_ciJW8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location506 (_ciJW8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location506 (_ciJW8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location506 (_ciJW8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location506 (_ciJW8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location506 (_ciJW8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location507 (_ciLzMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location507 (_ciLzMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location507 (_ciLzMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location507 (_ciLzMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location507 (_ciLzMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location507 (_ciLzMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location507 (_ciLzMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location508 (_ciOPccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location508 (_ciOPccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location508 (_ciOPccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location508 (_ciOPccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location508 (_ciOPccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location508 (_ciOPccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location508 (_ciOPccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location509 (_ciQrscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location509 (_ciQrscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location509 (_ciQrscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location509 (_ciQrscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location509 (_ciQrscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location509 (_ciQrscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location509 (_ciQrscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location51 (_cXJn4srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location51 (_cXJn4srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location51 (_cXJn4srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location51 (_cXJn4srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location51 (_cXJn4srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location51 (_cXJn4srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location51 (_cXJn4srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location510 (_ciTH8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location510 (_ciTH8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location510 (_ciTH8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location510 (_ciTH8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location510 (_ciTH8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location510 (_ciTH8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location510 (_ciTH8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location511 (_ciVkMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location511 (_ciVkMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location511 (_ciVkMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location511 (_ciVkMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location511 (_ciVkMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location511 (_ciVkMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location511 (_ciVkMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location512 (_ciYAccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location512 (_ciYAccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location512 (_ciYAccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location512 (_ciYAccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location512 (_ciYAccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location512 (_ciYAccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location512 (_ciYAccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location513 (_ciacscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location513 (_ciacscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location513 (_ciacscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location513 (_ciacscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location513 (_ciacscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location513 (_ciacscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location513 (_ciacscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location514 (_cidgAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location514 (_cidgAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location514 (_cidgAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location514 (_cidgAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location514 (_cidgAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location514 (_cidgAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location514 (_cidgAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location515 (_cif8QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location515 (_cif8QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location515 (_cif8QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location515 (_cif8QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location515 (_cif8QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location515 (_cif8QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location515 (_cif8QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location516 (_cii_kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location516 (_cii_kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location516 (_cii_kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location516 (_cii_kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location516 (_cii_kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location516 (_cii_kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location516 (_cii_kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location517 (_cilb0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location517 (_cilb0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location517 (_cilb0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location517 (_cilb0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location517 (_cilb0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location517 (_cilb0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location517 (_cilb0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location518 (_cin4EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location518 (_cin4EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location518 (_cin4EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location518 (_cin4EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location518 (_cin4EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location518 (_cin4EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location518 (_cin4EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location519 (_ciqUUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location519 (_ciqUUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location519 (_ciqUUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location519 (_ciqUUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location519 (_ciqUUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location519 (_ciqUUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location519 (_ciqUUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location52 (_cXJn5srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location52 (_cXJn5srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location52 (_cXJn5srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location52 (_cXJn5srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location52 (_cXJn5srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location52 (_cXJn5srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location52 (_cXJn5srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location520 (_ciswkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location520 (_ciswkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location520 (_ciswkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location520 (_ciswkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location520 (_ciswkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location520 (_ciswkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location520 (_ciswkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location521 (_civM0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location521 (_civM0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location521 (_civM0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location521 (_civM0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location521 (_civM0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location521 (_civM0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location521 (_civM0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location522 (_cixpEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location522 (_cixpEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location522 (_cixpEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location522 (_cixpEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location522 (_cixpEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location522 (_cixpEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location522 (_cixpEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location523 (_ci0FUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location523 (_ci0FUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location523 (_ci0FUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location523 (_ci0FUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location523 (_ci0FUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location523 (_ci0FUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location523 (_ci0FUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location524 (_ci3IocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location524 (_ci3IocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location524 (_ci3IocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location524 (_ci3IocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location524 (_ci3IocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location524 (_ci3IocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location524 (_ci3IocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location525 (_ci5k4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location525 (_ci5k4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location525 (_ci5k4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location525 (_ci5k4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location525 (_ci5k4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location525 (_ci5k4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location525 (_ci5k4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location526 (_ci8BIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location526 (_ci8BIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location526 (_ci8BIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location526 (_ci8BIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location526 (_ci8BIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location526 (_ci8BIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location526 (_ci8BIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location527 (_ci_EccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location527 (_ci_EccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location527 (_ci_EccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location527 (_ci_EccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location527 (_ci_EccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location527 (_ci_EccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location527 (_ci_EccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location528 (_cjBgscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location528 (_cjBgscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location528 (_cjBgscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location528 (_cjBgscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location528 (_cjBgscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location528 (_cjBgscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location528 (_cjBgscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location529 (_cjD88crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location529 (_cjD88crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location529 (_cjD88crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location529 (_cjD88crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location529 (_cjD88crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location529 (_cjD88crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location529 (_cjD88crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location53 (_cXKO8srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location53 (_cXKO8srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location53 (_cXKO8srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location53 (_cXKO8srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location53 (_cXKO8srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location53 (_cXKO8srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location53 (_cXKO8srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location530 (_cjHAQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location530 (_cjHAQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location530 (_cjHAQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location530 (_cjHAQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location530 (_cjHAQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location530 (_cjHAQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location530 (_cjHAQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location531 (_cjJcgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location531 (_cjJcgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location531 (_cjJcgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location531 (_cjJcgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location531 (_cjJcgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location531 (_cjJcgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location531 (_cjJcgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location532 (_cjL4wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location532 (_cjL4wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location532 (_cjL4wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location532 (_cjL4wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location532 (_cjL4wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location532 (_cjL4wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location532 (_cjL4wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location533 (_cjO8EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location533 (_cjO8EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location533 (_cjO8EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location533 (_cjO8EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location533 (_cjO8EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location533 (_cjO8EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location533 (_cjO8EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location534 (_cjRYUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location534 (_cjRYUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location534 (_cjRYUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location534 (_cjRYUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location534 (_cjRYUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location534 (_cjRYUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location534 (_cjRYUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location535 (_cjT0kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location535 (_cjT0kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location535 (_cjT0kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location535 (_cjT0kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location535 (_cjT0kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location535 (_cjT0kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location535 (_cjT0kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location536 (_cjW34crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location536 (_cjW34crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location536 (_cjW34crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location536 (_cjW34crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location536 (_cjW34crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location536 (_cjW34crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location536 (_cjW34crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location537 (_cjZUIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location537 (_cjZUIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location537 (_cjZUIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location537 (_cjZUIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location537 (_cjZUIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location537 (_cjZUIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location537 (_cjZUIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location538 (_cjbwYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location538 (_cjbwYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location538 (_cjbwYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location538 (_cjbwYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location538 (_cjbwYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location538 (_cjbwYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location538 (_cjbwYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location539 (_cjeMocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location539 (_cjeMocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location539 (_cjeMocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location539 (_cjeMocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location539 (_cjeMocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location539 (_cjeMocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location539 (_cjeMocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location54 (_cXK2AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location54 (_cXK2AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location54 (_cXK2AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location54 (_cXK2AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location54 (_cXK2AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location54 (_cXK2AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location54 (_cXK2AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location540 (_cjhP8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location540 (_cjhP8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location540 (_cjhP8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location540 (_cjhP8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location540 (_cjhP8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location540 (_cjhP8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location540 (_cjhP8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location541 (_cjjsMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location541 (_cjjsMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location541 (_cjjsMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location541 (_cjjsMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location541 (_cjjsMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location541 (_cjjsMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location541 (_cjjsMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location542 (_cjmIccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location542 (_cjmIccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location542 (_cjmIccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location542 (_cjmIccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location542 (_cjmIccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location542 (_cjmIccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location542 (_cjmIccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location543 (_cjokscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location543 (_cjokscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location543 (_cjokscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location543 (_cjokscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location543 (_cjokscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location543 (_cjokscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location543 (_cjokscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location544 (_cjroAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location544 (_cjroAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location544 (_cjroAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location544 (_cjroAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location544 (_cjroAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location544 (_cjroAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location544 (_cjroAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location545 (_cjuEQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location545 (_cjuEQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location545 (_cjuEQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location545 (_cjuEQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location545 (_cjuEQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location545 (_cjuEQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location545 (_cjuEQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location546 (_cjwggcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location546 (_cjwggcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location546 (_cjwggcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location546 (_cjwggcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location546 (_cjwggcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location546 (_cjwggcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location546 (_cjwggcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location547 (_cjy8wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location547 (_cjy8wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location547 (_cjy8wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location547 (_cjy8wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location547 (_cjy8wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location547 (_cjy8wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location547 (_cjy8wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location548 (_cj2AEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location548 (_cj2AEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location548 (_cj2AEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location548 (_cj2AEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location548 (_cj2AEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location548 (_cj2AEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location548 (_cj2AEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location549 (_cj4cUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location549 (_cj4cUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location549 (_cj4cUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location549 (_cj4cUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location549 (_cj4cUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location549 (_cj4cUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location549 (_cj4cUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location55 (_cXK2BcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location55 (_cXK2BcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location55 (_cXK2BcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location55 (_cXK2BcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location55 (_cXK2BcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location55 (_cXK2BcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location55 (_cXK2BcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location550 (_cj64kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location550 (_cj64kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location550 (_cj64kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location550 (_cj64kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location550 (_cj64kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location550 (_cj64kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location550 (_cj64kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location551 (_cj9U0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location551 (_cj9U0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location551 (_cj9U0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location551 (_cj9U0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location551 (_cj9U0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location551 (_cj9U0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location551 (_cj9U0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location552 (_ckAYIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location552 (_ckAYIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location552 (_ckAYIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location552 (_ckAYIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location552 (_ckAYIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location552 (_ckAYIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location552 (_ckAYIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location553 (_ckC0YcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location553 (_ckC0YcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location553 (_ckC0YcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location553 (_ckC0YcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location553 (_ckC0YcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location553 (_ckC0YcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location553 (_ckC0YcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location554 (_ckF3scrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location554 (_ckF3scrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location554 (_ckF3scrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location554 (_ckF3scrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location554 (_ckF3scrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location554 (_ckF3scrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location554 (_ckF3scrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location555 (_ckIT8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location555 (_ckIT8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location555 (_ckIT8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location555 (_ckIT8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location555 (_ckIT8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location555 (_ckIT8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location555 (_ckIT8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location556 (_ckLXQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location556 (_ckLXQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location556 (_ckLXQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location556 (_ckLXQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location556 (_ckLXQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location556 (_ckLXQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location556 (_ckLXQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location557 (_ckNzgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location557 (_ckNzgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location557 (_ckNzgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location557 (_ckNzgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location557 (_ckNzgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location557 (_ckNzgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location557 (_ckNzgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location558 (_ckQ20crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location558 (_ckQ20crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location558 (_ckQ20crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location558 (_ckQ20crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location558 (_ckQ20crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location558 (_ckQ20crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location558 (_ckQ20crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location559 (_ckTTEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location559 (_ckTTEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location559 (_ckTTEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location559 (_ckTTEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location559 (_ckTTEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location559 (_ckTTEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location559 (_ckTTEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location56 (_cXLdE8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location56 (_cXLdE8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location56 (_cXLdE8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location56 (_cXLdE8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location56 (_cXLdE8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location56 (_cXLdE8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location56 (_cXLdE8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location560 (_ckVvUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location560 (_ckVvUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location560 (_ckVvUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location560 (_ckVvUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location560 (_ckVvUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location560 (_ckVvUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location560 (_ckVvUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location561 (_ckYyocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location561 (_ckYyocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location561 (_ckYyocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location561 (_ckYyocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location561 (_ckYyocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location561 (_ckYyocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location561 (_ckYyocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location562 (_ckcdAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location562 (_ckcdAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location562 (_ckcdAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location562 (_ckcdAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location562 (_ckcdAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location562 (_ckcdAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location562 (_ckcdAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location563 (_ckgHYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location563 (_ckgHYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location563 (_ckgHYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location563 (_ckgHYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location563 (_ckgHYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location563 (_ckgHYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location563 (_ckgHYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location564 (_ckjKscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location564 (_ckjKscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location564 (_ckjKscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location564 (_ckjKscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location564 (_ckjKscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location564 (_ckjKscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location564 (_ckjKscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location565 (_ckmOAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location565 (_ckmOAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location565 (_ckmOAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location565 (_ckmOAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location565 (_ckmOAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location565 (_ckmOAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location565 (_ckmOAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location566 (_ckoqQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location566 (_ckoqQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location566 (_ckoqQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location566 (_ckoqQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location566 (_ckoqQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location566 (_ckoqQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location566 (_ckoqQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location567 (_ckrtkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location567 (_ckrtkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location567 (_ckrtkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location567 (_ckrtkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location567 (_ckrtkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location567 (_ckrtkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location567 (_ckrtkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location568 (_ckuJ0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location568 (_ckuJ0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location568 (_ckuJ0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location568 (_ckuJ0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location568 (_ckuJ0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location568 (_ckuJ0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location568 (_ckuJ0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location569 (_ckxNIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location569 (_ckxNIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location569 (_ckxNIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location569 (_ckxNIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location569 (_ckxNIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location569 (_ckxNIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location569 (_ckxNIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location57 (_cXLdF8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location57 (_cXLdF8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location57 (_cXLdF8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location57 (_cXLdF8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location57 (_cXLdF8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location57 (_cXLdF8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location57 (_cXLdF8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location570 (_ckzpYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location570 (_ckzpYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location570 (_ckzpYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location570 (_ckzpYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location570 (_ckzpYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location570 (_ckzpYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location570 (_ckzpYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location571 (_ck2sscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location571 (_ck2sscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location571 (_ck2sscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location571 (_ck2sscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location571 (_ck2sscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location571 (_ck2sscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location571 (_ck2sscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location572 (_ck5wAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location572 (_ck5wAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location572 (_ck5wAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location572 (_ck5wAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location572 (_ck5wAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location572 (_ck5wAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location572 (_ck5wAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location573 (_ck8zUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location573 (_ck8zUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location573 (_ck8zUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location573 (_ck8zUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location573 (_ck8zUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location573 (_ck8zUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location573 (_ck8zUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location574 (_ck_PkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location574 (_ck_PkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location574 (_ck_PkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location574 (_ck_PkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location574 (_ck_PkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location574 (_ck_PkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location574 (_ck_PkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location575 (_clCS4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location575 (_clCS4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location575 (_clCS4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location575 (_clCS4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location575 (_clCS4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location575 (_clCS4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location575 (_clCS4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location576 (_clEvIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location576 (_clEvIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location576 (_clEvIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location576 (_clEvIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location576 (_clEvIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location576 (_clEvIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location576 (_clEvIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location577 (_clHyccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location577 (_clHyccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location577 (_clHyccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location577 (_clHyccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location577 (_clHyccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location577 (_clHyccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location577 (_clHyccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location578 (_clKOscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location578 (_clKOscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location578 (_clKOscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location578 (_clKOscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location578 (_clKOscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location578 (_clKOscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location578 (_clKOscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location579 (_clNSAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location579 (_clNSAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location579 (_clNSAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location579 (_clNSAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location579 (_clNSAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location579 (_clNSAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location579 (_clNSAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location58 (_cXMEI8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location58 (_cXMEI8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location58 (_cXMEI8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location58 (_cXMEI8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location58 (_cXMEI8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location58 (_cXMEI8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location58 (_cXMEI8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location580 (_clQVUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location580 (_clQVUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location580 (_clQVUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location580 (_clQVUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location580 (_clQVUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location580 (_clQVUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location580 (_clQVUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location581 (_clSxkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location581 (_clSxkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location581 (_clSxkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location581 (_clSxkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location581 (_clSxkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location581 (_clSxkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location581 (_clSxkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location582 (_clV04crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location582 (_clV04crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location582 (_clV04crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location582 (_clV04crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location582 (_clV04crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location582 (_clV04crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location582 (_clV04crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location583 (_clYRIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location583 (_clYRIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location583 (_clYRIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location583 (_clYRIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location583 (_clYRIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location583 (_clYRIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location583 (_clYRIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location584 (_clbUccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location584 (_clbUccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location584 (_clbUccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location584 (_clbUccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location584 (_clbUccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location584 (_clbUccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location584 (_clbUccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location585 (_cleXwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location585 (_cleXwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location585 (_cleXwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location585 (_cleXwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location585 (_cleXwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location585 (_cleXwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location585 (_cleXwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location586 (_clg0AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location586 (_clg0AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location586 (_clg0AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location586 (_clg0AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location586 (_clg0AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location586 (_clg0AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location586 (_clg0AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location587 (_clj3UcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location587 (_clj3UcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location587 (_clj3UcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location587 (_clj3UcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location587 (_clj3UcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location587 (_clj3UcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location587 (_clj3UcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location588 (_clm6ocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location588 (_clm6ocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location588 (_clm6ocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location588 (_clm6ocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location588 (_clm6ocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location588 (_clm6ocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location588 (_clm6ocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location589 (_clp98crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location589 (_clp98crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location589 (_clp98crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location589 (_clp98crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location589 (_clp98crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location589 (_clp98crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location589 (_clp98crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location59 (_cXMEJ8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location59 (_cXMEJ8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location59 (_cXMEJ8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location59 (_cXMEJ8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location59 (_cXMEJ8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location59 (_cXMEJ8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location59 (_cXMEJ8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location590 (_clsaMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location590 (_clsaMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location590 (_clsaMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location590 (_clsaMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location590 (_clsaMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location590 (_clsaMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location590 (_clsaMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location591 (_clvdgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location591 (_clvdgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location591 (_clvdgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location591 (_clvdgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location591 (_clvdgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location591 (_clvdgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location591 (_clvdgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location592 (_clx5wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location592 (_clx5wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location592 (_clx5wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location592 (_clx5wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location592 (_clx5wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location592 (_clx5wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location592 (_clx5wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location593 (_cl09EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location593 (_cl09EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location593 (_cl09EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location593 (_cl09EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location593 (_cl09EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location593 (_cl09EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location593 (_cl09EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location594 (_cl3ZUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location594 (_cl3ZUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location594 (_cl3ZUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location594 (_cl3ZUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location594 (_cl3ZUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location594 (_cl3ZUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location594 (_cl3ZUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location595 (_cl6cocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location595 (_cl6cocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location595 (_cl6cocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location595 (_cl6cocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location595 (_cl6cocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location595 (_cl6cocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location595 (_cl6cocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location596 (_cl844crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location596 (_cl844crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location596 (_cl844crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location596 (_cl844crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location596 (_cl844crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location596 (_cl844crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location596 (_cl844crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location597 (_cl_8McrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location597 (_cl_8McrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location597 (_cl_8McrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location597 (_cl_8McrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location597 (_cl_8McrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location597 (_cl_8McrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location597 (_cl_8McrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location598 (_cmCYccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location598 (_cmCYccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location598 (_cmCYccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location598 (_cmCYccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location598 (_cmCYccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location598 (_cmCYccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location598 (_cmCYccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location599 (_cmFbwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location599 (_cmFbwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location599 (_cmFbwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location599 (_cmFbwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location599 (_cmFbwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location599 (_cmFbwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location599 (_cmFbwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location6 (_cW37EsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location6 (_cW37EsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location6 (_cW37EsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location6 (_cW37EsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location6 (_cW37EsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location6 (_cW37EsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location6 (_cW37EsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location60 (_cXMrMsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location60 (_cXMrMsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location60 (_cXMrMsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location60 (_cXMrMsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location60 (_cXMrMsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location60 (_cXMrMsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location60 (_cXMrMsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location600 (_cmIfEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location600 (_cmIfEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location600 (_cmIfEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location600 (_cmIfEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location600 (_cmIfEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location600 (_cmIfEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location600 (_cmIfEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location601 (_cmLiYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location601 (_cmLiYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location601 (_cmLiYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location601 (_cmLiYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location601 (_cmLiYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location601 (_cmLiYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location601 (_cmLiYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location602 (_cmN-ocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location602 (_cmN-ocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location602 (_cmN-ocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location602 (_cmN-ocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location602 (_cmN-ocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location602 (_cmN-ocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location602 (_cmN-ocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location603 (_cmRB8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location603 (_cmRB8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location603 (_cmRB8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location603 (_cmRB8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location603 (_cmRB8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location603 (_cmRB8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location603 (_cmRB8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location604 (_cmUFQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location604 (_cmUFQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location604 (_cmUFQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location604 (_cmUFQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location604 (_cmUFQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location604 (_cmUFQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location604 (_cmUFQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location605 (_cmWhgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location605 (_cmWhgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location605 (_cmWhgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location605 (_cmWhgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location605 (_cmWhgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location605 (_cmWhgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location605 (_cmWhgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location606 (_cmZk0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location606 (_cmZk0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location606 (_cmZk0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location606 (_cmZk0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location606 (_cmZk0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location606 (_cmZk0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location606 (_cmZk0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location607 (_cmcBEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location607 (_cmcBEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location607 (_cmcBEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location607 (_cmcBEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location607 (_cmcBEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location607 (_cmcBEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location607 (_cmcBEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location608 (_cmgSgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location608 (_cmgSgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location608 (_cmgSgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location608 (_cmgSgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location608 (_cmgSgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location608 (_cmgSgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location608 (_cmgSgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location609 (_cmjV0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location609 (_cmjV0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location609 (_cmjV0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location609 (_cmjV0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location609 (_cmjV0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location609 (_cmjV0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location609 (_cmjV0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location61 (_cXMrNsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location61 (_cXMrNsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location61 (_cXMrNsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location61 (_cXMrNsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location61 (_cXMrNsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location61 (_cXMrNsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location61 (_cXMrNsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location610 (_cmmZIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location610 (_cmmZIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location610 (_cmmZIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location610 (_cmmZIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location610 (_cmmZIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location610 (_cmmZIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location610 (_cmmZIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location611 (_cmpcccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location611 (_cmpcccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location611 (_cmpcccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location611 (_cmpcccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location611 (_cmpcccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location611 (_cmpcccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location611 (_cmpcccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location612 (_cmsfwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location612 (_cmsfwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location612 (_cmsfwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location612 (_cmsfwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location612 (_cmsfwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location612 (_cmsfwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location612 (_cmsfwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location613 (_cmvjEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location613 (_cmvjEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location613 (_cmvjEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location613 (_cmvjEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location613 (_cmvjEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location613 (_cmvjEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location613 (_cmvjEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location614 (_cmymYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location614 (_cmymYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location614 (_cmymYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location614 (_cmymYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location614 (_cmymYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location614 (_cmymYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location614 (_cmymYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location615 (_cm1pscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location615 (_cm1pscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location615 (_cm1pscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location615 (_cm1pscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location615 (_cm1pscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location615 (_cm1pscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location615 (_cm1pscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location616 (_cm4tAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location616 (_cm4tAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location616 (_cm4tAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location616 (_cm4tAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location616 (_cm4tAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location616 (_cm4tAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location616 (_cm4tAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location617 (_cm7wUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location617 (_cm7wUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location617 (_cm7wUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location617 (_cm7wUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location617 (_cm7wUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location617 (_cm7wUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location617 (_cm7wUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location618 (_cm-zocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location618 (_cm-zocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location618 (_cm-zocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location618 (_cm-zocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location618 (_cm-zocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location618 (_cm-zocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location618 (_cm-zocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location619 (_cnB28crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location619 (_cnB28crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location619 (_cnB28crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location619 (_cnB28crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location619 (_cnB28crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location619 (_cnB28crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location619 (_cnB28crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location62 (_cXNSQsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location62 (_cXNSQsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location62 (_cXNSQsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location62 (_cXNSQsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location62 (_cXNSQsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location62 (_cXNSQsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location62 (_cXNSQsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location620 (_cnE6QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location620 (_cnE6QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location620 (_cnE6QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location620 (_cnE6QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location620 (_cnE6QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location620 (_cnE6QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location620 (_cnE6QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location621 (_cnH9kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location621 (_cnH9kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location621 (_cnH9kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location621 (_cnH9kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location621 (_cnH9kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location621 (_cnH9kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location621 (_cnH9kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location622 (_cnLA4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location622 (_cnLA4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location622 (_cnLA4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location622 (_cnLA4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location622 (_cnLA4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location622 (_cnLA4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location622 (_cnLA4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location623 (_cnOEMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location623 (_cnOEMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location623 (_cnOEMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location623 (_cnOEMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location623 (_cnOEMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location623 (_cnOEMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location623 (_cnOEMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location624 (_cnRHgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location624 (_cnRHgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location624 (_cnRHgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location624 (_cnRHgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location624 (_cnRHgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location624 (_cnRHgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location624 (_cnRHgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location625 (_cnUK0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location625 (_cnUK0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location625 (_cnUK0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location625 (_cnUK0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location625 (_cnUK0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location625 (_cnUK0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location625 (_cnUK0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location626 (_cnXOIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location626 (_cnXOIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location626 (_cnXOIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location626 (_cnXOIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location626 (_cnXOIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location626 (_cnXOIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location626 (_cnXOIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location627 (_cncGocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location627 (_cncGocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location627 (_cncGocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location627 (_cncGocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location627 (_cncGocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location627 (_cncGocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location627 (_cncGocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location628 (_cng_IcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location628 (_cng_IcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location628 (_cng_IcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location628 (_cng_IcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location628 (_cng_IcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location628 (_cng_IcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location628 (_cng_IcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location629 (_cnkCccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location629 (_cnkCccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location629 (_cnkCccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location629 (_cnkCccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location629 (_cnkCccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location629 (_cnkCccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location629 (_cnkCccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location63 (_cXNSRsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location63 (_cXNSRsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location63 (_cXNSRsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location63 (_cXNSRsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location63 (_cXNSRsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location63 (_cXNSRsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location63 (_cXNSRsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location630 (_cnnFwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location630 (_cnnFwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location630 (_cnnFwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location630 (_cnnFwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location630 (_cnnFwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location630 (_cnnFwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location630 (_cnnFwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location631 (_cnqJEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location631 (_cnqJEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location631 (_cnqJEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location631 (_cnqJEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location631 (_cnqJEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location631 (_cnqJEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location631 (_cnqJEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location632 (_cntMYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location632 (_cntMYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location632 (_cntMYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location632 (_cntMYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location632 (_cntMYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location632 (_cntMYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location632 (_cntMYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location633 (_cnwPscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location633 (_cnwPscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location633 (_cnwPscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location633 (_cnwPscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location633 (_cnwPscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location633 (_cnwPscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location633 (_cnwPscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location634 (_cnzTAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location634 (_cnzTAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location634 (_cnzTAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location634 (_cnzTAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location634 (_cnzTAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location634 (_cnzTAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location634 (_cnzTAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location635 (_cn2WUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location635 (_cn2WUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location635 (_cn2WUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location635 (_cn2WUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location635 (_cn2WUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location635 (_cn2WUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location635 (_cn2WUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location636 (_cn5ZocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location636 (_cn5ZocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location636 (_cn5ZocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location636 (_cn5ZocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location636 (_cn5ZocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location636 (_cn5ZocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location636 (_cn5ZocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location637 (_cn8c8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location637 (_cn8c8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location637 (_cn8c8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location637 (_cn8c8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location637 (_cn8c8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location637 (_cn8c8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location637 (_cn8c8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location638 (_cn_gQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location638 (_cn_gQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location638 (_cn_gQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location638 (_cn_gQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location638 (_cn_gQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location638 (_cn_gQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location638 (_cn_gQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location639 (_coCjkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location639 (_coCjkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location639 (_coCjkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location639 (_coCjkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location639 (_coCjkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location639 (_coCjkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location639 (_coCjkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location64 (_cXN5UsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location64 (_cXN5UsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location64 (_cXN5UsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location64 (_cXN5UsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location64 (_cXN5UsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location64 (_cXN5UsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location64 (_cXN5UsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location640 (_coFm4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location640 (_coFm4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location640 (_coFm4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location640 (_coFm4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location640 (_coFm4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location640 (_coFm4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location640 (_coFm4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location641 (_coIqMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location641 (_coIqMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location641 (_coIqMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location641 (_coIqMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location641 (_coIqMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location641 (_coIqMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location641 (_coIqMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location642 (_coLtgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location642 (_coLtgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location642 (_coLtgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location642 (_coLtgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location642 (_coLtgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location642 (_coLtgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location642 (_coLtgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location643 (_coOw0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location643 (_coOw0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location643 (_coOw0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location643 (_coOw0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location643 (_coOw0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location643 (_coOw0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location643 (_coOw0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location644 (_coR0IcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location644 (_coR0IcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location644 (_coR0IcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location644 (_coR0IcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location644 (_coR0IcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location644 (_coR0IcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location644 (_coR0IcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location645 (_coU3ccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location645 (_coU3ccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location645 (_coU3ccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location645 (_coU3ccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location645 (_coU3ccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location645 (_coU3ccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location645 (_coU3ccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location646 (_coX6wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location646 (_coX6wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location646 (_coX6wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location646 (_coX6wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location646 (_coX6wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location646 (_coX6wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location646 (_coX6wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location647 (_coa-EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location647 (_coa-EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location647 (_coa-EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location647 (_coa-EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location647 (_coa-EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location647 (_coa-EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location647 (_coa-EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location648 (_coeoccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location648 (_coeoccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location648 (_coeoccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location648 (_coeoccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location648 (_coeoccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location648 (_coeoccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location648 (_coeoccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location649 (_coiS0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location649 (_coiS0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location649 (_coiS0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location649 (_coiS0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location649 (_coiS0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location649 (_coiS0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location649 (_coiS0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location65 (_cXN5VsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location65 (_cXN5VsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location65 (_cXN5VsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location65 (_cXN5VsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location65 (_cXN5VsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location65 (_cXN5VsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location65 (_cXN5VsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location650 (_col9McrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location650 (_col9McrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location650 (_col9McrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location650 (_col9McrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location650 (_col9McrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location650 (_col9McrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location650 (_col9McrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location651 (_copAgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location651 (_copAgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location651 (_copAgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location651 (_copAgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location651 (_copAgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location651 (_copAgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location651 (_copAgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location652 (_cosD0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location652 (_cosD0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location652 (_cosD0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location652 (_cosD0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location652 (_cosD0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location652 (_cosD0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location652 (_cosD0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location653 (_covHIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location653 (_covHIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location653 (_covHIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location653 (_covHIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location653 (_covHIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location653 (_covHIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location653 (_covHIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location654 (_coyxgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location654 (_coyxgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location654 (_coyxgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location654 (_coyxgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location654 (_coyxgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location654 (_coyxgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location654 (_coyxgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location655 (_co100crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location655 (_co100crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location655 (_co100crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location655 (_co100crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location655 (_co100crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location655 (_co100crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location655 (_co100crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location656 (_co44IcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location656 (_co44IcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location656 (_co44IcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location656 (_co44IcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location656 (_co44IcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location656 (_co44IcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location656 (_co44IcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location657 (_co8igcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location657 (_co8igcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location657 (_co8igcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location657 (_co8igcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location657 (_co8igcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location657 (_co8igcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location657 (_co8igcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location658 (_co_l0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location658 (_co_l0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location658 (_co_l0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location658 (_co_l0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location658 (_co_l0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location658 (_co_l0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location658 (_co_l0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location659 (_cpCpIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location659 (_cpCpIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location659 (_cpCpIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location659 (_cpCpIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location659 (_cpCpIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location659 (_cpCpIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location659 (_cpCpIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location66 (_cXOgYsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location66 (_cXOgYsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location66 (_cXOgYsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location66 (_cXOgYsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location66 (_cXOgYsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location66 (_cXOgYsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location66 (_cXOgYsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location660 (_cpGTgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location660 (_cpGTgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location660 (_cpGTgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location660 (_cpGTgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location660 (_cpGTgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location660 (_cpGTgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location660 (_cpGTgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location661 (_cpJW0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location661 (_cpJW0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location661 (_cpJW0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location661 (_cpJW0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location661 (_cpJW0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location661 (_cpJW0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location661 (_cpJW0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location662 (_cpMaIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location662 (_cpMaIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location662 (_cpMaIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location662 (_cpMaIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location662 (_cpMaIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location662 (_cpMaIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location662 (_cpMaIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location663 (_cpQEgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location663 (_cpQEgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location663 (_cpQEgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location663 (_cpQEgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location663 (_cpQEgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location663 (_cpQEgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location663 (_cpQEgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location664 (_cpTH0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location664 (_cpTH0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location664 (_cpTH0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location664 (_cpTH0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location664 (_cpTH0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location664 (_cpTH0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location664 (_cpTH0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location665 (_cpWyMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location665 (_cpWyMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location665 (_cpWyMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location665 (_cpWyMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location665 (_cpWyMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location665 (_cpWyMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location665 (_cpWyMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location666 (_cpZ1gcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location666 (_cpZ1gcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location666 (_cpZ1gcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location666 (_cpZ1gcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location666 (_cpZ1gcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location666 (_cpZ1gcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location666 (_cpZ1gcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location667 (_cpc40crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location667 (_cpc40crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location667 (_cpc40crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location667 (_cpc40crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location667 (_cpc40crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location667 (_cpc40crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location667 (_cpc40crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location668 (_cpgjMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location668 (_cpgjMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location668 (_cpgjMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location668 (_cpgjMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location668 (_cpgjMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location668 (_cpgjMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location668 (_cpgjMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location669 (_cpjmgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location669 (_cpjmgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location669 (_cpjmgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location669 (_cpjmgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location669 (_cpjmgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location669 (_cpjmgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location669 (_cpjmgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location67 (_cXOgZsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location67 (_cXOgZsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location67 (_cXOgZsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location67 (_cXOgZsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location67 (_cXOgZsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location67 (_cXOgZsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location67 (_cXOgZsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location670 (_cpmp0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location670 (_cpmp0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location670 (_cpmp0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location670 (_cpmp0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location670 (_cpmp0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location670 (_cpmp0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location670 (_cpmp0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location671 (_cpqUMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location671 (_cpqUMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location671 (_cpqUMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location671 (_cpqUMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location671 (_cpqUMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location671 (_cpqUMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location671 (_cpqUMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location672 (_cptXgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location672 (_cptXgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location672 (_cptXgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location672 (_cptXgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location672 (_cptXgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location672 (_cptXgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location672 (_cptXgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location673 (_cpxB4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location673 (_cpxB4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location673 (_cpxB4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location673 (_cpxB4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location673 (_cpxB4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location673 (_cpxB4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location673 (_cpxB4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location674 (_cp0FMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location674 (_cp0FMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location674 (_cp0FMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location674 (_cp0FMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location674 (_cp0FMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location674 (_cp0FMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location674 (_cp0FMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location675 (_cp3vkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location675 (_cp3vkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location675 (_cp3vkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location675 (_cp3vkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location675 (_cp3vkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location675 (_cp3vkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location675 (_cp3vkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location676 (_cp6y4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location676 (_cp6y4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location676 (_cp6y4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location676 (_cp6y4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location676 (_cp6y4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location676 (_cp6y4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location676 (_cp6y4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location677 (_cp92McrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location677 (_cp92McrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location677 (_cp92McrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location677 (_cp92McrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location677 (_cp92McrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location677 (_cp92McrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location677 (_cp92McrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location678 (_cqBgkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location678 (_cqBgkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location678 (_cqBgkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location678 (_cqBgkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location678 (_cqBgkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location678 (_cqBgkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location678 (_cqBgkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location679 (_cqEj4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location679 (_cqEj4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location679 (_cqEj4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location679 (_cqEj4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location679 (_cqEj4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location679 (_cqEj4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location679 (_cqEj4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location68 (_cXPHc8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location68 (_cXPHc8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location68 (_cXPHc8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location68 (_cXPHc8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location68 (_cXPHc8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location68 (_cXPHc8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location68 (_cXPHc8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location680 (_cqHnMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location680 (_cqHnMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location680 (_cqHnMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location680 (_cqHnMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location680 (_cqHnMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location680 (_cqHnMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location680 (_cqHnMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location681 (_cqLRkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location681 (_cqLRkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location681 (_cqLRkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location681 (_cqLRkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location681 (_cqLRkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location681 (_cqLRkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location681 (_cqLRkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location682 (_cqO78crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location682 (_cqO78crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location682 (_cqO78crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location682 (_cqO78crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location682 (_cqO78crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location682 (_cqO78crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location682 (_cqO78crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location683 (_cqR_QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location683 (_cqR_QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location683 (_cqR_QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location683 (_cqR_QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location683 (_cqR_QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location683 (_cqR_QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location683 (_cqR_QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location684 (_cqVpocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location684 (_cqVpocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location684 (_cqVpocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location684 (_cqVpocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location684 (_cqVpocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location684 (_cqVpocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location684 (_cqVpocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location685 (_cqYs8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location685 (_cqYs8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location685 (_cqYs8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location685 (_cqYs8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location685 (_cqYs8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location685 (_cqYs8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location685 (_cqYs8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location686 (_cqcXUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location686 (_cqcXUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location686 (_cqcXUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location686 (_cqcXUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location686 (_cqcXUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location686 (_cqcXUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location686 (_cqcXUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location687 (_cqgBscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location687 (_cqgBscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location687 (_cqgBscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location687 (_cqgBscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location687 (_cqgBscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location687 (_cqgBscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location687 (_cqgBscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location688 (_cqjsEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location688 (_cqjsEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location688 (_cqjsEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location688 (_cqjsEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location688 (_cqjsEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location688 (_cqjsEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location688 (_cqjsEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location689 (_cqnWccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location689 (_cqnWccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location689 (_cqnWccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location689 (_cqnWccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location689 (_cqnWccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location689 (_cqnWccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location689 (_cqnWccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location69 (_cXPugcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location69 (_cXPugcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location69 (_cXPugcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location69 (_cXPugcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location69 (_cXPugcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location69 (_cXPugcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location69 (_cXPugcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location690 (_cqrA0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location690 (_cqrA0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location690 (_cqrA0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location690 (_cqrA0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location690 (_cqrA0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location690 (_cqrA0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location690 (_cqrA0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location691 (_cquEIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location691 (_cquEIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location691 (_cquEIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location691 (_cquEIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location691 (_cquEIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location691 (_cquEIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location691 (_cquEIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location692 (_cqxugcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location692 (_cqxugcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location692 (_cqxugcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location692 (_cqxugcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location692 (_cqxugcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location692 (_cqxugcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location692 (_cqxugcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location693 (_cq1Y4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location693 (_cq1Y4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location693 (_cq1Y4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location693 (_cq1Y4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location693 (_cq1Y4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location693 (_cq1Y4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location693 (_cq1Y4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location694 (_cq4cMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location694 (_cq4cMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location694 (_cq4cMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location694 (_cq4cMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location694 (_cq4cMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location694 (_cq4cMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location694 (_cq4cMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location695 (_cq97wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location695 (_cq97wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location695 (_cq97wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location695 (_cq97wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location695 (_cq97wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location695 (_cq97wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location695 (_cq97wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location696 (_crC0QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location696 (_crC0QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location696 (_crC0QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location696 (_crC0QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location696 (_crC0QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location696 (_crC0QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location696 (_crC0QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location697 (_crF3kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location697 (_crF3kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location697 (_crF3kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location697 (_crF3kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location697 (_crF3kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location697 (_crF3kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location697 (_crF3kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location698 (_crJh8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location698 (_crJh8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location698 (_crJh8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location698 (_crJh8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location698 (_crJh8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location698 (_crJh8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location698 (_crJh8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location699 (_crNMUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location699 (_crNMUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location699 (_crNMUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location699 (_crNMUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location699 (_crNMUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location699 (_crNMUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location699 (_crNMUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location7 (_cW37FsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location7 (_cW37FsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location7 (_cW37FsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location7 (_cW37FsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location7 (_cW37FsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location7 (_cW37FsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location7 (_cW37FsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location70 (_cXPuhcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location70 (_cXPuhcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location70 (_cXPuhcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location70 (_cXPuhcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location70 (_cXPuhcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location70 (_cXPuhcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location70 (_cXPuhcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location700 (_crQ2scrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location700 (_crQ2scrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location700 (_crQ2scrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location700 (_crQ2scrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location700 (_crQ2scrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location700 (_crQ2scrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location700 (_crQ2scrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location701 (_crT6AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location701 (_crT6AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location701 (_crT6AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location701 (_crT6AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location701 (_crT6AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location701 (_crT6AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location701 (_crT6AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location702 (_crXkYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location702 (_crXkYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location702 (_crXkYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location702 (_crXkYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location702 (_crXkYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location702 (_crXkYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location702 (_crXkYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location703 (_cranscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location703 (_cranscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location703 (_cranscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location703 (_cranscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location703 (_cranscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location703 (_cranscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location703 (_cranscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location704 (_creSEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location704 (_creSEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location704 (_creSEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location704 (_creSEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location704 (_creSEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location704 (_creSEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location704 (_creSEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location705 (_crhVYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location705 (_crhVYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location705 (_crhVYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location705 (_crhVYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location705 (_crhVYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location705 (_crhVYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location705 (_crhVYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location706 (_crk_wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location706 (_crk_wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location706 (_crk_wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location706 (_crk_wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location706 (_crk_wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location706 (_crk_wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location706 (_crk_wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location707 (_croqIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location707 (_croqIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location707 (_croqIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location707 (_croqIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location707 (_croqIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location707 (_croqIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location707 (_croqIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location708 (_crsUgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location708 (_crsUgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location708 (_crsUgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location708 (_crsUgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location708 (_crsUgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location708 (_crsUgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location708 (_crsUgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location709 (_crvX0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location709 (_crvX0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location709 (_crvX0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location709 (_crvX0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location709 (_crvX0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location709 (_crvX0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location709 (_crvX0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location71 (_cXQVkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location71 (_cXQVkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location71 (_cXQVkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location71 (_cXQVkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location71 (_cXQVkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location71 (_cXQVkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location71 (_cXQVkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location710 (_crzCMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location710 (_crzCMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location710 (_crzCMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location710 (_crzCMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location710 (_crzCMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location710 (_crzCMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location710 (_crzCMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location711 (_cr2skcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location711 (_cr2skcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location711 (_cr2skcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location711 (_cr2skcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location711 (_cr2skcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location711 (_cr2skcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location711 (_cr2skcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location712 (_cr6W8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location712 (_cr6W8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location712 (_cr6W8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location712 (_cr6W8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location712 (_cr6W8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location712 (_cr6W8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location712 (_cr6W8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location713 (_cr9aQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location713 (_cr9aQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location713 (_cr9aQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location713 (_cr9aQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location713 (_cr9aQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location713 (_cr9aQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location713 (_cr9aQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location714 (_csBEocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location714 (_csBEocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location714 (_csBEocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location714 (_csBEocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location714 (_csBEocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location714 (_csBEocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location714 (_csBEocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location715 (_csEvAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location715 (_csEvAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location715 (_csEvAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location715 (_csEvAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location715 (_csEvAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location715 (_csEvAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location715 (_csEvAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location716 (_csIZYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location716 (_csIZYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location716 (_csIZYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location716 (_csIZYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location716 (_csIZYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location716 (_csIZYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location716 (_csIZYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location717 (_csLcscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location717 (_csLcscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location717 (_csLcscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location717 (_csLcscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location717 (_csLcscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location717 (_csLcscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location717 (_csLcscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location718 (_csPHEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location718 (_csPHEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location718 (_csPHEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location718 (_csPHEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location718 (_csPHEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location718 (_csPHEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location718 (_csPHEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location719 (_csSxccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location719 (_csSxccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location719 (_csSxccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location719 (_csSxccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location719 (_csSxccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location719 (_csSxccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location719 (_csSxccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location72 (_cXQ8ocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location72 (_cXQ8ocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location72 (_cXQ8ocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location72 (_cXQ8ocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location72 (_cXQ8ocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location72 (_cXQ8ocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location72 (_cXQ8ocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location720 (_csWb0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location720 (_csWb0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location720 (_csWb0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location720 (_csWb0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location720 (_csWb0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location720 (_csWb0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location720 (_csWb0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location721 (_csaGMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location721 (_csaGMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location721 (_csaGMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location721 (_csaGMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location721 (_csaGMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location721 (_csaGMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location721 (_csaGMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location722 (_csdwkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location722 (_csdwkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location722 (_csdwkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location722 (_csdwkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location722 (_csdwkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location722 (_csdwkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location722 (_csdwkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location723 (_csha8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location723 (_csha8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location723 (_csha8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location723 (_csha8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location723 (_csha8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location723 (_csha8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location723 (_csha8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location724 (_cslsYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location724 (_cslsYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location724 (_cslsYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location724 (_cslsYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location724 (_cslsYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location724 (_cslsYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location724 (_cslsYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location725 (_cspWwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location725 (_cspWwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location725 (_cspWwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location725 (_cspWwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location725 (_cspWwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location725 (_cspWwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location725 (_cspWwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location726 (_cstBIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location726 (_cstBIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location726 (_cstBIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location726 (_cstBIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location726 (_cstBIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location726 (_cstBIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location726 (_cstBIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location727 (_cswrgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location727 (_cswrgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location727 (_cswrgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location727 (_cswrgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location727 (_cswrgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location727 (_cswrgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location727 (_cswrgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location728 (_cs0V4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location728 (_cs0V4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location728 (_cs0V4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location728 (_cs0V4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location728 (_cs0V4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location728 (_cs0V4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location728 (_cs0V4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location729 (_cs3ZMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location729 (_cs3ZMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location729 (_cs3ZMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location729 (_cs3ZMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location729 (_cs3ZMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location729 (_cs3ZMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location729 (_cs3ZMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location73 (_cXQ8pcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location73 (_cXQ8pcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location73 (_cXQ8pcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location73 (_cXQ8pcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location73 (_cXQ8pcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location73 (_cXQ8pcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location73 (_cXQ8pcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location730 (_cs8RscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location730 (_cs8RscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location730 (_cs8RscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location730 (_cs8RscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location730 (_cs8RscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location730 (_cs8RscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location730 (_cs8RscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location731 (_cs_8EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location731 (_cs_8EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location731 (_cs_8EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location731 (_cs_8EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location731 (_cs_8EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location731 (_cs_8EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location731 (_cs_8EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location732 (_ctENgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location732 (_ctENgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location732 (_ctENgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location732 (_ctENgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location732 (_ctENgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location732 (_ctENgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location732 (_ctENgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location733 (_ctH34crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location733 (_ctH34crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location733 (_ctH34crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location733 (_ctH34crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location733 (_ctH34crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location733 (_ctH34crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location733 (_ctH34crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location734 (_ctMJUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location734 (_ctMJUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location734 (_ctMJUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location734 (_ctMJUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location734 (_ctMJUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location734 (_ctMJUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location734 (_ctMJUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location735 (_ctQawcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location735 (_ctQawcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location735 (_ctQawcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location735 (_ctQawcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location735 (_ctQawcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location735 (_ctQawcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location735 (_ctQawcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location736 (_ctUsMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location736 (_ctUsMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location736 (_ctUsMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location736 (_ctUsMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location736 (_ctUsMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location736 (_ctUsMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location736 (_ctUsMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location737 (_ctY9ocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location737 (_ctY9ocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location737 (_ctY9ocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location737 (_ctY9ocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location737 (_ctY9ocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location737 (_ctY9ocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location737 (_ctY9ocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location738 (_ctcoAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location738 (_ctcoAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location738 (_ctcoAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location738 (_ctcoAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location738 (_ctcoAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location738 (_ctcoAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location738 (_ctcoAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location739 (_ctg5ccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location739 (_ctg5ccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location739 (_ctg5ccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location739 (_ctg5ccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location739 (_ctg5ccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location739 (_ctg5ccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location739 (_ctg5ccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location74 (_cXRjs8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location74 (_cXRjs8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location74 (_cXRjs8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location74 (_cXRjs8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location74 (_cXRjs8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location74 (_cXRjs8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location74 (_cXRjs8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location740 (_ctlK4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location740 (_ctlK4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location740 (_ctlK4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location740 (_ctlK4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location740 (_ctlK4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location740 (_ctlK4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location740 (_ctlK4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location741 (_cto1QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location741 (_cto1QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location741 (_cto1QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location741 (_cto1QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location741 (_cto1QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location741 (_cto1QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location741 (_cto1QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location742 (_cttGscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location742 (_cttGscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location742 (_cttGscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location742 (_cttGscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location742 (_cttGscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location742 (_cttGscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location742 (_cttGscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location743 (_ctwxEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location743 (_ctwxEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location743 (_ctwxEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location743 (_ctwxEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location743 (_ctwxEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location743 (_ctwxEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location743 (_ctwxEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location744 (_ct1CgMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location744 (_ct1CgMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location744 (_ct1CgMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location744 (_ct1CgMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location744 (_ct1CgMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location744 (_ct1CgMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location744 (_ct1CgMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location745 (_ct4s4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location745 (_ct4s4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location745 (_ct4s4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location745 (_ct4s4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location745 (_ct4s4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location745 (_ct4s4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location745 (_ct4s4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location746 (_ct8XQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location746 (_ct8XQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location746 (_ct8XQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location746 (_ct8XQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location746 (_ct8XQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location746 (_ct8XQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location746 (_ct8XQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location747 (_cuBPwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location747 (_cuBPwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location747 (_cuBPwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location747 (_cuBPwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location747 (_cuBPwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location747 (_cuBPwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location747 (_cuBPwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location748 (_cuGIQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location748 (_cuGIQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location748 (_cuGIQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location748 (_cuGIQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location748 (_cuGIQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location748 (_cuGIQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location748 (_cuGIQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location749 (_cuJyocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location749 (_cuJyocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location749 (_cuJyocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location749 (_cuJyocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location749 (_cuJyocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location749 (_cuJyocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location749 (_cuJyocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location75 (_cXSKwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location75 (_cXSKwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location75 (_cXSKwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location75 (_cXSKwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location75 (_cXSKwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location75 (_cXSKwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location75 (_cXSKwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location750 (_cuOEEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location750 (_cuOEEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location750 (_cuOEEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location750 (_cuOEEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location750 (_cuOEEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location750 (_cuOEEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location750 (_cuOEEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location751 (_cuRuccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location751 (_cuRuccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location751 (_cuRuccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location751 (_cuRuccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location751 (_cuRuccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location751 (_cuRuccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location751 (_cuRuccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location752 (_cuV_4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location752 (_cuV_4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location752 (_cuV_4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location752 (_cuV_4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location752 (_cuV_4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location752 (_cuV_4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location752 (_cuV_4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location753 (_cuZqQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location753 (_cuZqQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location753 (_cuZqQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location753 (_cuZqQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location753 (_cuZqQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location753 (_cuZqQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location753 (_cuZqQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location754 (_cueiwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location754 (_cueiwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location754 (_cueiwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location754 (_cueiwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location754 (_cueiwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location754 (_cueiwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location754 (_cueiwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location755 (_cukCUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location755 (_cukCUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location755 (_cukCUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location755 (_cukCUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location755 (_cukCUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location755 (_cukCUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location755 (_cukCUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location756 (_cuoTwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location756 (_cuoTwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location756 (_cuoTwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location756 (_cuoTwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location756 (_cuoTwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location756 (_cuoTwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location756 (_cuoTwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location757 (_cur-IcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location757 (_cur-IcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location757 (_cur-IcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location757 (_cur-IcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location757 (_cur-IcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location757 (_cur-IcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location757 (_cur-IcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location758 (_cuwPkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location758 (_cuwPkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location758 (_cuwPkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location758 (_cuwPkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location758 (_cuwPkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location758 (_cuwPkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location758 (_cuwPkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location759 (_cu0hAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location759 (_cu0hAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location759 (_cu0hAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location759 (_cu0hAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location759 (_cu0hAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location759 (_cu0hAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location759 (_cu0hAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location76 (_cXSKxcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location76 (_cXSKxcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location76 (_cXSKxcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location76 (_cXSKxcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location76 (_cXSKxcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location76 (_cXSKxcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location76 (_cXSKxcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location760 (_cu4yccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location760 (_cu4yccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location760 (_cu4yccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location760 (_cu4yccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location760 (_cu4yccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location760 (_cu4yccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location760 (_cu4yccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location761 (_cu8c0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location761 (_cu8c0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location761 (_cu8c0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location761 (_cu8c0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location761 (_cu8c0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location761 (_cu8c0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location761 (_cu8c0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location762 (_cvBVUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location762 (_cvBVUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location762 (_cvBVUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location762 (_cvBVUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location762 (_cvBVUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location762 (_cvBVUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location762 (_cvBVUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location763 (_cvE_scrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location763 (_cvE_scrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location763 (_cvE_scrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location763 (_cvE_scrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location763 (_cvE_scrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location763 (_cvE_scrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location763 (_cvE_scrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location764 (_cvJRIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location764 (_cvJRIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location764 (_cvJRIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location764 (_cvJRIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location764 (_cvJRIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location764 (_cvJRIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location764 (_cvJRIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location765 (_cvM7gcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location765 (_cvM7gcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location765 (_cvM7gcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location765 (_cvM7gcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location765 (_cvM7gcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location765 (_cvM7gcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location765 (_cvM7gcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location766 (_cvRM8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location766 (_cvRM8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location766 (_cvRM8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location766 (_cvRM8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location766 (_cvRM8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location766 (_cvRM8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location766 (_cvRM8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location767 (_cvVeYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location767 (_cvVeYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location767 (_cvVeYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location767 (_cvVeYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location767 (_cvVeYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location767 (_cvVeYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location767 (_cvVeYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location768 (_cvZv0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location768 (_cvZv0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location768 (_cvZv0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location768 (_cvZv0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location768 (_cvZv0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location768 (_cvZv0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location768 (_cvZv0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location769 (_cveBQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location769 (_cveBQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location769 (_cveBQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location769 (_cveBQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location769 (_cveBQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location769 (_cveBQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location769 (_cveBQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location77 (_cXSx08rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location77 (_cXSx08rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location77 (_cXSx08rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location77 (_cXSx08rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location77 (_cXSx08rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location77 (_cXSx08rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location77 (_cXSx08rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location770 (_cviSscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location770 (_cviSscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location770 (_cviSscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location770 (_cviSscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location770 (_cviSscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location770 (_cviSscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location770 (_cviSscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location771 (_cvnLMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location771 (_cvnLMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location771 (_cvnLMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location771 (_cvnLMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location771 (_cvnLMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location771 (_cvnLMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location771 (_cvnLMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location772 (_cvrcocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location772 (_cvrcocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location772 (_cvrcocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location772 (_cvrcocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location772 (_cvrcocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location772 (_cvrcocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location772 (_cvrcocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location773 (_cvwVIMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location773 (_cvwVIMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location773 (_cvwVIMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location773 (_cvwVIMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location773 (_cvwVIMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location773 (_cvwVIMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location773 (_cvwVIMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location774 (_cv0mkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location774 (_cv0mkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location774 (_cv0mkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location774 (_cv0mkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location774 (_cv0mkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location774 (_cv0mkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location774 (_cv0mkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location775 (_cv44AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location775 (_cv44AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location775 (_cv44AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location775 (_cv44AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location775 (_cv44AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location775 (_cv44AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location775 (_cv44AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location776 (_cv9wgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location776 (_cv9wgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location776 (_cv9wgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location776 (_cv9wgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location776 (_cv9wgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location776 (_cv9wgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location776 (_cv9wgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location777 (_cwCB8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location777 (_cwCB8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location777 (_cwCB8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location777 (_cwCB8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location777 (_cwCB8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location777 (_cwCB8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location777 (_cwCB8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location778 (_cwGTYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location778 (_cwGTYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location778 (_cwGTYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location778 (_cwGTYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location778 (_cwGTYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location778 (_cwGTYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location778 (_cwGTYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location779 (_cwLL4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location779 (_cwLL4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location779 (_cwLL4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location779 (_cwLL4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location779 (_cwLL4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location779 (_cwLL4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location779 (_cwLL4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location78 (_cXTY4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location78 (_cXTY4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location78 (_cXTY4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location78 (_cXTY4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location78 (_cXTY4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location78 (_cXTY4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location78 (_cXTY4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location780 (_cwQEYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location780 (_cwQEYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location780 (_cwQEYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location780 (_cwQEYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location780 (_cwQEYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location780 (_cwQEYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location780 (_cwQEYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location781 (_cwVj8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location781 (_cwVj8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location781 (_cwVj8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location781 (_cwVj8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location781 (_cwVj8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location781 (_cwVj8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location781 (_cwVj8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location782 (_cwacccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location782 (_cwacccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location782 (_cwacccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location782 (_cwacccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location782 (_cwacccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location782 (_cwacccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location782 (_cwacccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location783 (_cwgjEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location783 (_cwgjEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location783 (_cwgjEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location783 (_cwgjEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location783 (_cwgjEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location783 (_cwgjEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location783 (_cwgjEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location784 (_cwnQwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location784 (_cwnQwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location784 (_cwnQwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location784 (_cwnQwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location784 (_cwnQwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location784 (_cwnQwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location784 (_cwnQwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location785 (_cwswUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location785 (_cwswUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location785 (_cwswUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location785 (_cwswUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location785 (_cwswUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location785 (_cwswUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location785 (_cwswUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location786 (_cw0sIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location786 (_cw0sIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location786 (_cw0sIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location786 (_cw0sIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location786 (_cw0sIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location786 (_cw0sIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location786 (_cw0sIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location787 (_cw6ywcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location787 (_cw6ywcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location787 (_cw6ywcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location787 (_cw6ywcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location787 (_cw6ywcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location787 (_cw6ywcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location787 (_cw6ywcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location788 (_cw_EMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location788 (_cw_EMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location788 (_cw_EMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location788 (_cw_EMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location788 (_cw_EMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location788 (_cw_EMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location788 (_cw_EMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location789 (_cxFK0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location789 (_cxFK0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location789 (_cxFK0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location789 (_cxFK0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location789 (_cxFK0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location789 (_cxFK0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location789 (_cxFK0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location79 (_cXT_8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location79 (_cXT_8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location79 (_cXT_8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location79 (_cXT_8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location79 (_cXT_8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location79 (_cXT_8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location79 (_cXT_8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location790 (_cxNGocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location790 (_cxNGocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location790 (_cxNGocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location790 (_cxNGocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location790 (_cxNGocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location790 (_cxNGocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location790 (_cxNGocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location791 (_cxT0UcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location791 (_cxT0UcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location791 (_cxT0UcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location791 (_cxT0UcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location791 (_cxT0UcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location791 (_cxT0UcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location791 (_cxT0UcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location792 (_cxaiAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location792 (_cxaiAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location792 (_cxaiAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location792 (_cxaiAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location792 (_cxaiAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location792 (_cxaiAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location792 (_cxaiAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location793 (_cxhPsMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location793 (_cxhPsMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location793 (_cxhPsMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location793 (_cxhPsMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location793 (_cxhPsMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location793 (_cxhPsMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location793 (_cxhPsMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location794 (_cxnWUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location794 (_cxnWUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location794 (_cxnWUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location794 (_cxnWUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location794 (_cxnWUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location794 (_cxnWUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location794 (_cxnWUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location795 (_cxuEAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location795 (_cxuEAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location795 (_cxuEAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location795 (_cxuEAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location795 (_cxuEAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location795 (_cxuEAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location795 (_cxuEAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location796 (_cx0KocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location796 (_cx0KocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location796 (_cx0KocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location796 (_cx0KocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location796 (_cx0KocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location796 (_cx0KocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location796 (_cx0KocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location797 (_cx64UcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location797 (_cx64UcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location797 (_cx64UcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location797 (_cx64UcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location797 (_cx64UcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location797 (_cx64UcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location797 (_cx64UcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location798 (_cyBmAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location798 (_cyBmAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location798 (_cyBmAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location798 (_cyBmAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location798 (_cyBmAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location798 (_cyBmAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location798 (_cyBmAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location799 (_cyHsocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location799 (_cyHsocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location799 (_cyHsocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location799 (_cyHsocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location799 (_cyHsocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location799 (_cyHsocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location799 (_cyHsocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location8 (_cW37GsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location8 (_cW37GsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location8 (_cW37GsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location8 (_cW37GsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location8 (_cW37GsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location8 (_cW37GsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location8 (_cW37GsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location80 (_cXUnAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location80 (_cXUnAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location80 (_cXUnAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location80 (_cXUnAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location80 (_cXUnAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location80 (_cXUnAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location80 (_cXUnAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location800 (_cyOaUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location800 (_cyOaUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location800 (_cyOaUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location800 (_cyOaUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location800 (_cyOaUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location800 (_cyOaUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location800 (_cyOaUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location801 (_cyVIAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location801 (_cyVIAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location801 (_cyVIAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location801 (_cyVIAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location801 (_cyVIAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location801 (_cyVIAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location801 (_cyVIAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location802 (_cybOocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location802 (_cybOocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location802 (_cybOocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location802 (_cybOocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location802 (_cybOocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location802 (_cybOocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location802 (_cybOocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location803 (_cyh8UcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location803 (_cyh8UcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location803 (_cyh8UcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location803 (_cyh8UcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location803 (_cyh8UcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location803 (_cyh8UcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location803 (_cyh8UcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location804 (_cytigcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location804 (_cytigcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location804 (_cytigcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location804 (_cytigcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location804 (_cytigcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location804 (_cytigcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location804 (_cytigcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location805 (_cyybAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location805 (_cyybAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location805 (_cyybAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location805 (_cyybAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location805 (_cyybAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location805 (_cyybAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location805 (_cyybAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location806 (_cy2sccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location806 (_cy2sccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location806 (_cy2sccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location806 (_cy2sccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location806 (_cy2sccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location806 (_cy2sccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location806 (_cy2sccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location807 (_cy694crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location807 (_cy694crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location807 (_cy694crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location807 (_cy694crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location807 (_cy694crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location807 (_cy694crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location807 (_cy694crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location808 (_cy-oQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location808 (_cy-oQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location808 (_cy-oQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location808 (_cy-oQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location808 (_cy-oQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location808 (_cy-oQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location808 (_cy-oQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location809 (_czCSocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location809 (_czCSocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location809 (_czCSocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location809 (_czCSocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location809 (_czCSocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location809 (_czCSocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location809 (_czCSocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location81 (_cXVOEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location81 (_cXVOEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location81 (_cXVOEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location81 (_cXVOEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location81 (_cXVOEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location81 (_cXVOEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location81 (_cXVOEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location810 (_czGkEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location810 (_czGkEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location810 (_czGkEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location810 (_czGkEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location810 (_czGkEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location810 (_czGkEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location810 (_czGkEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location811 (_czKOccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location811 (_czKOccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location811 (_czKOccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location811 (_czKOccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location811 (_czKOccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location811 (_czKOccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location811 (_czKOccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location812 (_czN40crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location812 (_czN40crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location812 (_czN40crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location812 (_czN40crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location812 (_czN40crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location812 (_czN40crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location812 (_czN40crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location813 (_czSKQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location813 (_czSKQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location813 (_czSKQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location813 (_czSKQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location813 (_czSKQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location813 (_czSKQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location813 (_czSKQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location814 (_czV0ocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location814 (_czV0ocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location814 (_czV0ocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location814 (_czV0ocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location814 (_czV0ocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location814 (_czV0ocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location814 (_czV0ocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location815 (_czZfAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location815 (_czZfAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location815 (_czZfAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location815 (_czZfAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location815 (_czZfAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location815 (_czZfAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location815 (_czZfAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location816 (_czdJYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location816 (_czdJYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location816 (_czdJYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location816 (_czdJYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location816 (_czdJYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location816 (_czdJYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location816 (_czdJYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location817 (_czgzwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location817 (_czgzwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location817 (_czgzwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location817 (_czgzwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location817 (_czgzwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location817 (_czgzwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location817 (_czgzwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location818 (_czlFMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location818 (_czlFMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location818 (_czlFMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location818 (_czlFMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location818 (_czlFMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location818 (_czlFMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location818 (_czlFMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location819 (_czovkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location819 (_czovkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location819 (_czovkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location819 (_czovkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location819 (_czovkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location819 (_czovkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location819 (_czovkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location82 (_cXVOFcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location82 (_cXVOFcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location82 (_cXVOFcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location82 (_cXVOFcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location82 (_cXVOFcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location82 (_cXVOFcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location82 (_cXVOFcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location820 (_czsZ8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location820 (_czsZ8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location820 (_czsZ8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location820 (_czsZ8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location820 (_czsZ8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location820 (_czsZ8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location820 (_czsZ8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location821 (_czwEUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location821 (_czwEUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location821 (_czwEUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location821 (_czwEUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location821 (_czwEUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location821 (_czwEUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location821 (_czwEUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location822 (_czzuscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location822 (_czzuscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location822 (_czzuscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location822 (_czzuscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location822 (_czzuscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location822 (_czzuscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location822 (_czzuscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location823 (_cz4AIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location823 (_cz4AIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location823 (_cz4AIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location823 (_cz4AIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location823 (_cz4AIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location823 (_cz4AIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location823 (_cz4AIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location824 (_cz7qgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location824 (_cz7qgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location824 (_cz7qgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location824 (_cz7qgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location824 (_cz7qgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location824 (_cz7qgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location824 (_cz7qgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location825 (_cz_U4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location825 (_cz_U4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location825 (_cz_U4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location825 (_cz_U4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location825 (_cz_U4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location825 (_cz_U4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location825 (_cz_U4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location826 (_c0DmUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location826 (_c0DmUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location826 (_c0DmUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location826 (_c0DmUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location826 (_c0DmUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location826 (_c0DmUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location826 (_c0DmUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location827 (_c0HQscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location827 (_c0HQscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location827 (_c0HQscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location827 (_c0HQscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location827 (_c0HQscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location827 (_c0HQscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location827 (_c0HQscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location828 (_c0K7EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location828 (_c0K7EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location828 (_c0K7EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location828 (_c0K7EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location828 (_c0K7EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location828 (_c0K7EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location828 (_c0K7EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location829 (_c0PMgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location829 (_c0PMgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location829 (_c0PMgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location829 (_c0PMgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location829 (_c0PMgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location829 (_c0PMgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location829 (_c0PMgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location83 (_cXV1I8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location83 (_cXV1I8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location83 (_cXV1I8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location83 (_cXV1I8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location83 (_cXV1I8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location83 (_cXV1I8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location83 (_cXV1I8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location830 (_c0S24crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location830 (_c0S24crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location830 (_c0S24crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location830 (_c0S24crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location830 (_c0S24crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location830 (_c0S24crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location830 (_c0S24crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location831 (_c0WhQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location831 (_c0WhQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location831 (_c0WhQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location831 (_c0WhQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location831 (_c0WhQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location831 (_c0WhQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location831 (_c0WhQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location832 (_c0ayscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location832 (_c0ayscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location832 (_c0ayscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location832 (_c0ayscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location832 (_c0ayscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location832 (_c0ayscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location832 (_c0ayscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location833 (_c0fEIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location833 (_c0fEIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location833 (_c0fEIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location833 (_c0fEIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location833 (_c0fEIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location833 (_c0fEIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location833 (_c0fEIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location834 (_c0jVkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location834 (_c0jVkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location834 (_c0jVkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location834 (_c0jVkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location834 (_c0jVkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location834 (_c0jVkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location834 (_c0jVkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location835 (_c0oOEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location835 (_c0oOEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location835 (_c0oOEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location835 (_c0oOEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location835 (_c0oOEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location835 (_c0oOEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location835 (_c0oOEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location836 (_c0sfgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location836 (_c0sfgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location836 (_c0sfgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location836 (_c0sfgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location836 (_c0sfgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location836 (_c0sfgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location836 (_c0sfgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location837 (_c0wJ4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location837 (_c0wJ4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location837 (_c0wJ4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location837 (_c0wJ4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location837 (_c0wJ4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location837 (_c0wJ4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location837 (_c0wJ4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location838 (_c0z0QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location838 (_c0z0QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location838 (_c0z0QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location838 (_c0z0QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location838 (_c0z0QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location838 (_c0z0QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location838 (_c0z0QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location839 (_c04swcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location839 (_c04swcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location839 (_c04swcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location839 (_c04swcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location839 (_c04swcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location839 (_c04swcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location839 (_c04swcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location84 (_cXWcMsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location84 (_cXWcMsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location84 (_cXWcMsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location84 (_cXWcMsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location84 (_cXWcMsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location84 (_cXWcMsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location84 (_cXWcMsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location840 (_c08XIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location840 (_c08XIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location840 (_c08XIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location840 (_c08XIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location840 (_c08XIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location840 (_c08XIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location840 (_c08XIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location841 (_c1AokcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location841 (_c1AokcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location841 (_c1AokcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location841 (_c1AokcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location841 (_c1AokcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location841 (_c1AokcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location841 (_c1AokcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location842 (_c1E6AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location842 (_c1E6AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location842 (_c1E6AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location842 (_c1E6AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location842 (_c1E6AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location842 (_c1E6AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location842 (_c1E6AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location843 (_c1IkYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location843 (_c1IkYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location843 (_c1IkYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location843 (_c1IkYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location843 (_c1IkYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location843 (_c1IkYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location843 (_c1IkYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location844 (_c1M10crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location844 (_c1M10crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location844 (_c1M10crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location844 (_c1M10crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location844 (_c1M10crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location844 (_c1M10crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location844 (_c1M10crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location845 (_c1QgMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location845 (_c1QgMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location845 (_c1QgMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location845 (_c1QgMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location845 (_c1QgMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location845 (_c1QgMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location845 (_c1QgMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location846 (_c1VYscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location846 (_c1VYscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location846 (_c1VYscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location846 (_c1VYscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location846 (_c1VYscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location846 (_c1VYscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location846 (_c1VYscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location847 (_c1ZqIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location847 (_c1ZqIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location847 (_c1ZqIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location847 (_c1ZqIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location847 (_c1ZqIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location847 (_c1ZqIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location847 (_c1ZqIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location848 (_c1dUgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location848 (_c1dUgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location848 (_c1dUgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location848 (_c1dUgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location848 (_c1dUgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location848 (_c1dUgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location848 (_c1dUgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location849 (_c1hl8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location849 (_c1hl8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location849 (_c1hl8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location849 (_c1hl8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location849 (_c1hl8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location849 (_c1hl8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location849 (_c1hl8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location85 (_cXWcNsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location85 (_cXWcNsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location85 (_cXWcNsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location85 (_cXWcNsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location85 (_cXWcNsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location85 (_cXWcNsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location85 (_cXWcNsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location850 (_c1lQUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location850 (_c1lQUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location850 (_c1lQUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location850 (_c1lQUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location850 (_c1lQUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location850 (_c1lQUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location850 (_c1lQUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location851 (_c1o6scrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location851 (_c1o6scrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location851 (_c1o6scrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location851 (_c1o6scrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location851 (_c1o6scrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location851 (_c1o6scrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location851 (_c1o6scrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location852 (_c1tMIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location852 (_c1tMIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location852 (_c1tMIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location852 (_c1tMIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location852 (_c1tMIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location852 (_c1tMIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location852 (_c1tMIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location853 (_c1w2gcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location853 (_c1w2gcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location853 (_c1w2gcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location853 (_c1w2gcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location853 (_c1w2gcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location853 (_c1w2gcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location853 (_c1w2gcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location854 (_c11H8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location854 (_c11H8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location854 (_c11H8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location854 (_c11H8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location854 (_c11H8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location854 (_c11H8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location854 (_c11H8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location855 (_c14yUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location855 (_c14yUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location855 (_c14yUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location855 (_c14yUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location855 (_c14yUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location855 (_c14yUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location855 (_c14yUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location856 (_c19DwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location856 (_c19DwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location856 (_c19DwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location856 (_c19DwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location856 (_c19DwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location856 (_c19DwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location856 (_c19DwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location857 (_c2BVMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location857 (_c2BVMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location857 (_c2BVMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location857 (_c2BVMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location857 (_c2BVMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location857 (_c2BVMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location857 (_c2BVMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location858 (_c2E_kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location858 (_c2E_kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location858 (_c2E_kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location858 (_c2E_kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location858 (_c2E_kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location858 (_c2E_kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location858 (_c2E_kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location859 (_c2J4EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location859 (_c2J4EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location859 (_c2J4EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location859 (_c2J4EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location859 (_c2J4EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location859 (_c2J4EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location859 (_c2J4EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location86 (_cXXDQ8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location86 (_cXXDQ8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location86 (_cXXDQ8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location86 (_cXXDQ8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location86 (_cXXDQ8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location86 (_cXXDQ8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location86 (_cXXDQ8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location860 (_c2NiccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location860 (_c2NiccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location860 (_c2NiccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location860 (_c2NiccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location860 (_c2NiccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location860 (_c2NiccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location860 (_c2NiccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location861 (_c2Rz4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location861 (_c2Rz4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location861 (_c2Rz4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location861 (_c2Rz4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location861 (_c2Rz4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location861 (_c2Rz4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location861 (_c2Rz4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location862 (_c2WFUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location862 (_c2WFUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location862 (_c2WFUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location862 (_c2WFUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location862 (_c2WFUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location862 (_c2WFUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location862 (_c2WFUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location863 (_c2ZvscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location863 (_c2ZvscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location863 (_c2ZvscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location863 (_c2ZvscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location863 (_c2ZvscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location863 (_c2ZvscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location863 (_c2ZvscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location864 (_c2eBIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location864 (_c2eBIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location864 (_c2eBIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location864 (_c2eBIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location864 (_c2eBIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location864 (_c2eBIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location864 (_c2eBIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location865 (_c2hEccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location865 (_c2hEccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location865 (_c2hEccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location865 (_c2hEccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location865 (_c2hEccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location865 (_c2hEccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location865 (_c2hEccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location866 (_c2l88crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location866 (_c2l88crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location866 (_c2l88crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location866 (_c2l88crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location866 (_c2l88crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location866 (_c2l88crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location866 (_c2l88crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location867 (_c2qOYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location867 (_c2qOYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location867 (_c2qOYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location867 (_c2qOYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location867 (_c2qOYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location867 (_c2qOYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location867 (_c2qOYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location868 (_c2uf0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location868 (_c2uf0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location868 (_c2uf0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location868 (_c2uf0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location868 (_c2uf0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location868 (_c2uf0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location868 (_c2uf0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location869 (_c2yKMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location869 (_c2yKMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location869 (_c2yKMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location869 (_c2yKMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location869 (_c2yKMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location869 (_c2yKMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location869 (_c2yKMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location87 (_cXXqUsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location87 (_cXXqUsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location87 (_cXXqUsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location87 (_cXXqUsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location87 (_cXXqUsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location87 (_cXXqUsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location87 (_cXXqUsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location870 (_c210kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location870 (_c210kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location870 (_c210kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location870 (_c210kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location870 (_c210kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location870 (_c210kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location870 (_c210kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location871 (_c25e8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location871 (_c25e8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location871 (_c25e8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location871 (_c25e8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location871 (_c25e8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location871 (_c25e8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location871 (_c25e8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location872 (_c29JUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location872 (_c29JUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location872 (_c29JUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location872 (_c29JUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location872 (_c29JUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location872 (_c29JUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location872 (_c29JUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location873 (_c3AzscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location873 (_c3AzscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location873 (_c3AzscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location873 (_c3AzscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location873 (_c3AzscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location873 (_c3AzscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location873 (_c3AzscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location874 (_c3FFIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location874 (_c3FFIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location874 (_c3FFIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location874 (_c3FFIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location874 (_c3FFIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location874 (_c3FFIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location874 (_c3FFIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location875 (_c3IvgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location875 (_c3IvgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location875 (_c3IvgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location875 (_c3IvgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location875 (_c3IvgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location875 (_c3IvgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location875 (_c3IvgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location876 (_c3NA8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location876 (_c3NA8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location876 (_c3NA8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location876 (_c3NA8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location876 (_c3NA8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location876 (_c3NA8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location876 (_c3NA8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location877 (_c3RSYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location877 (_c3RSYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location877 (_c3RSYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location877 (_c3RSYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location877 (_c3RSYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location877 (_c3RSYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location877 (_c3RSYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location878 (_c3U8wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location878 (_c3U8wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location878 (_c3U8wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location878 (_c3U8wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location878 (_c3U8wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location878 (_c3U8wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location878 (_c3U8wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location879 (_c3ZOMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location879 (_c3ZOMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location879 (_c3ZOMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location879 (_c3ZOMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location879 (_c3ZOMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location879 (_c3ZOMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location879 (_c3ZOMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location88 (_cXYRYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location88 (_cXYRYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location88 (_cXYRYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location88 (_cXYRYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location88 (_cXYRYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location88 (_cXYRYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location88 (_cXYRYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location880 (_c3c4kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location880 (_c3c4kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location880 (_c3c4kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location880 (_c3c4kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location880 (_c3c4kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location880 (_c3c4kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location880 (_c3c4kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location881 (_c3gi8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location881 (_c3gi8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location881 (_c3gi8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location881 (_c3gi8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location881 (_c3gi8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location881 (_c3gi8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location881 (_c3gi8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location882 (_c3kNUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location882 (_c3kNUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location882 (_c3kNUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location882 (_c3kNUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location882 (_c3kNUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location882 (_c3kNUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location882 (_c3kNUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location883 (_c3pF0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location883 (_c3pF0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location883 (_c3pF0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location883 (_c3pF0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location883 (_c3pF0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location883 (_c3pF0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location883 (_c3pF0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location884 (_c3swMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location884 (_c3swMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location884 (_c3swMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location884 (_c3swMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location884 (_c3swMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location884 (_c3swMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location884 (_c3swMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location885 (_c3xBocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location885 (_c3xBocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location885 (_c3xBocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location885 (_c3xBocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location885 (_c3xBocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location885 (_c3xBocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location885 (_c3xBocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location886 (_c30sAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location886 (_c30sAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location886 (_c30sAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location886 (_c30sAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location886 (_c30sAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location886 (_c30sAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location886 (_c30sAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location887 (_c34WYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location887 (_c34WYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location887 (_c34WYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location887 (_c34WYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location887 (_c34WYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location887 (_c34WYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location887 (_c34WYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location888 (_c38AwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location888 (_c38AwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location888 (_c38AwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location888 (_c38AwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location888 (_c38AwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location888 (_c38AwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location888 (_c38AwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location889 (_c4ASMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location889 (_c4ASMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location889 (_c4ASMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location889 (_c4ASMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location889 (_c4ASMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location889 (_c4ASMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location889 (_c4ASMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location89 (_cXYRZcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location89 (_cXYRZcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location89 (_cXYRZcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location89 (_cXYRZcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location89 (_cXYRZcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location89 (_cXYRZcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location89 (_cXYRZcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location890 (_c4FKscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location890 (_c4FKscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location890 (_c4FKscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location890 (_c4FKscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location890 (_c4FKscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location890 (_c4FKscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location890 (_c4FKscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location891 (_c4I1EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location891 (_c4I1EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location891 (_c4I1EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location891 (_c4I1EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location891 (_c4I1EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location891 (_c4I1EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location891 (_c4I1EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location892 (_c4MfccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location892 (_c4MfccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location892 (_c4MfccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location892 (_c4MfccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location892 (_c4MfccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location892 (_c4MfccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location892 (_c4MfccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location893 (_c4Qw4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location893 (_c4Qw4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location893 (_c4Qw4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location893 (_c4Qw4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location893 (_c4Qw4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location893 (_c4Qw4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location893 (_c4Qw4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location894 (_c4UbQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location894 (_c4UbQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location894 (_c4UbQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location894 (_c4UbQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location894 (_c4UbQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location894 (_c4UbQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location894 (_c4UbQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location895 (_c4YFocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location895 (_c4YFocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location895 (_c4YFocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location895 (_c4YFocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location895 (_c4YFocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location895 (_c4YFocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location895 (_c4YFocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location896 (_c4bwAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location896 (_c4bwAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location896 (_c4bwAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location896 (_c4bwAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location896 (_c4bwAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location896 (_c4bwAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location896 (_c4bwAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location897 (_c4gBccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location897 (_c4gBccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location897 (_c4gBccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location897 (_c4gBccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location897 (_c4gBccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location897 (_c4gBccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location897 (_c4gBccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location898 (_c4jr0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location898 (_c4jr0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location898 (_c4jr0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location898 (_c4jr0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location898 (_c4jr0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location898 (_c4jr0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location898 (_c4jr0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location899 (_c4n9QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location899 (_c4n9QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location899 (_c4n9QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location899 (_c4n9QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location899 (_c4n9QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location899 (_c4n9QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location899 (_c4n9QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location9 (_cW37HsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location9 (_cW37HsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location9 (_cW37HsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location9 (_cW37HsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location9 (_cW37HsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location9 (_cW37HsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location9 (_cW37HsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location90 (_cXY4c8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location90 (_cXY4c8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location90 (_cXY4c8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location90 (_cXY4c8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location90 (_cXY4c8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location90 (_cXY4c8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location90 (_cXY4c8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location900 (_c4sOscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location900 (_c4sOscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location900 (_c4sOscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location900 (_c4sOscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location900 (_c4sOscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location900 (_c4sOscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location900 (_c4sOscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location901 (_c4v5EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location901 (_c4v5EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location901 (_c4v5EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location901 (_c4v5EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location901 (_c4v5EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location901 (_c4v5EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location901 (_c4v5EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location902 (_c40KgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location902 (_c40KgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location902 (_c40KgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location902 (_c40KgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location902 (_c40KgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location902 (_c40KgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location902 (_c40KgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location903 (_c4304crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location903 (_c4304crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location903 (_c4304crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location903 (_c4304crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location903 (_c4304crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location903 (_c4304crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location903 (_c4304crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location904 (_c47fQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location904 (_c47fQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location904 (_c47fQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location904 (_c47fQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location904 (_c47fQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location904 (_c47fQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location904 (_c47fQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location905 (_c4_wscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location905 (_c4_wscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location905 (_c4_wscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location905 (_c4_wscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location905 (_c4_wscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location905 (_c4_wscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location905 (_c4_wscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location906 (_c5DbEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location906 (_c5DbEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location906 (_c5DbEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location906 (_c5DbEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location906 (_c5DbEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location906 (_c5DbEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location906 (_c5DbEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location907 (_c5HsgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location907 (_c5HsgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location907 (_c5HsgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location907 (_c5HsgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location907 (_c5HsgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location907 (_c5HsgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location907 (_c5HsgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location908 (_c5LW4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location908 (_c5LW4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location908 (_c5LW4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location908 (_c5LW4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location908 (_c5LW4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location908 (_c5LW4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location908 (_c5LW4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location909 (_c5PBQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location909 (_c5PBQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location909 (_c5PBQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location909 (_c5PBQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location909 (_c5PBQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location909 (_c5PBQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location909 (_c5PBQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location91 (_cXZfgsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location91 (_cXZfgsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location91 (_cXZfgsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location91 (_cXZfgsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location91 (_cXZfgsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location91 (_cXZfgsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location91 (_cXZfgsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location910 (_c5TSscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location910 (_c5TSscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location910 (_c5TSscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location910 (_c5TSscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location910 (_c5TSscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location910 (_c5TSscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location910 (_c5TSscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location911 (_c5W9EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location911 (_c5W9EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location911 (_c5W9EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location911 (_c5W9EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location911 (_c5W9EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location911 (_c5W9EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location911 (_c5W9EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location912 (_c5anccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location912 (_c5anccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location912 (_c5anccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location912 (_c5anccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location912 (_c5anccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location912 (_c5anccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location912 (_c5anccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location913 (_c5e44crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location913 (_c5e44crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location913 (_c5e44crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location913 (_c5e44crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location913 (_c5e44crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location913 (_c5e44crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location913 (_c5e44crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location914 (_c5jKUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location914 (_c5jKUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location914 (_c5jKUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location914 (_c5jKUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location914 (_c5jKUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location914 (_c5jKUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location914 (_c5jKUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location915 (_c5m0scrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location915 (_c5m0scrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location915 (_c5m0scrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location915 (_c5m0scrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location915 (_c5m0scrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location915 (_c5m0scrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location915 (_c5m0scrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location916 (_c5qfEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location916 (_c5qfEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location916 (_c5qfEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location916 (_c5qfEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location916 (_c5qfEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location916 (_c5qfEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location916 (_c5qfEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location917 (_c5uwgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location917 (_c5uwgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location917 (_c5uwgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location917 (_c5uwgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location917 (_c5uwgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location917 (_c5uwgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location917 (_c5uwgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location918 (_c5ya4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location918 (_c5ya4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location918 (_c5ya4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location918 (_c5ya4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location918 (_c5ya4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location918 (_c5ya4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location918 (_c5ya4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location919 (_c53TYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location919 (_c53TYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location919 (_c53TYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location919 (_c53TYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location919 (_c53TYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location919 (_c53TYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location919 (_c53TYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location92 (_cXaGkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location92 (_cXaGkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location92 (_cXaGkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location92 (_cXaGkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location92 (_cXaGkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location92 (_cXaGkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location92 (_cXaGkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location920 (_c569wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location920 (_c569wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location920 (_c569wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location920 (_c569wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location920 (_c569wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location920 (_c569wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location920 (_c569wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location921 (_c5_PMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location921 (_c5_PMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location921 (_c5_PMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location921 (_c5_PMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location921 (_c5_PMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location921 (_c5_PMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location921 (_c5_PMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location922 (_c6C5kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location922 (_c6C5kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location922 (_c6C5kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location922 (_c6C5kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location922 (_c6C5kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location922 (_c6C5kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location922 (_c6C5kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location923 (_c6HLAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location923 (_c6HLAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location923 (_c6HLAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location923 (_c6HLAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location923 (_c6HLAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location923 (_c6HLAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location923 (_c6HLAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location924 (_c6K1YcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location924 (_c6K1YcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location924 (_c6K1YcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location924 (_c6K1YcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location924 (_c6K1YcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location924 (_c6K1YcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location924 (_c6K1YcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location925 (_c6PG0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location925 (_c6PG0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location925 (_c6PG0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location925 (_c6PG0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location925 (_c6PG0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location925 (_c6PG0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location925 (_c6PG0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location926 (_c6SxMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location926 (_c6SxMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location926 (_c6SxMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location926 (_c6SxMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location926 (_c6SxMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location926 (_c6SxMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location926 (_c6SxMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location927 (_c6XCocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location927 (_c6XCocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location927 (_c6XCocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location927 (_c6XCocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location927 (_c6XCocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location927 (_c6XCocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location927 (_c6XCocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location928 (_c6atAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location928 (_c6atAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location928 (_c6atAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location928 (_c6atAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location928 (_c6atAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location928 (_c6atAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location928 (_c6atAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location929 (_c6e-ccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location929 (_c6e-ccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location929 (_c6e-ccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location929 (_c6e-ccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location929 (_c6e-ccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location929 (_c6e-ccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location929 (_c6e-ccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location93 (_cXaGlcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location93 (_cXaGlcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location93 (_cXaGlcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location93 (_cXaGlcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location93 (_cXaGlcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location93 (_cXaGlcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location93 (_cXaGlcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location930 (_c6io0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location930 (_c6io0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location930 (_c6io0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location930 (_c6io0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location930 (_c6io0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location930 (_c6io0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location930 (_c6io0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location931 (_c6oIYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location931 (_c6oIYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location931 (_c6oIYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location931 (_c6oIYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location931 (_c6oIYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location931 (_c6oIYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location931 (_c6oIYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location932 (_c6sZ0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location932 (_c6sZ0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location932 (_c6sZ0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location932 (_c6sZ0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location932 (_c6sZ0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location932 (_c6sZ0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location932 (_c6sZ0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location933 (_c6x5YcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location933 (_c6x5YcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location933 (_c6x5YcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location933 (_c6x5YcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location933 (_c6x5YcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location933 (_c6x5YcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location933 (_c6x5YcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location934 (_c61jwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location934 (_c61jwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location934 (_c61jwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location934 (_c61jwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location934 (_c61jwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location934 (_c61jwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location934 (_c61jwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location935 (_c651McrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location935 (_c651McrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location935 (_c651McrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location935 (_c651McrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location935 (_c651McrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location935 (_c651McrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location935 (_c651McrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location936 (_c6-GocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location936 (_c6-GocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location936 (_c6-GocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location936 (_c6-GocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location936 (_c6-GocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location936 (_c6-GocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location936 (_c6-GocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location937 (_c7BxAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location937 (_c7BxAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location937 (_c7BxAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location937 (_c7BxAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location937 (_c7BxAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location937 (_c7BxAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location937 (_c7BxAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location938 (_c7GCccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location938 (_c7GCccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location938 (_c7GCccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location938 (_c7GCccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location938 (_c7GCccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location938 (_c7GCccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location938 (_c7GCccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location939 (_c7Js0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location939 (_c7Js0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location939 (_c7Js0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location939 (_c7Js0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location939 (_c7Js0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location939 (_c7Js0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location939 (_c7Js0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location94 (_cXbUscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location94 (_cXbUscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location94 (_cXbUscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location94 (_cXbUscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location94 (_cXbUscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location94 (_cXbUscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location94 (_cXbUscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location940 (_c7N-QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location940 (_c7N-QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location940 (_c7N-QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location940 (_c7N-QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location940 (_c7N-QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location940 (_c7N-QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location940 (_c7N-QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location941 (_c7RoocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location941 (_c7RoocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location941 (_c7RoocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location941 (_c7RoocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location941 (_c7RoocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location941 (_c7RoocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location941 (_c7RoocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location942 (_c7V6EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location942 (_c7V6EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location942 (_c7V6EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location942 (_c7V6EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location942 (_c7V6EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location942 (_c7V6EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location942 (_c7V6EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location943 (_c7aLgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location943 (_c7aLgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location943 (_c7aLgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location943 (_c7aLgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location943 (_c7aLgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location943 (_c7aLgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location943 (_c7aLgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location944 (_c7d14crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location944 (_c7d14crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location944 (_c7d14crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location944 (_c7d14crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location944 (_c7d14crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location944 (_c7d14crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location944 (_c7d14crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location945 (_c7iHUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location945 (_c7iHUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location945 (_c7iHUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location945 (_c7iHUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location945 (_c7iHUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location945 (_c7iHUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location945 (_c7iHUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location946 (_c7mYwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location946 (_c7mYwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location946 (_c7mYwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location946 (_c7mYwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location946 (_c7mYwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location946 (_c7mYwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location946 (_c7mYwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location947 (_c7qDIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location947 (_c7qDIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location947 (_c7qDIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location947 (_c7qDIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location947 (_c7qDIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location947 (_c7qDIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location947 (_c7qDIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location948 (_c7uUkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location948 (_c7uUkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location948 (_c7uUkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location948 (_c7uUkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location948 (_c7uUkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location948 (_c7uUkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location948 (_c7uUkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location949 (_c7x-8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location949 (_c7x-8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location949 (_c7x-8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location949 (_c7x-8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location949 (_c7x-8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location949 (_c7x-8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location949 (_c7x-8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location95 (_cXb7wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location95 (_cXb7wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location95 (_cXb7wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location95 (_cXb7wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location95 (_cXb7wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location95 (_cXb7wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location95 (_cXb7wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location950 (_c723ccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location950 (_c723ccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location950 (_c723ccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location950 (_c723ccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location950 (_c723ccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location950 (_c723ccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location950 (_c723ccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location951 (_c76h0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location951 (_c76h0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location951 (_c76h0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location951 (_c76h0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location951 (_c76h0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location951 (_c76h0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location951 (_c76h0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location952 (_c7-zQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location952 (_c7-zQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location952 (_c7-zQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location952 (_c7-zQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location952 (_c7-zQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location952 (_c7-zQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location952 (_c7-zQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location953 (_c8DEscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location953 (_c8DEscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location953 (_c8DEscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location953 (_c8DEscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location953 (_c8DEscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location953 (_c8DEscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location953 (_c8DEscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location954 (_c8GvEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location954 (_c8GvEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location954 (_c8GvEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location954 (_c8GvEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location954 (_c8GvEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location954 (_c8GvEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location954 (_c8GvEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location955 (_c8LnkMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location955 (_c8LnkMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location955 (_c8LnkMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location955 (_c8LnkMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location955 (_c8LnkMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location955 (_c8LnkMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location955 (_c8LnkMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location956 (_c8PR8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location956 (_c8PR8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location956 (_c8PR8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location956 (_c8PR8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location956 (_c8PR8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location956 (_c8PR8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location956 (_c8PR8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location957 (_c8UxgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location957 (_c8UxgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location957 (_c8UxgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location957 (_c8UxgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location957 (_c8UxgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location957 (_c8UxgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location957 (_c8UxgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location958 (_c8aREcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location958 (_c8aREcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location958 (_c8aREcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location958 (_c8aREcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location958 (_c8aREcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location958 (_c8aREcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location958 (_c8aREcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location959 (_c8fwocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location959 (_c8fwocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location959 (_c8fwocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location959 (_c8fwocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location959 (_c8fwocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location959 (_c8fwocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location959 (_c8fwocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location96 (_cXb7xcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location96 (_cXb7xcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location96 (_cXb7xcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location96 (_cXb7xcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location96 (_cXb7xcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location96 (_cXb7xcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location96 (_cXb7xcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location960 (_c8kCEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location960 (_c8kCEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location960 (_c8kCEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location960 (_c8kCEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location960 (_c8kCEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location960 (_c8kCEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location960 (_c8kCEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location961 (_c8qIscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location961 (_c8qIscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location961 (_c8qIscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location961 (_c8qIscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location961 (_c8qIscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location961 (_c8qIscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location961 (_c8qIscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location962 (_c8voQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location962 (_c8voQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location962 (_c8voQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location962 (_c8voQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location962 (_c8voQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location962 (_c8voQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location962 (_c8voQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location963 (_c80gwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location963 (_c80gwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location963 (_c80gwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location963 (_c80gwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location963 (_c80gwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location963 (_c80gwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location963 (_c80gwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location964 (_c84yMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location964 (_c84yMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location964 (_c84yMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location964 (_c84yMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location964 (_c84yMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location964 (_c84yMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location964 (_c84yMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location965 (_c89qscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location965 (_c89qscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location965 (_c89qscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location965 (_c89qscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location965 (_c89qscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location965 (_c89qscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location965 (_c89qscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location966 (_c9B8IcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location966 (_c9B8IcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location966 (_c9B8IcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location966 (_c9B8IcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location966 (_c9B8IcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location966 (_c9B8IcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location966 (_c9B8IcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location967 (_c9G0ocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location967 (_c9G0ocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location967 (_c9G0ocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location967 (_c9G0ocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location967 (_c9G0ocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location967 (_c9G0ocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location967 (_c9G0ocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location968 (_c9LGEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location968 (_c9LGEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location968 (_c9LGEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location968 (_c9LGEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location968 (_c9LGEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location968 (_c9LGEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location968 (_c9LGEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location969 (_c9P-kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location969 (_c9P-kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location969 (_c9P-kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location969 (_c9P-kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location969 (_c9P-kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location969 (_c9P-kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location969 (_c9P-kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location97 (_cXci08rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location97 (_cXci08rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location97 (_cXci08rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location97 (_cXci08rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location97 (_cXci08rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location97 (_cXci08rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location97 (_cXci08rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location970 (_c9U3EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location970 (_c9U3EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location970 (_c9U3EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location970 (_c9U3EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location970 (_c9U3EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location970 (_c9U3EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location970 (_c9U3EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location971 (_c9ZIgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location971 (_c9ZIgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location971 (_c9ZIgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location971 (_c9ZIgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location971 (_c9ZIgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location971 (_c9ZIgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location971 (_c9ZIgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location972 (_c9eBAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location972 (_c9eBAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location972 (_c9eBAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location972 (_c9eBAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location972 (_c9eBAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location972 (_c9eBAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location972 (_c9eBAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location973 (_c9i5gcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location973 (_c9i5gcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location973 (_c9i5gcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location973 (_c9i5gcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location973 (_c9i5gcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location973 (_c9i5gcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location973 (_c9i5gcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location974 (_c9nK8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location974 (_c9nK8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location974 (_c9nK8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location974 (_c9nK8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location974 (_c9nK8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location974 (_c9nK8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location974 (_c9nK8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location975 (_c9sDccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location975 (_c9sDccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location975 (_c9sDccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location975 (_c9sDccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location975 (_c9sDccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location975 (_c9sDccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location975 (_c9sDccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location976 (_c9w78crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location976 (_c9w78crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location976 (_c9w78crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location976 (_c9w78crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location976 (_c9w78crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location976 (_c9w78crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location976 (_c9w78crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location977 (_c910ccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location977 (_c910ccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location977 (_c910ccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location977 (_c910ccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location977 (_c910ccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location977 (_c910ccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location977 (_c910ccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location978 (_c96s8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location978 (_c96s8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location978 (_c96s8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location978 (_c96s8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location978 (_c96s8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location978 (_c96s8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location978 (_c96s8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location979 (_c9--YcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location979 (_c9--YcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location979 (_c9--YcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location979 (_c9--YcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location979 (_c9--YcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location979 (_c9--YcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location979 (_c9--YcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location98 (_cXdJ4srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location98 (_cXdJ4srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location98 (_cXdJ4srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location98 (_cXdJ4srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location98 (_cXdJ4srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location98 (_cXdJ4srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location98 (_cXdJ4srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location980 (_c-G6McrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location980 (_c-G6McrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location980 (_c-G6McrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location980 (_c-G6McrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location980 (_c-G6McrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location980 (_c-G6McrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location980 (_c-G6McrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location981 (_c-LyscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location981 (_c-LyscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location981 (_c-LyscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location981 (_c-LyscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location981 (_c-LyscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location981 (_c-LyscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location981 (_c-LyscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location982 (_c-RSQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location982 (_c-RSQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location982 (_c-RSQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location982 (_c-RSQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location982 (_c-RSQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location982 (_c-RSQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location982 (_c-RSQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location983 (_c-VjscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location983 (_c-VjscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location983 (_c-VjscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location983 (_c-VjscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location983 (_c-VjscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location983 (_c-VjscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location983 (_c-VjscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location984 (_c-acMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location984 (_c-acMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location984 (_c-acMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location984 (_c-acMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location984 (_c-acMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location984 (_c-acMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location984 (_c-acMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location985 (_c-fUscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location985 (_c-fUscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location985 (_c-fUscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location985 (_c-fUscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location985 (_c-fUscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location985 (_c-fUscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location985 (_c-fUscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location986 (_c-kNMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location986 (_c-kNMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location986 (_c-kNMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location986 (_c-kNMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location986 (_c-kNMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location986 (_c-kNMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location986 (_c-kNMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location987 (_c-pFscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location987 (_c-pFscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location987 (_c-pFscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location987 (_c-pFscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location987 (_c-pFscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location987 (_c-pFscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location987 (_c-pFscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location988 (_c-ulQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location988 (_c-ulQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location988 (_c-ulQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location988 (_c-ulQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location988 (_c-ulQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location988 (_c-ulQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location988 (_c-ulQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location989 (_c-zdwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location989 (_c-zdwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location989 (_c-zdwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location989 (_c-zdwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location989 (_c-zdwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location989 (_c-zdwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location989 (_c-zdwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location99 (_cXdw8srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location99 (_cXdw8srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location99 (_cXdw8srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location99 (_cXdw8srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location99 (_cXdw8srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location99 (_cXdw8srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location99 (_cXdw8srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location990 (_c-49UcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location990 (_c-49UcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location990 (_c-49UcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location990 (_c-49UcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location990 (_c-49UcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location990 (_c-49UcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location990 (_c-49UcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location991 (_c-910crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location991 (_c-910crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location991 (_c-910crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location991 (_c-910crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location991 (_c-910crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location991 (_c-910crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location991 (_c-910crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location992 (_c_CuUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location992 (_c_CuUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location992 (_c_CuUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location992 (_c_CuUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location992 (_c_CuUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location992 (_c_CuUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location992 (_c_CuUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location993 (_c_G_wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location993 (_c_G_wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location993 (_c_G_wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location993 (_c_G_wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location993 (_c_G_wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location993 (_c_G_wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location993 (_c_G_wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location994 (_c_MfUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location994 (_c_MfUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location994 (_c_MfUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location994 (_c_MfUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location994 (_c_MfUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location994 (_c_MfUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location994 (_c_MfUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location995 (_c_RX0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location995 (_c_RX0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location995 (_c_RX0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location995 (_c_RX0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location995 (_c_RX0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location995 (_c_RX0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location995 (_c_RX0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location996 (_c_WQUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location996 (_c_WQUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location996 (_c_WQUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location996 (_c_WQUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location996 (_c_WQUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location996 (_c_WQUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location996 (_c_WQUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location997 (_c_bI0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location997 (_c_bI0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location997 (_c_bI0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location997 (_c_bI0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location997 (_c_bI0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location997 (_c_bI0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location997 (_c_bI0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location998 (_c_gBUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location998 (_c_gBUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location998 (_c_gBUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location998 (_c_gBUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location998 (_c_gBUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location998 (_c_gBUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location998 (_c_gBUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location999 (_c_k50crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location999 (_c_k50crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location999 (_c_k50crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location999 (_c_k50crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location999 (_c_k50crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location999 (_c_k50crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location999 (_c_k50crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Read Access (_rd9cA9VeEeqRbpVUMz5XAQ)').
characteristicTypeValue('Read Access (_rd9cA9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Read Access (_rd9cA9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Read Access (_rd9cA9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Read Access (_rd9cA9VeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Read Access (_rd9cA9VeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Read Access (_rd9cA9VeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).

% =====
% Nodes
% =====
% Actor Scientist
actor('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)').
nodeCharacteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').
inputPin('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'input (_oG4EENVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)').
outputPin('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'output (_oaeVgdVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)').
characteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'output (_oaeVgdVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)').
characteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'output (_oaeVgdVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)').
characteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'output (_oaeVgdVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').
characteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'output (_oaeVgdVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)').
characteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'output (_oaeVgdVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)').
characteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'output (_oaeVgdVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').
characteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'output (_oaeVgdVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)').
characteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'output (_oaeVgdVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)').
characteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'output (_oaeVgdVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').

% Actor Worker
actor('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)').
nodeCharacteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').
inputPin('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'input (_ytCKcNVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)').
outputPin('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'output (_y8wBcdVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)').
characteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'output (_y8wBcdVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)').
characteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'output (_y8wBcdVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)').
characteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'output (_y8wBcdVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').
characteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'output (_y8wBcdVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)').
characteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'output (_y8wBcdVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)').
characteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'output (_y8wBcdVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').
characteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'output (_y8wBcdVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)').
characteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'output (_y8wBcdVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)').
characteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'output (_y8wBcdVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').

% Actor Visitor
actor('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)').
nodeCharacteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').
inputPin('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'input (_-2tSANVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)').
outputPin('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'output (__MIvcdVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)').
characteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'output (__MIvcdVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)').
characteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'output (__MIvcdVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)').
characteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'output (__MIvcdVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').
characteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'output (__MIvcdVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)').
characteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'output (__MIvcdVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)').
characteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'output (__MIvcdVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').
characteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'output (__MIvcdVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)').
characteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'output (__MIvcdVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)').
characteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'output (__MIvcdVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', [], _) :-
	nodeCharacteristic('Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').

% Process read DB
process('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)').
inputPin('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)').
outputPin('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)').
characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S0, VISITED).

% Process write DB
process('write DB (_qSfIF8hpEeuNMePdRPFY4g)').
inputPin('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)').
outputPin('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)').
characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S0, VISITED).

% Store Laboratory DB
store('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)').
nodeCharacteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'Read Access (_rd9cA9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)').
inputPin('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)').
outputPin('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'output (_DEBuYdVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)').
characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'output (_DEBuYdVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'output (_DEBuYdVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'output (_DEBuYdVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'output (_DEBuYdVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'output (_DEBuYdVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'output (_DEBuYdVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'output (_DEBuYdVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'output (_DEBuYdVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', S0, VISITED).
characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'output (_DEBuYdVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S, VISITED) :-
	inputFlow('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', S0, VISITED).

% =====
% Edges
% =====
dataflow('dbEntry (_OMdmechGEeu_Wf8wLuiSoQ)', 'read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'input (_oG4EENVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)').
dataflow('dbEntry (_fis5ichGEeu_Wf8wLuiSoQ)', 'read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Worker (_Glj7ddVfEeqRbpVUMz5XAQ)', 'input (_ytCKcNVhEeqRbpVUMz5XAQ_Glj7ddVfEeqRbpVUMz5XAQ)').
dataflow('dbEntry (_j8-sechGEeu_Wf8wLuiSoQ)', 'read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)', 'Visitor (_JEgDFdVfEeqRbpVUMz5XAQ)', 'input (_-2tSANVhEeqRbpVUMz5XAQ_JEgDFdVfEeqRbpVUMz5XAQ)').
dataflow('dbEntry (_nI-uachGEeu_Wf8wLuiSoQ)', 'Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'output (_DEBuYdVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)', 'read DB (_bt1Dx9VhEeqRbpVUMz5XAQ)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_bt1Dx9VhEeqRbpVUMz5XAQ)').
dataflow('dbEntry (_F09lqchqEeuNMePdRPFY4g)', 'Scientist (_EoxepdVfEeqRbpVUMz5XAQ)', 'output (_oaeVgdVhEeqRbpVUMz5XAQ_EoxepdVfEeqRbpVUMz5XAQ)', 'write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'input (_7LfE0NVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)').
dataflow('dbEntry (_J7OQachqEeuNMePdRPFY4g)', 'write DB (_qSfIF8hpEeuNMePdRPFY4g)', 'output (_8BeRodVeEeqRbpVUMz5XAQ_qSfIF8hpEeuNMePdRPFY4g)', 'Laboratory DB (_gIROyNVhEeqRbpVUMz5XAQ)', 'input (_CsafoNVfEeqRbpVUMz5XAQ_gIROyNVhEeqRbpVUMz5XAQ)').
