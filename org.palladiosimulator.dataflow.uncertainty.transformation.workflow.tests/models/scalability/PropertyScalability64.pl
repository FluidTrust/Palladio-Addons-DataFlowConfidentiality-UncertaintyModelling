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
characteristicType('Location0 (_Zk_pUMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location0 (_Zk_pUMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location0 (_Zk_pUMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location0 (_Zk_pUMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location0 (_Zk_pUMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location0 (_Zk_pUMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location0 (_Zk_pUMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1 (_ZlBegsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1 (_ZlBegsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1 (_ZlBegsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1 (_ZlBegsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1 (_ZlBegsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1 (_ZlBegsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1 (_ZlBegsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location10 (_ZlCsp8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location10 (_ZlCsp8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location10 (_ZlCsp8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location10 (_ZlCsp8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location10 (_ZlCsp8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location10 (_ZlCsp8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location10 (_ZlCsp8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location11 (_ZlCsq8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location11 (_ZlCsq8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location11 (_ZlCsq8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location11 (_ZlCsq8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location11 (_ZlCsq8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location11 (_ZlCsq8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location11 (_ZlCsq8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location12 (_ZlCsr8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location12 (_ZlCsr8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location12 (_ZlCsr8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location12 (_ZlCsr8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location12 (_ZlCsr8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location12 (_ZlCsr8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location12 (_ZlCsr8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location13 (_ZlDTs8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location13 (_ZlDTs8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location13 (_ZlDTs8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location13 (_ZlDTs8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location13 (_ZlDTs8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location13 (_ZlDTs8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location13 (_ZlDTs8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location14 (_ZlDTt8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location14 (_ZlDTt8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location14 (_ZlDTt8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location14 (_ZlDTt8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location14 (_ZlDTt8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location14 (_ZlDTt8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location14 (_ZlDTt8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location15 (_ZlDTu8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location15 (_ZlDTu8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location15 (_ZlDTu8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location15 (_ZlDTu8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location15 (_ZlDTu8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location15 (_ZlDTu8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location15 (_ZlDTu8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location16 (_ZlD6wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location16 (_ZlD6wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location16 (_ZlD6wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location16 (_ZlD6wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location16 (_ZlD6wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location16 (_ZlD6wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location16 (_ZlD6wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location17 (_ZlD6xcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location17 (_ZlD6xcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location17 (_ZlD6xcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location17 (_ZlD6xcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location17 (_ZlD6xcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location17 (_ZlD6xcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location17 (_ZlD6xcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location18 (_ZlD6ycrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location18 (_ZlD6ycrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location18 (_ZlD6ycrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location18 (_ZlD6ycrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location18 (_ZlD6ycrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location18 (_ZlD6ycrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location18 (_ZlD6ycrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location19 (_ZlEh0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location19 (_ZlEh0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location19 (_ZlEh0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location19 (_ZlEh0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location19 (_ZlEh0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location19 (_ZlEh0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location19 (_ZlEh0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location2 (_ZlBehsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location2 (_ZlBehsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location2 (_ZlBehsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location2 (_ZlBehsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location2 (_ZlBehsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location2 (_ZlBehsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location2 (_ZlBehsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location20 (_ZlEh1crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location20 (_ZlEh1crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location20 (_ZlEh1crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location20 (_ZlEh1crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location20 (_ZlEh1crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location20 (_ZlEh1crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location20 (_ZlEh1crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location21 (_ZlEh2crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location21 (_ZlEh2crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location21 (_ZlEh2crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location21 (_ZlEh2crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location21 (_ZlEh2crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location21 (_ZlEh2crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location21 (_ZlEh2crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location22 (_ZlFI4srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location22 (_ZlFI4srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location22 (_ZlFI4srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location22 (_ZlFI4srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location22 (_ZlFI4srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location22 (_ZlFI4srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location22 (_ZlFI4srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location23 (_ZlFI5srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location23 (_ZlFI5srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location23 (_ZlFI5srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location23 (_ZlFI5srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location23 (_ZlFI5srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location23 (_ZlFI5srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location23 (_ZlFI5srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location24 (_ZlFv8MrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location24 (_ZlFv8MrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location24 (_ZlFv8MrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location24 (_ZlFv8MrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location24 (_ZlFv8MrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location24 (_ZlFv8MrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location24 (_ZlFv8MrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location25 (_ZlFv9MrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location25 (_ZlFv9MrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location25 (_ZlFv9MrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location25 (_ZlFv9MrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location25 (_ZlFv9MrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location25 (_ZlFv9MrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location25 (_ZlFv9MrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location26 (_ZlFv-MrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location26 (_ZlFv-MrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location26 (_ZlFv-MrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location26 (_ZlFv-MrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location26 (_ZlFv-MrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location26 (_ZlFv-MrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location26 (_ZlFv-MrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location27 (_ZlGXA8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location27 (_ZlGXA8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location27 (_ZlGXA8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location27 (_ZlGXA8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location27 (_ZlGXA8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location27 (_ZlGXA8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location27 (_ZlGXA8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location28 (_ZlGXB8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location28 (_ZlGXB8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location28 (_ZlGXB8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location28 (_ZlGXB8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location28 (_ZlGXB8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location28 (_ZlGXB8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location28 (_ZlGXB8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location29 (_ZlG-E8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location29 (_ZlG-E8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location29 (_ZlG-E8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location29 (_ZlG-E8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location29 (_ZlG-E8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location29 (_ZlG-E8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location29 (_ZlG-E8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location3 (_ZlBeisrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location3 (_ZlBeisrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location3 (_ZlBeisrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location3 (_ZlBeisrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location3 (_ZlBeisrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location3 (_ZlBeisrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location3 (_ZlBeisrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location30 (_ZlG-F8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location30 (_ZlG-F8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location30 (_ZlG-F8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location30 (_ZlG-F8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location30 (_ZlG-F8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location30 (_ZlG-F8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location30 (_ZlG-F8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location31 (_ZlHlI8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location31 (_ZlHlI8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location31 (_ZlHlI8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location31 (_ZlHlI8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location31 (_ZlHlI8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location31 (_ZlHlI8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location31 (_ZlHlI8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location32 (_ZlIMMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location32 (_ZlIMMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location32 (_ZlIMMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location32 (_ZlIMMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location32 (_ZlIMMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location32 (_ZlIMMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location32 (_ZlIMMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location33 (_ZlIMNcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location33 (_ZlIMNcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location33 (_ZlIMNcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location33 (_ZlIMNcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location33 (_ZlIMNcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location33 (_ZlIMNcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location33 (_ZlIMNcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location34 (_ZlIzQ8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location34 (_ZlIzQ8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location34 (_ZlIzQ8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location34 (_ZlIzQ8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location34 (_ZlIzQ8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location34 (_ZlIzQ8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location34 (_ZlIzQ8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location35 (_ZlJaUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location35 (_ZlJaUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location35 (_ZlJaUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location35 (_ZlJaUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location35 (_ZlJaUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location35 (_ZlJaUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location35 (_ZlJaUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location36 (_ZlJaVcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location36 (_ZlJaVcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location36 (_ZlJaVcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location36 (_ZlJaVcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location36 (_ZlJaVcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location36 (_ZlJaVcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location36 (_ZlJaVcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location37 (_ZlKBY8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location37 (_ZlKBY8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location37 (_ZlKBY8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location37 (_ZlKBY8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location37 (_ZlKBY8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location37 (_ZlKBY8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location37 (_ZlKBY8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location38 (_ZlKoc8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location38 (_ZlKoc8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location38 (_ZlKoc8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location38 (_ZlKoc8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location38 (_ZlKoc8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location38 (_ZlKoc8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location38 (_ZlKoc8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location39 (_ZlLPgsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location39 (_ZlLPgsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location39 (_ZlLPgsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location39 (_ZlLPgsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location39 (_ZlLPgsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location39 (_ZlLPgsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location39 (_ZlLPgsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location4 (_ZlCFkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location4 (_ZlCFkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location4 (_ZlCFkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location4 (_ZlCFkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location4 (_ZlCFkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location4 (_ZlCFkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location4 (_ZlCFkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location40 (_ZlL2kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location40 (_ZlL2kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location40 (_ZlL2kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location40 (_ZlL2kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location40 (_ZlL2kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location40 (_ZlL2kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location40 (_ZlL2kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location41 (_ZlL2lcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location41 (_ZlL2lcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location41 (_ZlL2lcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location41 (_ZlL2lcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location41 (_ZlL2lcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location41 (_ZlL2lcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location41 (_ZlL2lcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location42 (_ZlMdo8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location42 (_ZlMdo8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location42 (_ZlMdo8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location42 (_ZlMdo8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location42 (_ZlMdo8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location42 (_ZlMdo8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location42 (_ZlMdo8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location43 (_ZlNEscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location43 (_ZlNEscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location43 (_ZlNEscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location43 (_ZlNEscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location43 (_ZlNEscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location43 (_ZlNEscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location43 (_ZlNEscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location44 (_ZlNEtcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location44 (_ZlNEtcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location44 (_ZlNEtcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location44 (_ZlNEtcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location44 (_ZlNEtcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location44 (_ZlNEtcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location44 (_ZlNEtcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location45 (_ZlNrw8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location45 (_ZlNrw8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location45 (_ZlNrw8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location45 (_ZlNrw8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location45 (_ZlNrw8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location45 (_ZlNrw8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location45 (_ZlNrw8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location46 (_ZlOS0srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location46 (_ZlOS0srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location46 (_ZlOS0srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location46 (_ZlOS0srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location46 (_ZlOS0srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location46 (_ZlOS0srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location46 (_ZlOS0srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location47 (_ZlO54crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location47 (_ZlO54crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location47 (_ZlO54crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location47 (_ZlO54crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location47 (_ZlO54crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location47 (_ZlO54crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location47 (_ZlO54crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location48 (_ZlO55crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location48 (_ZlO55crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location48 (_ZlO55crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location48 (_ZlO55crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location48 (_ZlO55crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location48 (_ZlO55crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location48 (_ZlO55crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location49 (_ZlPg88rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location49 (_ZlPg88rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location49 (_ZlPg88rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location49 (_ZlPg88rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location49 (_ZlPg88rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location49 (_ZlPg88rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location49 (_ZlPg88rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location5 (_ZlCFlcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location5 (_ZlCFlcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location5 (_ZlCFlcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location5 (_ZlCFlcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location5 (_ZlCFlcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location5 (_ZlCFlcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location5 (_ZlCFlcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location50 (_ZlQIAsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location50 (_ZlQIAsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location50 (_ZlQIAsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location50 (_ZlQIAsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location50 (_ZlQIAsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location50 (_ZlQIAsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location50 (_ZlQIAsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location51 (_ZlQvEsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location51 (_ZlQvEsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location51 (_ZlQvEsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location51 (_ZlQvEsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location51 (_ZlQvEsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location51 (_ZlQvEsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location51 (_ZlQvEsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location52 (_ZlRWIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location52 (_ZlRWIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location52 (_ZlRWIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location52 (_ZlRWIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location52 (_ZlRWIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location52 (_ZlRWIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location52 (_ZlRWIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location53 (_ZlR9McrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location53 (_ZlR9McrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location53 (_ZlR9McrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location53 (_ZlR9McrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location53 (_ZlR9McrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location53 (_ZlR9McrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location53 (_ZlR9McrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location54 (_ZlSkQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location54 (_ZlSkQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location54 (_ZlSkQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location54 (_ZlSkQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location54 (_ZlSkQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location54 (_ZlSkQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location54 (_ZlSkQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location55 (_ZlTLUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location55 (_ZlTLUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location55 (_ZlTLUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location55 (_ZlTLUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location55 (_ZlTLUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location55 (_ZlTLUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location55 (_ZlTLUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location56 (_ZlTyYsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location56 (_ZlTyYsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location56 (_ZlTyYsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location56 (_ZlTyYsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location56 (_ZlTyYsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location56 (_ZlTyYsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location56 (_ZlTyYsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location57 (_ZlUZc8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location57 (_ZlUZc8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location57 (_ZlUZc8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location57 (_ZlUZc8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location57 (_ZlUZc8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location57 (_ZlUZc8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location57 (_ZlUZc8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location58 (_ZlVAgsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location58 (_ZlVAgsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location58 (_ZlVAgsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location58 (_ZlVAgsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location58 (_ZlVAgsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location58 (_ZlVAgsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location58 (_ZlVAgsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location59 (_ZlVnksrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location59 (_ZlVnksrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location59 (_ZlVnksrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location59 (_ZlVnksrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location59 (_ZlVnksrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location59 (_ZlVnksrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location59 (_ZlVnksrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location6 (_ZlCFmcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location6 (_ZlCFmcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location6 (_ZlCFmcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location6 (_ZlCFmcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location6 (_ZlCFmcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location6 (_ZlCFmcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location6 (_ZlCFmcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location60 (_ZlWOocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location60 (_ZlWOocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location60 (_ZlWOocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location60 (_ZlWOocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location60 (_ZlWOocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location60 (_ZlWOocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location60 (_ZlWOocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location61 (_ZlW1ssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location61 (_ZlW1ssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location61 (_ZlW1ssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location61 (_ZlW1ssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location61 (_ZlW1ssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location61 (_ZlW1ssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location61 (_ZlW1ssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location62 (_ZlXcwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location62 (_ZlXcwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location62 (_ZlXcwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location62 (_ZlXcwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location62 (_ZlXcwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location62 (_ZlXcwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location62 (_ZlXcwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location63 (_ZlYD0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location63 (_ZlYD0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location63 (_ZlYD0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location63 (_ZlYD0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location63 (_ZlYD0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location63 (_ZlYD0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location63 (_ZlYD0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location7 (_ZlCFncrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location7 (_ZlCFncrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location7 (_ZlCFncrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location7 (_ZlCFncrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location7 (_ZlCFncrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location7 (_ZlCFncrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location7 (_ZlCFncrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location8 (_ZlCFocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location8 (_ZlCFocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location8 (_ZlCFocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location8 (_ZlCFocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location8 (_ZlCFocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location8 (_ZlCFocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location8 (_ZlCFocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location9 (_ZlCso8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location9 (_ZlCso8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location9 (_ZlCso8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location9 (_ZlCso8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location9 (_ZlCso8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location9 (_ZlCso8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location9 (_ZlCso8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
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
