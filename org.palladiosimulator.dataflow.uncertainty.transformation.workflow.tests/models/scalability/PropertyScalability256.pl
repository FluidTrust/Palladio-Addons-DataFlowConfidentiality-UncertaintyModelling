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
characteristicType('Location0 (_aGt2UcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location0 (_aGt2UcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location0 (_aGt2UcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location0 (_aGt2UcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location0 (_aGt2UcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location0 (_aGt2UcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location0 (_aGt2UcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location1 (_aGvrgsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location1 (_aGvrgsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location1 (_aGvrgsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location1 (_aGvrgsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location1 (_aGvrgsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location1 (_aGvrgsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location1 (_aGvrgsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location10 (_aGw5rsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location10 (_aGw5rsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location10 (_aGw5rsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location10 (_aGw5rsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location10 (_aGw5rsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location10 (_aGw5rsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location10 (_aGw5rsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location100 (_aHWvgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location100 (_aHWvgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location100 (_aHWvgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location100 (_aHWvgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location100 (_aHWvgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location100 (_aHWvgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location100 (_aHWvgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location101 (_aHXWkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location101 (_aHXWkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location101 (_aHXWkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location101 (_aHXWkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location101 (_aHXWkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location101 (_aHXWkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location101 (_aHXWkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location102 (_aHX9osrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location102 (_aHX9osrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location102 (_aHX9osrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location102 (_aHX9osrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location102 (_aHX9osrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location102 (_aHX9osrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location102 (_aHX9osrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location103 (_aHYkssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location103 (_aHYkssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location103 (_aHYkssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location103 (_aHYkssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location103 (_aHYkssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location103 (_aHYkssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location103 (_aHYkssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location104 (_aHZLwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location104 (_aHZLwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location104 (_aHZLwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location104 (_aHZLwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location104 (_aHZLwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location104 (_aHZLwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location104 (_aHZLwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location105 (_aHZy0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location105 (_aHZy0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location105 (_aHZy0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location105 (_aHZy0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location105 (_aHZy0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location105 (_aHZy0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location105 (_aHZy0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location106 (_aHaZ4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location106 (_aHaZ4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location106 (_aHaZ4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location106 (_aHaZ4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location106 (_aHaZ4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location106 (_aHaZ4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location106 (_aHaZ4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location107 (_aHbA8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location107 (_aHbA8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location107 (_aHbA8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location107 (_aHbA8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location107 (_aHbA8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location107 (_aHbA8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location107 (_aHbA8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location108 (_aHboAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location108 (_aHboAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location108 (_aHboAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location108 (_aHboAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location108 (_aHboAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location108 (_aHboAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location108 (_aHboAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location109 (_aHboBcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location109 (_aHboBcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location109 (_aHboBcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location109 (_aHboBcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location109 (_aHboBcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location109 (_aHboBcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location109 (_aHboBcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location11 (_aGw5ssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location11 (_aGw5ssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location11 (_aGw5ssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location11 (_aGw5ssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location11 (_aGw5ssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location11 (_aGw5ssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location11 (_aGw5ssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location110 (_aHcPE8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location110 (_aHcPE8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location110 (_aHcPE8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location110 (_aHcPE8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location110 (_aHcPE8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location110 (_aHcPE8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location110 (_aHcPE8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location111 (_aHc2I8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location111 (_aHc2I8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location111 (_aHc2I8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location111 (_aHc2I8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location111 (_aHc2I8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location111 (_aHc2I8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location111 (_aHc2I8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location112 (_aHeEQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location112 (_aHeEQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location112 (_aHeEQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location112 (_aHeEQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location112 (_aHeEQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location112 (_aHeEQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location112 (_aHeEQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location113 (_aHerUsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location113 (_aHerUsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location113 (_aHerUsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location113 (_aHerUsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location113 (_aHerUsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location113 (_aHerUsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location113 (_aHerUsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location114 (_aHfSY8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location114 (_aHfSY8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location114 (_aHfSY8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location114 (_aHfSY8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location114 (_aHfSY8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location114 (_aHfSY8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location114 (_aHfSY8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location115 (_aHgggcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location115 (_aHgggcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location115 (_aHgggcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location115 (_aHgggcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location115 (_aHgggcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location115 (_aHgggcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location115 (_aHgggcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location116 (_aHhHkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location116 (_aHhHkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location116 (_aHhHkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location116 (_aHhHkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location116 (_aHhHkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location116 (_aHhHkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location116 (_aHhHkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location117 (_aHhuocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location117 (_aHhuocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location117 (_aHhuocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location117 (_aHhuocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location117 (_aHhuocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location117 (_aHhuocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location117 (_aHhuocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location118 (_aHiVscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location118 (_aHiVscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location118 (_aHiVscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location118 (_aHiVscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location118 (_aHiVscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location118 (_aHiVscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location118 (_aHiVscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location119 (_aHi8wsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location119 (_aHi8wsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location119 (_aHi8wsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location119 (_aHi8wsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location119 (_aHi8wsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location119 (_aHi8wsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location119 (_aHi8wsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location12 (_aGxgs8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location12 (_aGxgs8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location12 (_aGxgs8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location12 (_aGxgs8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location12 (_aGxgs8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location12 (_aGxgs8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location12 (_aGxgs8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location120 (_aHkK4srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location120 (_aHkK4srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location120 (_aHkK4srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location120 (_aHkK4srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location120 (_aHkK4srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location120 (_aHkK4srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location120 (_aHkK4srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location121 (_aHkx8srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location121 (_aHkx8srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location121 (_aHkx8srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location121 (_aHkx8srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location121 (_aHkx8srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location121 (_aHkx8srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location121 (_aHkx8srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location122 (_aHmAEsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location122 (_aHmAEsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location122 (_aHmAEsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location122 (_aHmAEsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location122 (_aHmAEsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location122 (_aHmAEsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location122 (_aHmAEsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location123 (_aHnOMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location123 (_aHnOMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location123 (_aHnOMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location123 (_aHnOMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location123 (_aHnOMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location123 (_aHnOMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location123 (_aHnOMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location124 (_aHn1Q8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location124 (_aHn1Q8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location124 (_aHn1Q8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location124 (_aHn1Q8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location124 (_aHn1Q8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location124 (_aHn1Q8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location124 (_aHn1Q8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location125 (_aHpDYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location125 (_aHpDYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location125 (_aHpDYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location125 (_aHpDYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location125 (_aHpDYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location125 (_aHpDYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location125 (_aHpDYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location126 (_aHpqccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location126 (_aHpqccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location126 (_aHpqccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location126 (_aHpqccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location126 (_aHpqccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location126 (_aHpqccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location126 (_aHpqccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location127 (_aHqRgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location127 (_aHqRgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location127 (_aHqRgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location127 (_aHqRgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location127 (_aHqRgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location127 (_aHqRgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location127 (_aHqRgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location128 (_aHq4kcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location128 (_aHq4kcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location128 (_aHq4kcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location128 (_aHq4kcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location128 (_aHq4kcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location128 (_aHq4kcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location128 (_aHq4kcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location129 (_aHrfocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location129 (_aHrfocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location129 (_aHrfocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location129 (_aHrfocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location129 (_aHrfocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location129 (_aHrfocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location129 (_aHrfocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location13 (_aGxgt8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location13 (_aGxgt8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location13 (_aGxgt8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location13 (_aGxgt8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location13 (_aGxgt8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location13 (_aGxgt8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location13 (_aGxgt8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location130 (_aHsGscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location130 (_aHsGscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location130 (_aHsGscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location130 (_aHsGscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location130 (_aHsGscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location130 (_aHsGscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location130 (_aHsGscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location131 (_aHstwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location131 (_aHstwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location131 (_aHstwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location131 (_aHstwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location131 (_aHstwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location131 (_aHstwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location131 (_aHstwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location132 (_aHtU0srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location132 (_aHtU0srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location132 (_aHtU0srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location132 (_aHtU0srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location132 (_aHtU0srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location132 (_aHtU0srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location132 (_aHtU0srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location133 (_aHt748rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location133 (_aHt748rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location133 (_aHt748rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location133 (_aHt748rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location133 (_aHt748rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location133 (_aHt748rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location133 (_aHt748rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location134 (_aHvKAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location134 (_aHvKAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location134 (_aHvKAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location134 (_aHvKAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location134 (_aHvKAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location134 (_aHvKAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location134 (_aHvKAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location135 (_aHvxEsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location135 (_aHvxEsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location135 (_aHvxEsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location135 (_aHvxEsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location135 (_aHvxEsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location135 (_aHvxEsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location135 (_aHvxEsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location136 (_aHwYIsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location136 (_aHwYIsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location136 (_aHwYIsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location136 (_aHwYIsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location136 (_aHwYIsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location136 (_aHwYIsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location136 (_aHwYIsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location137 (_aHw_MsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location137 (_aHw_MsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location137 (_aHw_MsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location137 (_aHw_MsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location137 (_aHw_MsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location137 (_aHw_MsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location137 (_aHw_MsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location138 (_aHxmQ8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location138 (_aHxmQ8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location138 (_aHxmQ8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location138 (_aHxmQ8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location138 (_aHxmQ8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location138 (_aHxmQ8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location138 (_aHxmQ8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location139 (_aHy0YMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location139 (_aHy0YMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location139 (_aHy0YMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location139 (_aHy0YMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location139 (_aHy0YMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location139 (_aHy0YMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location139 (_aHy0YMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location14 (_aGxgu8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location14 (_aGxgu8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location14 (_aGxgu8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location14 (_aGxgu8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location14 (_aGxgu8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location14 (_aGxgu8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location14 (_aGxgu8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location140 (_aHzbccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location140 (_aHzbccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location140 (_aHzbccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location140 (_aHzbccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location140 (_aHzbccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location140 (_aHzbccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location140 (_aHzbccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location141 (_aH0pksrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location141 (_aH0pksrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location141 (_aH0pksrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location141 (_aH0pksrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location141 (_aH0pksrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location141 (_aH0pksrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location141 (_aH0pksrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location142 (_aH13ssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location142 (_aH13ssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location142 (_aH13ssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location142 (_aH13ssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location142 (_aH13ssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location142 (_aH13ssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location142 (_aH13ssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location143 (_aH3s4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location143 (_aH3s4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location143 (_aH3s4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location143 (_aH3s4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location143 (_aH3s4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location143 (_aH3s4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location143 (_aH3s4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location144 (_aH47AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location144 (_aH47AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location144 (_aH47AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location144 (_aH47AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location144 (_aH47AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location144 (_aH47AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location144 (_aH47AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location145 (_aH6JIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location145 (_aH6JIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location145 (_aH6JIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location145 (_aH6JIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location145 (_aH6JIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location145 (_aH6JIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location145 (_aH6JIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location146 (_aH7XQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location146 (_aH7XQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location146 (_aH7XQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location146 (_aH7XQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location146 (_aH7XQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location146 (_aH7XQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location146 (_aH7XQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location147 (_aH8lYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location147 (_aH8lYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location147 (_aH8lYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location147 (_aH8lYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location147 (_aH8lYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location147 (_aH8lYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location147 (_aH8lYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location148 (_aH9zgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location148 (_aH9zgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location148 (_aH9zgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location148 (_aH9zgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location148 (_aH9zgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location148 (_aH9zgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location148 (_aH9zgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location149 (_aH_BocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location149 (_aH_BocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location149 (_aH_BocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location149 (_aH_BocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location149 (_aH_BocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location149 (_aH_BocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location149 (_aH_BocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location15 (_aGyHwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location15 (_aGyHwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location15 (_aGyHwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location15 (_aGyHwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location15 (_aGyHwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location15 (_aGyHwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location15 (_aGyHwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location150 (_aIAPwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location150 (_aIAPwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location150 (_aIAPwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location150 (_aIAPwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location150 (_aIAPwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location150 (_aIAPwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location150 (_aIAPwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location151 (_aIBd4srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location151 (_aIBd4srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location151 (_aIBd4srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location151 (_aIBd4srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location151 (_aIBd4srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location151 (_aIBd4srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location151 (_aIBd4srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location152 (_aICsAsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location152 (_aICsAsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location152 (_aICsAsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location152 (_aICsAsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location152 (_aICsAsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location152 (_aICsAsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location152 (_aICsAsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location153 (_aID6IsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location153 (_aID6IsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location153 (_aID6IsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location153 (_aID6IsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location153 (_aID6IsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location153 (_aID6IsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location153 (_aID6IsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location154 (_aIFvUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location154 (_aIFvUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location154 (_aIFvUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location154 (_aIFvUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location154 (_aIFvUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location154 (_aIFvUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location154 (_aIFvUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location155 (_aIG9ccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location155 (_aIG9ccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location155 (_aIG9ccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location155 (_aIG9ccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location155 (_aIG9ccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location155 (_aIG9ccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location155 (_aIG9ccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location156 (_aIILkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location156 (_aIILkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location156 (_aIILkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location156 (_aIILkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location156 (_aIILkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location156 (_aIILkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location156 (_aIILkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location157 (_aIJZscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location157 (_aIJZscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location157 (_aIJZscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location157 (_aIJZscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location157 (_aIJZscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location157 (_aIJZscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location157 (_aIJZscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location158 (_aIKn0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location158 (_aIKn0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location158 (_aIKn0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location158 (_aIKn0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location158 (_aIKn0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location158 (_aIKn0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location158 (_aIKn0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location159 (_aIL18srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location159 (_aIL18srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location159 (_aIL18srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location159 (_aIL18srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location159 (_aIL18srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location159 (_aIL18srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location159 (_aIL18srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location16 (_aGyHxcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location16 (_aGyHxcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location16 (_aGyHxcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location16 (_aGyHxcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location16 (_aGyHxcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location16 (_aGyHxcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location16 (_aGyHxcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location160 (_aINrIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location160 (_aINrIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location160 (_aINrIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location160 (_aINrIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location160 (_aINrIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location160 (_aINrIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location160 (_aINrIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location161 (_aIO5QcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location161 (_aIO5QcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location161 (_aIO5QcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location161 (_aIO5QcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location161 (_aIO5QcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location161 (_aIO5QcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location161 (_aIO5QcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location162 (_aIQHYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location162 (_aIQHYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location162 (_aIQHYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location162 (_aIQHYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location162 (_aIQHYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location162 (_aIQHYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location162 (_aIQHYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location163 (_aIRVgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location163 (_aIRVgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location163 (_aIRVgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location163 (_aIRVgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location163 (_aIRVgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location163 (_aIRVgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location163 (_aIRVgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location164 (_aITKscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location164 (_aITKscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location164 (_aITKscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location164 (_aITKscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location164 (_aITKscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location164 (_aITKscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location164 (_aITKscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location165 (_aIUY0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location165 (_aIUY0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location165 (_aIUY0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location165 (_aIUY0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location165 (_aIUY0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location165 (_aIUY0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location165 (_aIUY0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location166 (_aIWOAMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location166 (_aIWOAMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location166 (_aIWOAMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location166 (_aIWOAMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location166 (_aIWOAMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location166 (_aIWOAMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location166 (_aIWOAMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location167 (_aIYDMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location167 (_aIYDMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location167 (_aIYDMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location167 (_aIYDMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location167 (_aIYDMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location167 (_aIYDMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location167 (_aIYDMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location168 (_aIZ4YcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location168 (_aIZ4YcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location168 (_aIZ4YcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location168 (_aIZ4YcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location168 (_aIZ4YcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location168 (_aIZ4YcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location168 (_aIZ4YcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location169 (_aIbtkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location169 (_aIbtkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location169 (_aIbtkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location169 (_aIbtkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location169 (_aIbtkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location169 (_aIbtkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location169 (_aIbtkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location17 (_aGyHycrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location17 (_aGyHycrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location17 (_aGyHycrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location17 (_aGyHycrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location17 (_aGyHycrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location17 (_aGyHycrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location17 (_aGyHycrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location170 (_aIdiwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location170 (_aIdiwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location170 (_aIdiwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location170 (_aIdiwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location170 (_aIdiwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location170 (_aIdiwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location170 (_aIdiwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location171 (_aIew4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location171 (_aIew4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location171 (_aIew4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location171 (_aIew4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location171 (_aIew4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location171 (_aIew4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location171 (_aIew4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location172 (_aIgmEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location172 (_aIgmEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location172 (_aIgmEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location172 (_aIgmEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location172 (_aIgmEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location172 (_aIgmEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location172 (_aIgmEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location173 (_aIjCUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location173 (_aIjCUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location173 (_aIjCUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location173 (_aIjCUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location173 (_aIjCUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location173 (_aIjCUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location173 (_aIjCUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location174 (_aIk3gcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location174 (_aIk3gcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location174 (_aIk3gcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location174 (_aIk3gcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location174 (_aIk3gcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location174 (_aIk3gcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location174 (_aIk3gcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location175 (_aImFocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location175 (_aImFocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location175 (_aImFocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location175 (_aImFocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location175 (_aImFocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location175 (_aImFocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location175 (_aImFocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location176 (_aInTwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location176 (_aInTwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location176 (_aInTwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location176 (_aInTwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location176 (_aInTwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location176 (_aInTwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location176 (_aInTwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location177 (_aIn60srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location177 (_aIn60srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location177 (_aIn60srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location177 (_aIn60srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location177 (_aIn60srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location177 (_aIn60srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location177 (_aIn60srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location178 (_aIpI8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location178 (_aIpI8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location178 (_aIpI8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location178 (_aIpI8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location178 (_aIpI8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location178 (_aIpI8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location178 (_aIpI8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location179 (_aIqXEsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location179 (_aIqXEsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location179 (_aIqXEsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location179 (_aIqXEsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location179 (_aIqXEsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location179 (_aIqXEsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location179 (_aIqXEsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location18 (_aGyHzcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location18 (_aGyHzcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location18 (_aGyHzcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location18 (_aGyHzcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location18 (_aGyHzcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location18 (_aGyHzcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location18 (_aGyHzcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location180 (_aIrlMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location180 (_aIrlMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location180 (_aIrlMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location180 (_aIrlMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location180 (_aIrlMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location180 (_aIrlMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location180 (_aIrlMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location181 (_aIszUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location181 (_aIszUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location181 (_aIszUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location181 (_aIszUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location181 (_aIszUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location181 (_aIszUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location181 (_aIszUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location182 (_aIuBccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location182 (_aIuBccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location182 (_aIuBccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location182 (_aIuBccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location182 (_aIuBccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location182 (_aIuBccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location182 (_aIuBccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location183 (_aIvPkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location183 (_aIvPkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location183 (_aIvPkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location183 (_aIvPkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location183 (_aIvPkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location183 (_aIvPkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location183 (_aIvPkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location184 (_aIxEwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location184 (_aIxEwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location184 (_aIxEwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location184 (_aIxEwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location184 (_aIxEwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location184 (_aIxEwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location184 (_aIxEwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location185 (_aIxr0srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location185 (_aIxr0srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location185 (_aIxr0srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location185 (_aIxr0srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location185 (_aIxr0srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location185 (_aIxr0srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location185 (_aIxr0srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location186 (_aIy58crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location186 (_aIy58crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location186 (_aIy58crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location186 (_aIy58crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location186 (_aIy58crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location186 (_aIy58crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location186 (_aIy58crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location187 (_aIzhAsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location187 (_aIzhAsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location187 (_aIzhAsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location187 (_aIzhAsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location187 (_aIzhAsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location187 (_aIzhAsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location187 (_aIzhAsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location188 (_aI0vIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location188 (_aI0vIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location188 (_aI0vIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location188 (_aI0vIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location188 (_aI0vIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location188 (_aI0vIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location188 (_aI0vIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location189 (_aI1WMsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location189 (_aI1WMsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location189 (_aI1WMsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location189 (_aI1WMsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location189 (_aI1WMsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location189 (_aI1WMsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location189 (_aI1WMsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location19 (_aGyu08rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location19 (_aGyu08rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location19 (_aGyu08rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location19 (_aGyu08rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location19 (_aGyu08rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location19 (_aGyu08rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location19 (_aGyu08rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location190 (_aI2kUcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location190 (_aI2kUcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location190 (_aI2kUcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location190 (_aI2kUcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location190 (_aI2kUcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location190 (_aI2kUcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location190 (_aI2kUcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location191 (_aI3yccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location191 (_aI3yccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location191 (_aI3yccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location191 (_aI3yccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location191 (_aI3yccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location191 (_aI3yccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location191 (_aI3yccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location192 (_aI5AkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location192 (_aI5AkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location192 (_aI5AkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location192 (_aI5AkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location192 (_aI5AkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location192 (_aI5AkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location192 (_aI5AkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location193 (_aI6OssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location193 (_aI6OssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location193 (_aI6OssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location193 (_aI6OssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location193 (_aI6OssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location193 (_aI6OssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location193 (_aI6OssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location194 (_aI7c0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location194 (_aI7c0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location194 (_aI7c0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location194 (_aI7c0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location194 (_aI7c0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location194 (_aI7c0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location194 (_aI7c0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location195 (_aI8q8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location195 (_aI8q8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location195 (_aI8q8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location195 (_aI8q8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location195 (_aI8q8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location195 (_aI8q8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location195 (_aI8q8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location196 (_aI95EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location196 (_aI95EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location196 (_aI95EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location196 (_aI95EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location196 (_aI95EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location196 (_aI95EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location196 (_aI95EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location197 (_aI-gIsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location197 (_aI-gIsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location197 (_aI-gIsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location197 (_aI-gIsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location197 (_aI-gIsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location197 (_aI-gIsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location197 (_aI-gIsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location198 (_aI_uQsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location198 (_aI_uQsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location198 (_aI_uQsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location198 (_aI_uQsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location198 (_aI_uQsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location198 (_aI_uQsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location198 (_aI_uQsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location199 (_aJA8YcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location199 (_aJA8YcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location199 (_aJA8YcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location199 (_aJA8YcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location199 (_aJA8YcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location199 (_aJA8YcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location199 (_aJA8YcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location2 (_aGwSk8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location2 (_aGwSk8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location2 (_aGwSk8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location2 (_aGwSk8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location2 (_aGwSk8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location2 (_aGwSk8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location2 (_aGwSk8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location20 (_aGyu18rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location20 (_aGyu18rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location20 (_aGyu18rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location20 (_aGyu18rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location20 (_aGyu18rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location20 (_aGyu18rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location20 (_aGyu18rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location200 (_aJCKgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location200 (_aJCKgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location200 (_aJCKgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location200 (_aJCKgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location200 (_aJCKgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location200 (_aJCKgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location200 (_aJCKgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location201 (_aJDYocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location201 (_aJDYocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location201 (_aJDYocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location201 (_aJDYocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location201 (_aJDYocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location201 (_aJDYocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location201 (_aJDYocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location202 (_aJEmwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location202 (_aJEmwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location202 (_aJEmwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location202 (_aJEmwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location202 (_aJEmwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location202 (_aJEmwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location202 (_aJEmwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location203 (_aJF04crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location203 (_aJF04crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location203 (_aJF04crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location203 (_aJF04crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location203 (_aJF04crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location203 (_aJF04crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location203 (_aJF04crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location204 (_aJHDAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location204 (_aJHDAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location204 (_aJHDAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location204 (_aJHDAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location204 (_aJHDAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location204 (_aJHDAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location204 (_aJHDAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location205 (_aJIRIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location205 (_aJIRIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location205 (_aJIRIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location205 (_aJIRIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location205 (_aJIRIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location205 (_aJIRIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location205 (_aJIRIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location206 (_aJJfQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location206 (_aJJfQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location206 (_aJJfQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location206 (_aJJfQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location206 (_aJJfQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location206 (_aJJfQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location206 (_aJJfQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location207 (_aJLUccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location207 (_aJLUccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location207 (_aJLUccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location207 (_aJLUccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location207 (_aJLUccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location207 (_aJLUccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location207 (_aJLUccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location208 (_aJMikcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location208 (_aJMikcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location208 (_aJMikcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location208 (_aJMikcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location208 (_aJMikcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location208 (_aJMikcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location208 (_aJMikcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location209 (_aJNwssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location209 (_aJNwssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location209 (_aJNwssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location209 (_aJNwssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location209 (_aJNwssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location209 (_aJNwssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location209 (_aJNwssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location21 (_aGyu28rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location21 (_aGyu28rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location21 (_aGyu28rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location21 (_aGyu28rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location21 (_aGyu28rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location21 (_aGyu28rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location21 (_aGyu28rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location210 (_aJO-0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location210 (_aJO-0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location210 (_aJO-0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location210 (_aJO-0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location210 (_aJO-0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location210 (_aJO-0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location210 (_aJO-0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location211 (_aJQM8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location211 (_aJQM8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location211 (_aJQM8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location211 (_aJQM8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location211 (_aJQM8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location211 (_aJQM8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location211 (_aJQM8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location212 (_aJRbEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location212 (_aJRbEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location212 (_aJRbEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location212 (_aJRbEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location212 (_aJRbEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location212 (_aJRbEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location212 (_aJRbEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location213 (_aJSCIsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location213 (_aJSCIsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location213 (_aJSCIsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location213 (_aJSCIsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location213 (_aJSCIsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location213 (_aJSCIsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location213 (_aJSCIsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location214 (_aJTQQsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location214 (_aJTQQsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location214 (_aJTQQsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location214 (_aJTQQsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location214 (_aJTQQsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location214 (_aJTQQsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location214 (_aJTQQsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location215 (_aJUeYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location215 (_aJUeYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location215 (_aJUeYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location215 (_aJUeYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location215 (_aJUeYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location215 (_aJUeYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location215 (_aJUeYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location216 (_aJVsgsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location216 (_aJVsgsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location216 (_aJVsgsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location216 (_aJVsgsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location216 (_aJVsgsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location216 (_aJVsgsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location216 (_aJVsgsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location217 (_aJW6osrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location217 (_aJW6osrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location217 (_aJW6osrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location217 (_aJW6osrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location217 (_aJW6osrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location217 (_aJW6osrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location217 (_aJW6osrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location218 (_aJYIwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location218 (_aJYIwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location218 (_aJYIwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location218 (_aJYIwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location218 (_aJYIwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location218 (_aJYIwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location218 (_aJYIwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location219 (_aJZW4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location219 (_aJZW4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location219 (_aJZW4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location219 (_aJZW4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location219 (_aJZW4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location219 (_aJZW4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location219 (_aJZW4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location22 (_aGzV48rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location22 (_aGzV48rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location22 (_aGzV48rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location22 (_aGzV48rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location22 (_aGzV48rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location22 (_aGzV48rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location22 (_aGzV48rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location220 (_aJalAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location220 (_aJalAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location220 (_aJalAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location220 (_aJalAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location220 (_aJalAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location220 (_aJalAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location220 (_aJalAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location221 (_aJbzIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location221 (_aJbzIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location221 (_aJbzIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location221 (_aJbzIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location221 (_aJbzIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location221 (_aJbzIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location221 (_aJbzIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location222 (_aJcaMsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location222 (_aJcaMsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location222 (_aJcaMsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location222 (_aJcaMsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location222 (_aJcaMsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location222 (_aJcaMsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location222 (_aJcaMsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location223 (_aJdoUsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location223 (_aJdoUsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location223 (_aJdoUsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location223 (_aJdoUsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location223 (_aJdoUsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location223 (_aJdoUsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location223 (_aJdoUsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location224 (_aJe2ccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location224 (_aJe2ccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location224 (_aJe2ccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location224 (_aJe2ccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location224 (_aJe2ccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location224 (_aJe2ccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location224 (_aJe2ccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location225 (_aJgEkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location225 (_aJgEkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location225 (_aJgEkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location225 (_aJgEkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location225 (_aJgEkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location225 (_aJgEkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location225 (_aJgEkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location226 (_aJhSscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location226 (_aJhSscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location226 (_aJhSscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location226 (_aJhSscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location226 (_aJhSscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location226 (_aJhSscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location226 (_aJhSscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location227 (_aJig0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location227 (_aJig0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location227 (_aJig0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location227 (_aJig0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location227 (_aJig0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location227 (_aJig0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location227 (_aJig0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location228 (_aJju8MrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location228 (_aJju8MrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location228 (_aJju8MrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location228 (_aJju8MrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location228 (_aJju8MrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location228 (_aJju8MrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location228 (_aJju8MrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location229 (_aJkWAsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location229 (_aJkWAsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location229 (_aJkWAsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location229 (_aJkWAsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location229 (_aJkWAsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location229 (_aJkWAsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location229 (_aJkWAsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location23 (_aGzV58rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location23 (_aGzV58rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location23 (_aGzV58rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location23 (_aGzV58rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location23 (_aGzV58rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location23 (_aGzV58rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location23 (_aGzV58rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location230 (_aJlkIsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location230 (_aJlkIsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location230 (_aJlkIsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location230 (_aJlkIsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location230 (_aJlkIsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location230 (_aJlkIsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location230 (_aJlkIsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location231 (_aJmyQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location231 (_aJmyQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location231 (_aJmyQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location231 (_aJmyQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location231 (_aJmyQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location231 (_aJmyQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location231 (_aJmyQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location232 (_aJoAYcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location232 (_aJoAYcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location232 (_aJoAYcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location232 (_aJoAYcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location232 (_aJoAYcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location232 (_aJoAYcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location232 (_aJoAYcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location233 (_aJpOgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location233 (_aJpOgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location233 (_aJpOgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location233 (_aJpOgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location233 (_aJpOgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location233 (_aJpOgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location233 (_aJpOgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location234 (_aJqcocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location234 (_aJqcocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location234 (_aJqcocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location234 (_aJqcocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location234 (_aJqcocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location234 (_aJqcocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location234 (_aJqcocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location235 (_aJrDssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location235 (_aJrDssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location235 (_aJrDssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location235 (_aJrDssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location235 (_aJrDssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location235 (_aJrDssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location235 (_aJrDssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location236 (_aJsR0srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location236 (_aJsR0srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location236 (_aJsR0srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location236 (_aJsR0srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location236 (_aJsR0srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location236 (_aJsR0srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location236 (_aJsR0srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location237 (_aJtf8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location237 (_aJtf8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location237 (_aJtf8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location237 (_aJtf8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location237 (_aJtf8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location237 (_aJtf8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location237 (_aJtf8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location238 (_aJuuEsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location238 (_aJuuEsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location238 (_aJuuEsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location238 (_aJuuEsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location238 (_aJuuEsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location238 (_aJuuEsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location238 (_aJuuEsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location239 (_aJv8MsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location239 (_aJv8MsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location239 (_aJv8MsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location239 (_aJv8MsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location239 (_aJv8MsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location239 (_aJv8MsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location239 (_aJv8MsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location24 (_aGzV68rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location24 (_aGzV68rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location24 (_aGzV68rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location24 (_aGzV68rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location24 (_aGzV68rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location24 (_aGzV68rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location24 (_aGzV68rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location240 (_aJxKUsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location240 (_aJxKUsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location240 (_aJxKUsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location240 (_aJxKUsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location240 (_aJxKUsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location240 (_aJxKUsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location240 (_aJxKUsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location241 (_aJyYccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location241 (_aJyYccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location241 (_aJyYccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location241 (_aJyYccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location241 (_aJyYccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location241 (_aJyYccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location241 (_aJyYccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location242 (_aJzmkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location242 (_aJzmkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location242 (_aJzmkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location242 (_aJzmkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location242 (_aJzmkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location242 (_aJzmkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location242 (_aJzmkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location243 (_aJ00scrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location243 (_aJ00scrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location243 (_aJ00scrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location243 (_aJ00scrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location243 (_aJ00scrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location243 (_aJ00scrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location243 (_aJ00scrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location244 (_aJ2C0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location244 (_aJ2C0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location244 (_aJ2C0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location244 (_aJ2C0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location244 (_aJ2C0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location244 (_aJ2C0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location244 (_aJ2C0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location245 (_aJ3Q8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location245 (_aJ3Q8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location245 (_aJ3Q8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location245 (_aJ3Q8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location245 (_aJ3Q8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location245 (_aJ3Q8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location245 (_aJ3Q8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location246 (_aJ4fEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location246 (_aJ4fEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location246 (_aJ4fEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location246 (_aJ4fEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location246 (_aJ4fEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location246 (_aJ4fEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location246 (_aJ4fEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location247 (_aJ5tMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location247 (_aJ5tMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location247 (_aJ5tMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location247 (_aJ5tMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location247 (_aJ5tMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location247 (_aJ5tMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location247 (_aJ5tMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location248 (_aJ67UcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location248 (_aJ67UcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location248 (_aJ67UcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location248 (_aJ67UcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location248 (_aJ67UcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location248 (_aJ67UcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location248 (_aJ67UcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location249 (_aJ8JccrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location249 (_aJ8JccrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location249 (_aJ8JccrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location249 (_aJ8JccrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location249 (_aJ8JccrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location249 (_aJ8JccrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location249 (_aJ8JccrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location25 (_aGz888rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location25 (_aGz888rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location25 (_aGz888rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location25 (_aGz888rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location25 (_aGz888rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location25 (_aGz888rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location25 (_aGz888rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location250 (_aJ9XkcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location250 (_aJ9XkcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location250 (_aJ9XkcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location250 (_aJ9XkcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location250 (_aJ9XkcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location250 (_aJ9XkcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location250 (_aJ9XkcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location251 (_aJ-lscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location251 (_aJ-lscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location251 (_aJ-lscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location251 (_aJ-lscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location251 (_aJ-lscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location251 (_aJ-lscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location251 (_aJ-lscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location252 (_aJ_z0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location252 (_aJ_z0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location252 (_aJ_z0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location252 (_aJ_z0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location252 (_aJ_z0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location252 (_aJ_z0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location252 (_aJ_z0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location253 (_aKBB8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location253 (_aKBB8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location253 (_aKBB8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location253 (_aKBB8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location253 (_aKBB8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location253 (_aKBB8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location253 (_aKBB8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location254 (_aKCQEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location254 (_aKCQEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location254 (_aKCQEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location254 (_aKCQEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location254 (_aKCQEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location254 (_aKCQEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location254 (_aKCQEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location255 (_aKDeMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location255 (_aKDeMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location255 (_aKDeMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location255 (_aKDeMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location255 (_aKDeMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location255 (_aKDeMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location255 (_aKDeMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location26 (_aGz898rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location26 (_aGz898rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location26 (_aGz898rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location26 (_aGz898rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location26 (_aGz898rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location26 (_aGz898rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location26 (_aGz898rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location27 (_aG0kAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location27 (_aG0kAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location27 (_aG0kAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location27 (_aG0kAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location27 (_aG0kAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location27 (_aG0kAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location27 (_aG0kAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location28 (_aG0kBcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location28 (_aG0kBcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location28 (_aG0kBcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location28 (_aG0kBcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location28 (_aG0kBcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location28 (_aG0kBcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location28 (_aG0kBcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location29 (_aG0kCcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location29 (_aG0kCcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location29 (_aG0kCcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location29 (_aG0kCcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location29 (_aG0kCcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location29 (_aG0kCcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location29 (_aG0kCcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location3 (_aGwSl8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location3 (_aGwSl8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location3 (_aGwSl8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location3 (_aGwSl8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location3 (_aGwSl8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location3 (_aGwSl8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location3 (_aGwSl8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location30 (_aG1LE8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location30 (_aG1LE8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location30 (_aG1LE8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location30 (_aG1LE8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location30 (_aG1LE8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location30 (_aG1LE8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location30 (_aG1LE8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location31 (_aG1yIcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location31 (_aG1yIcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location31 (_aG1yIcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location31 (_aG1yIcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location31 (_aG1yIcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location31 (_aG1yIcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location31 (_aG1yIcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location32 (_aG1yJcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location32 (_aG1yJcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location32 (_aG1yJcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location32 (_aG1yJcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location32 (_aG1yJcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location32 (_aG1yJcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location32 (_aG1yJcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location33 (_aG2ZMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location33 (_aG2ZMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location33 (_aG2ZMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location33 (_aG2ZMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location33 (_aG2ZMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location33 (_aG2ZMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location33 (_aG2ZMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location34 (_aG2ZNcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location34 (_aG2ZNcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location34 (_aG2ZNcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location34 (_aG2ZNcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location34 (_aG2ZNcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location34 (_aG2ZNcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location34 (_aG2ZNcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location35 (_aG3AQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location35 (_aG3AQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location35 (_aG3AQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location35 (_aG3AQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location35 (_aG3AQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location35 (_aG3AQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location35 (_aG3AQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location36 (_aG3ARcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location36 (_aG3ARcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location36 (_aG3ARcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location36 (_aG3ARcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location36 (_aG3ARcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location36 (_aG3ARcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location36 (_aG3ARcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location37 (_aG3nUsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location37 (_aG3nUsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location37 (_aG3nUsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location37 (_aG3nUsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location37 (_aG3nUsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location37 (_aG3nUsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location37 (_aG3nUsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location38 (_aG3nVsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location38 (_aG3nVsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location38 (_aG3nVsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location38 (_aG3nVsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location38 (_aG3nVsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location38 (_aG3nVsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location38 (_aG3nVsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location39 (_aG4OY8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location39 (_aG4OY8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location39 (_aG4OY8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location39 (_aG4OY8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location39 (_aG4OY8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location39 (_aG4OY8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location39 (_aG4OY8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location4 (_aGwSm8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location4 (_aGwSm8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location4 (_aGwSm8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location4 (_aGwSm8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location4 (_aGwSm8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location4 (_aGwSm8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location4 (_aGwSm8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location40 (_aG4OZ8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location40 (_aG4OZ8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location40 (_aG4OZ8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location40 (_aG4OZ8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location40 (_aG4OZ8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location40 (_aG4OZ8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location40 (_aG4OZ8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location41 (_aG41c8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location41 (_aG41c8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location41 (_aG41c8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location41 (_aG41c8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location41 (_aG41c8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location41 (_aG41c8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location41 (_aG41c8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location42 (_aG5cgcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location42 (_aG5cgcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location42 (_aG5cgcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location42 (_aG5cgcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location42 (_aG5cgcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location42 (_aG5cgcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location42 (_aG5cgcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location43 (_aG5chcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location43 (_aG5chcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location43 (_aG5chcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location43 (_aG5chcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location43 (_aG5chcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location43 (_aG5chcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location43 (_aG5chcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location44 (_aG6DksrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location44 (_aG6DksrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location44 (_aG6DksrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location44 (_aG6DksrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location44 (_aG6DksrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location44 (_aG6DksrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location44 (_aG6DksrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location45 (_aG6qocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location45 (_aG6qocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location45 (_aG6qocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location45 (_aG6qocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location45 (_aG6qocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location45 (_aG6qocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location45 (_aG6qocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location46 (_aG6qpcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location46 (_aG6qpcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location46 (_aG6qpcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location46 (_aG6qpcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location46 (_aG6qpcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location46 (_aG6qpcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location46 (_aG6qpcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location47 (_aG7RssrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location47 (_aG7RssrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location47 (_aG7RssrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location47 (_aG7RssrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location47 (_aG7RssrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location47 (_aG7RssrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location47 (_aG7RssrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location48 (_aG74wcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location48 (_aG74wcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location48 (_aG74wcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location48 (_aG74wcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location48 (_aG74wcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location48 (_aG74wcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location48 (_aG74wcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location49 (_aG74xcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location49 (_aG74xcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location49 (_aG74xcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location49 (_aG74xcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location49 (_aG74xcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location49 (_aG74xcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location49 (_aG74xcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location5 (_aGwSn8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location5 (_aGwSn8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location5 (_aGwSn8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location5 (_aGwSn8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location5 (_aGwSn8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location5 (_aGwSn8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location5 (_aGwSn8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location50 (_aG8f08rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location50 (_aG8f08rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location50 (_aG8f08rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location50 (_aG8f08rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location50 (_aG8f08rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location50 (_aG8f08rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location50 (_aG8f08rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location51 (_aG9G4crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location51 (_aG9G4crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location51 (_aG9G4crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location51 (_aG9G4crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location51 (_aG9G4crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location51 (_aG9G4crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location51 (_aG9G4crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location52 (_aG9G5crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location52 (_aG9G5crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location52 (_aG9G5crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location52 (_aG9G5crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location52 (_aG9G5crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location52 (_aG9G5crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location52 (_aG9G5crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location53 (_aG9t88rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location53 (_aG9t88rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location53 (_aG9t88rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location53 (_aG9t88rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location53 (_aG9t88rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location53 (_aG9t88rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location53 (_aG9t88rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location54 (_aG-VAsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location54 (_aG-VAsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location54 (_aG-VAsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location54 (_aG-VAsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location54 (_aG-VAsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location54 (_aG-VAsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location54 (_aG-VAsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location55 (_aG-8EcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location55 (_aG-8EcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location55 (_aG-8EcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location55 (_aG-8EcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location55 (_aG-8EcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location55 (_aG-8EcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location55 (_aG-8EcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location56 (_aG-8FcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location56 (_aG-8FcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location56 (_aG-8FcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location56 (_aG-8FcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location56 (_aG-8FcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location56 (_aG-8FcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location56 (_aG-8FcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location57 (_aG_jI8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location57 (_aG_jI8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location57 (_aG_jI8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location57 (_aG_jI8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location57 (_aG_jI8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location57 (_aG_jI8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location57 (_aG_jI8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location58 (_aHAKMcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location58 (_aHAKMcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location58 (_aHAKMcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location58 (_aHAKMcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location58 (_aHAKMcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location58 (_aHAKMcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location58 (_aHAKMcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location59 (_aHAxQcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location59 (_aHAxQcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location59 (_aHAxQcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location59 (_aHAxQcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location59 (_aHAxQcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location59 (_aHAxQcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location59 (_aHAxQcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location6 (_aGwSo8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location6 (_aGwSo8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location6 (_aGwSo8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location6 (_aGwSo8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location6 (_aGwSo8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location6 (_aGwSo8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location6 (_aGwSo8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location60 (_aHAxRcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location60 (_aHAxRcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location60 (_aHAxRcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location60 (_aHAxRcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location60 (_aHAxRcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location60 (_aHAxRcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location60 (_aHAxRcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location61 (_aHBYU8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location61 (_aHBYU8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location61 (_aHBYU8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location61 (_aHBYU8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location61 (_aHBYU8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location61 (_aHBYU8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location61 (_aHBYU8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location62 (_aHB_Y8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location62 (_aHB_Y8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location62 (_aHB_Y8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location62 (_aHB_Y8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location62 (_aHB_Y8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location62 (_aHB_Y8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location62 (_aHB_Y8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location63 (_aHCmcsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location63 (_aHCmcsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location63 (_aHCmcsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location63 (_aHCmcsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location63 (_aHCmcsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location63 (_aHCmcsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location63 (_aHCmcsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location64 (_aHDNgsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location64 (_aHDNgsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location64 (_aHDNgsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location64 (_aHDNgsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location64 (_aHDNgsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location64 (_aHDNgsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location64 (_aHDNgsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location65 (_aHD0ksrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location65 (_aHD0ksrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location65 (_aHD0ksrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location65 (_aHD0ksrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location65 (_aHD0ksrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location65 (_aHD0ksrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location65 (_aHD0ksrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location66 (_aHEbocrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location66 (_aHEbocrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location66 (_aHEbocrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location66 (_aHEbocrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location66 (_aHEbocrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location66 (_aHEbocrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location66 (_aHEbocrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location67 (_aHFCscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location67 (_aHFCscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location67 (_aHFCscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location67 (_aHFCscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location67 (_aHFCscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location67 (_aHFCscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location67 (_aHFCscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location68 (_aHFpwcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location68 (_aHFpwcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location68 (_aHFpwcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location68 (_aHFpwcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location68 (_aHFpwcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location68 (_aHFpwcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location68 (_aHFpwcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location69 (_aHGQ0crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location69 (_aHGQ0crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location69 (_aHGQ0crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location69 (_aHGQ0crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location69 (_aHGQ0crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location69 (_aHGQ0crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location69 (_aHGQ0crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location7 (_aGw5osrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location7 (_aGw5osrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location7 (_aGw5osrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location7 (_aGw5osrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location7 (_aGw5osrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location7 (_aGw5osrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location7 (_aGw5osrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location70 (_aHG34crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location70 (_aHG34crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location70 (_aHG34crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location70 (_aHG34crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location70 (_aHG34crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location70 (_aHG34crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location70 (_aHG34crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location71 (_aHHe8crVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location71 (_aHHe8crVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location71 (_aHHe8crVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location71 (_aHHe8crVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location71 (_aHHe8crVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location71 (_aHHe8crVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location71 (_aHHe8crVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location72 (_aHIGAcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location72 (_aHIGAcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location72 (_aHIGAcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location72 (_aHIGAcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location72 (_aHIGAcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location72 (_aHIGAcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location72 (_aHIGAcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location73 (_aHItEcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location73 (_aHItEcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location73 (_aHItEcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location73 (_aHItEcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location73 (_aHItEcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location73 (_aHItEcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location73 (_aHItEcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location74 (_aHItFcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location74 (_aHItFcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location74 (_aHItFcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location74 (_aHItFcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location74 (_aHItFcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location74 (_aHItFcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location74 (_aHItFcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location75 (_aHJUI8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location75 (_aHJUI8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location75 (_aHJUI8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location75 (_aHJUI8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location75 (_aHJUI8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location75 (_aHJUI8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location75 (_aHJUI8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location76 (_aHJ7McrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location76 (_aHJ7McrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location76 (_aHJ7McrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location76 (_aHJ7McrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location76 (_aHJ7McrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location76 (_aHJ7McrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location76 (_aHJ7McrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location77 (_aHJ7NcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location77 (_aHJ7NcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location77 (_aHJ7NcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location77 (_aHJ7NcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location77 (_aHJ7NcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location77 (_aHJ7NcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location77 (_aHJ7NcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location78 (_aHKiQ8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location78 (_aHKiQ8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location78 (_aHKiQ8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location78 (_aHKiQ8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location78 (_aHKiQ8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location78 (_aHKiQ8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location78 (_aHKiQ8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location79 (_aHLJU8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location79 (_aHLJU8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location79 (_aHLJU8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location79 (_aHLJU8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location79 (_aHLJU8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location79 (_aHLJU8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location79 (_aHLJU8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location8 (_aGw5psrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location8 (_aGw5psrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location8 (_aGw5psrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location8 (_aGw5psrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location8 (_aGw5psrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location8 (_aGw5psrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location8 (_aGw5psrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location80 (_aHLwY8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location80 (_aHLwY8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location80 (_aHLwY8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location80 (_aHLwY8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location80 (_aHLwY8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location80 (_aHLwY8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location80 (_aHLwY8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location81 (_aHMXc8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location81 (_aHMXc8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location81 (_aHMXc8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location81 (_aHMXc8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location81 (_aHMXc8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location81 (_aHMXc8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location81 (_aHMXc8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location82 (_aHM-gcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location82 (_aHM-gcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location82 (_aHM-gcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location82 (_aHM-gcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location82 (_aHM-gcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location82 (_aHM-gcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location82 (_aHM-gcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location83 (_aHM-hcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location83 (_aHM-hcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location83 (_aHM-hcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location83 (_aHM-hcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location83 (_aHM-hcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location83 (_aHM-hcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location83 (_aHM-hcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location84 (_aHNlk8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location84 (_aHNlk8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location84 (_aHNlk8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location84 (_aHNlk8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location84 (_aHNlk8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location84 (_aHNlk8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location84 (_aHNlk8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location85 (_aHOMo8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location85 (_aHOMo8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location85 (_aHOMo8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location85 (_aHOMo8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location85 (_aHOMo8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location85 (_aHOMo8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location85 (_aHOMo8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location86 (_aHOzscrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location86 (_aHOzscrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location86 (_aHOzscrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location86 (_aHOzscrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location86 (_aHOzscrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location86 (_aHOzscrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location86 (_aHOzscrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location87 (_aHPawMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location87 (_aHPawMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location87 (_aHPawMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location87 (_aHPawMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location87 (_aHPawMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location87 (_aHPawMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location87 (_aHPawMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location88 (_aHPaxMrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location88 (_aHPaxMrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location88 (_aHPaxMrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location88 (_aHPaxMrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location88 (_aHPaxMrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location88 (_aHPaxMrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location88 (_aHPaxMrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location89 (_aHQB08rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location89 (_aHQB08rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location89 (_aHQB08rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location89 (_aHQB08rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location89 (_aHQB08rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location89 (_aHQB08rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location89 (_aHQB08rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location9 (_aGw5qsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location9 (_aGw5qsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location9 (_aGw5qsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location9 (_aGw5qsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location9 (_aGw5qsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location9 (_aGw5qsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location9 (_aGw5qsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location90 (_aHQo4srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location90 (_aHQo4srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location90 (_aHQo4srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location90 (_aHQo4srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location90 (_aHQo4srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location90 (_aHQo4srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location90 (_aHQo4srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location91 (_aHRP8srVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location91 (_aHRP8srVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location91 (_aHRP8srVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location91 (_aHRP8srVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location91 (_aHRP8srVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location91 (_aHRP8srVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location91 (_aHRP8srVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location92 (_aHR3AcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location92 (_aHR3AcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location92 (_aHR3AcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location92 (_aHR3AcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location92 (_aHR3AcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location92 (_aHR3AcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location92 (_aHR3AcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location93 (_aHR3BcrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location93 (_aHR3BcrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location93 (_aHR3BcrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location93 (_aHR3BcrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location93 (_aHR3BcrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location93 (_aHR3BcrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location93 (_aHR3BcrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location94 (_aHSeE8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location94 (_aHSeE8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location94 (_aHSeE8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location94 (_aHSeE8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location94 (_aHSeE8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location94 (_aHSeE8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location94 (_aHSeE8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location95 (_aHTFI8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location95 (_aHTFI8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location95 (_aHTFI8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location95 (_aHTFI8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location95 (_aHTFI8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location95 (_aHTFI8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location95 (_aHTFI8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location96 (_aHTsM8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location96 (_aHTsM8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location96 (_aHTsM8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location96 (_aHTsM8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location96 (_aHTsM8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location96 (_aHTsM8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location96 (_aHTsM8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location97 (_aHUTQ8rVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location97 (_aHUTQ8rVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location97 (_aHUTQ8rVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location97 (_aHUTQ8rVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location97 (_aHUTQ8rVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location97 (_aHUTQ8rVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location97 (_aHUTQ8rVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location98 (_aHU6UsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location98 (_aHU6UsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location98 (_aHU6UsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location98 (_aHU6UsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location98 (_aHU6UsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location98 (_aHU6UsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location98 (_aHU6UsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
characteristicType('Location99 (_aHVhYsrVEeuB5qhd4oQ7PA)').
characteristicTypeValue('Location99 (_aHVhYsrVEeuB5qhd4oQ7PA)', 'Outside (_kF3NENVeEeqRbpVUMz5XAQ)', 0).
characteristicTypeValue('Location99 (_aHVhYsrVEeuB5qhd4oQ7PA)', 'MeetingRoom (_lwXnENVeEeqRbpVUMz5XAQ)', 1).
characteristicTypeValue('Location99 (_aHVhYsrVEeuB5qhd4oQ7PA)', 'Laboratory (_marvYNVeEeqRbpVUMz5XAQ)', 2).
characteristicTypeTrust('Location99 (_aHVhYsrVEeuB5qhd4oQ7PA)', 'trust_low (_drJM4MhEEeu_Wf8wLuiSoQ)', 0).
characteristicTypeTrust('Location99 (_aHVhYsrVEeuB5qhd4oQ7PA)', 'trust_mid (_fzA4UMhEEeu_Wf8wLuiSoQ)', 1).
characteristicTypeTrust('Location99 (_aHVhYsrVEeuB5qhd4oQ7PA)', 'trust_high (_g6JfgMhEEeu_Wf8wLuiSoQ)', 2).
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
