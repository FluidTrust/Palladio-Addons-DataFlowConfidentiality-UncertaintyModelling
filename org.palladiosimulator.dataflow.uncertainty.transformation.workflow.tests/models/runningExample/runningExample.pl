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
characteristicType('ReadAccess (_cC9Ph8dyEeuG_ImeU_5DqQ)').
characteristicTypeValue('ReadAccess (_cC9Ph8dyEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 0).
characteristicTypeValue('ReadAccess (_cC9Ph8dyEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 1).
characteristicTypeValue('ReadAccess (_cC9Ph8dyEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 2).
characteristicTypeTrust('ReadAccess (_cC9Ph8dyEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', 0).
characteristicTypeTrust('ReadAccess (_cC9Ph8dyEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', 1).
characteristicTypeTrust('ReadAccess (_cC9Ph8dyEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', 2).
characteristicType('UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)').
characteristicTypeValue('UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 0).
characteristicTypeValue('UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 1).
characteristicTypeValue('UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 2).
characteristicTypeTrust('UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', 0).
characteristicTypeTrust('UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', 1).
characteristicTypeTrust('UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', 2).

% =====
% Nodes
% =====
% Actor Scientist
actor('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)').
nodeCharacteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
inputPin('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'input (_ewGOYMd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)').
outputPin('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)').
characteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)').
characteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
characteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)').
characteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)').
characteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
characteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)').
characteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)').
characteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
characteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)').

% Actor Worker
actor('Worker (_EcA99cdzEeuG_ImeU_5DqQ)').
nodeCharacteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
inputPin('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'input (_ewGOYMd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)').
outputPin('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)').
characteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)').
characteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
characteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)').
characteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)').
characteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
characteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)').
characteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)').
characteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
characteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)').

% Actor Visitor
actor('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)').
nodeCharacteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)').
inputPin('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'input (_ewGOYMd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)').
outputPin('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)').
characteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)').
characteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
characteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)').
characteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)').
characteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
characteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)').
characteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)').
characteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
characteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'output (_fL6Aocd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', [], _) :-
	nodeCharacteristic('Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)').

% Store LaboratoryDB
store('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)').
nodeCharacteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'ReadAccess (_cC9Ph8dyEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)').
inputPin('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)').
outputPin('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'output (_OtJaEcd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)').
characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'output (_OtJaEcd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'output (_OtJaEcd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'output (_OtJaEcd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'output (_OtJaEcd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'output (_OtJaEcd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'output (_OtJaEcd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'output (_OtJaEcd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'output (_OtJaEcd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'output (_OtJaEcd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'input (_Nr5_gMd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S0, VISITED).

% Process ReadDB
process('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)').
inputPin('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)').
outputPin('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)').
characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Outside (_XhorUMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'MeetingRoom (_ZB91oMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_low (_mvvNMMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_mid (_oZ3MsMdwEeuG_ImeU_5DqQ)', S0, VISITED).
characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S, VISITED) :-
	inputFlow('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', _, F0, VISITED),
	S0 = [F0 | _],
	S = [S0],
	characteristic('ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)', 'Laboratory (_a28aQMdwEeuG_ImeU_5DqQ)', 'trust_high (_rHkJEMdwEeuG_ImeU_5DqQ)', S0, VISITED).

% =====
% Edges
% =====
dataflow('DB2Process (_9TgGWcd2EeuG_ImeU_5DqQ)', 'LaboratoryDB (_XVqvFsd0EeuG_ImeU_5DqQ)', 'output (_OtJaEcd0EeuG_ImeU_5DqQ_XVqvFsd0EeuG_ImeU_5DqQ)', 'ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'input (_oZGQUMdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)').
dataflow('Process2Scientist (_mlC7-Md3EeuG_ImeU_5DqQ)', 'ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'Scientist (__sRRUMdyEeuG_ImeU_5DqQ)', 'input (_ewGOYMd2EeuG_ImeU_5DqQ__sRRUMdyEeuG_ImeU_5DqQ)').
dataflow('Process2Worker (_sPR66cd3EeuG_ImeU_5DqQ)', 'ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'Worker (_EcA99cdzEeuG_ImeU_5DqQ)', 'input (_ewGOYMd2EeuG_ImeU_5DqQ_EcA99cdzEeuG_ImeU_5DqQ)').
dataflow('Process2Visitor (_1ZmVacd3EeuG_ImeU_5DqQ)', 'ReadDB (_4pQPp8d0EeuG_ImeU_5DqQ)', 'output (_rNx-ccdzEeuG_ImeU_5DqQ_4pQPp8d0EeuG_ImeU_5DqQ)', 'Visitor (_Ibu71cdzEeuG_ImeU_5DqQ)', 'input (_ewGOYMd2EeuG_ImeU_5DqQ_Ibu71cdzEeuG_ImeU_5DqQ)').
