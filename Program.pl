% Anne Benedicte Abildgaard Ejsing 
% aejsin16@student.aau.dk

% Route facts
route("Aalborg", "Aarhus", 100, "motorway", 3).
route("Aarhus", "Horsens", 50, "motorway", 2).
route("Aarhus", "Silkeborg", 20, "motorway", 2).
route("Silkeborg", "Horsens", 20, "motorway", 2).
route("Horsens", "Vejle", 30, "paved", 1).
route("Vejle", "Juelsminde", 10, "gravel", 1).

% Vehicle facts
vehicle("Annes Up", "Car").
vehicle("Lars' C1", "Car").
vehicle("Taxi 1", "Taxi").
vehicle("Taxi 2", "Taxi").
vehicle("Den store bus", "Bus").
vehicle("Den lille bus", "Bus").
vehicle("Blå cykel", "Bicycle").
vehicle("Rød cykel", "Bicycle").

% Traveller facts
traveller("Anne", ["Rød cykel", "Annes Up"]).
traveller("Lars", ["Rød cykel"]).
traveller("Casper",["Taxi 1", "Den lille bus"]).
traveller("Mark", "Taxi 2").

% Condition facts
condition("Car", ["paved", "gravel", "motorway"]).
condition("Taxi", ["paved", "gravel", "motorway"]).
condition("Bus", ["paved", "motorway"]).
condition("Bicycle", ["paved", "gravel"]).

% These two rules assures all routes are bidirectional
connection(X,Y,L,B,T) :- route(X,Y,L,B,T).
connection(X,Y,L,B,T) :- route(Y,X,L,B,T).

% The purpose of the pathBase rule is to instantiate the
% history needed in pathCond with the element of X. 
pathBase(X, Y, Length, C, Time, Res) :-
    pathCond(X, Y, Length, C, Time, [X], Res).

% The pathCond rules computes the transitive closure of
% routes. The "cond"-part of the name indicates that a
% route can only be taken if consists of the road condi-
% tions specified in Conditions.
pathCond(X, Y, Length, Conditions, Time, History, Res) :- 
    connection(X, Y, Length, C, Time),
    member(C, Conditions),
    append(History, [Y], Res).
pathCond(X, Y, Length, Conditions, Time, History, Res) :- 
    connection(X, Z, Length1, C, Time1),
    member(C, Conditions),
    not(member(Z, History)),
    append(History, [Z], New_History),
    pathCond(Z, Y, Length2, Conditions, Time2, New_History, Res),
    plus(Length1, Length2, Length),
    plus(Time1, Time2, Time).


% ------------------------------------------------------------------------
% 
% The program must be able to return routes in the form of lists and should 
% be able to deal with queries such as (select at least some of these)

% ------------------------------------------------------------------------
% Find a route between two towns that a given person can travel by, if 
% possible
% ------------------------------------------------------------------------
person_travel(X,Y, PersonName, History) :- 
    vehicles([PersonName], Vehicles),
    conditions(Vehicles, Conditions),
    pathBase(X, Y, _, Conditions, _, History).

% ------------------------------------------------------------------------
% Find a route that passes though towns from a given list, if possible. 
% ------------------------------------------------------------------------
through_towns(PassThrough, History) :- 
    pathBase(_, _, _, ["paved", "gravel", "motorway"], _, History),
    contains(PassThrough, History).

 
% ------------------------------------------------------------------------
% Find a route that can be used a list of travellers
% ------------------------------------------------------------------------

% This query handles when there are more than 5 people.
list_travellers(People, History) :-
    length(People, NumberOfPeople),
    NumberOfPeople > 5,
    vehicles(People, Vehicles),
    can_go_together(Vehicles, NumberOfPeople),
    conditions(Vehicles, Conditions),
    pathBase(_, _, _, Conditions, _, History).

% This query handles when there are 5 or less people.
list_travellers(People, History) :-
    length(People, NumberOfPeople),
    NumberOfPeople =< 5,
    vehicles(People, Vehicles),
    conditions(Vehicles, Conditions),
    pathBase(_, _, _, Conditions, _, History).

% If someone from the group of travellers owns a bus, they can go together
can_go_together(Vehicles, _) :-
    member("Bus", Vehicles).

% If all travellers own bicycles, they can go together
can_go_together(Vehicles, NumberOfPeople) :-
    aggregate(count, member("Bicycle", Vehicles), NumberOfBicycles),
    NumberOfBicycles >= NumberOfPeople.

% If enough travellers own cars, they can go together
can_go_together(Vehicles, NumberOfPeople) :-
    aggregate(count, member("Car", Vehicles), NumberOfCars),
    (NumberOfPeople / 4) =< NumberOfCars.

% ------------------------------------------------------------------------
% Find a route that uses only certain road conditions.
% ------------------------------------------------------------------------
certain_roads(Conditions, History) :- 
    pathBase(_, _, _, Conditions, _, History).


% ------------------------------------------------------------------------
% Find the shortest route between two given towns
% ------------------------------------------------------------------------
shortest(X, Y, History, Result) :-
    aggregate_all(min(Length, History), 
                  pathBase(X, Y, Length, ["paved", "gravel", "motorway"], _, History), 
                  min(Result, History)).


% ------------------------------------------------------------------------
% Find the fastest route between two given towns
% ------------------------------------------------------------------------
fastest(X, Y, History, Result) :-
    aggregate_all(min(Time, History), 
                  pathBase(X, Y, _, ["paved", "gravel", "motorway"], Time, History), 
                  min(Result, History)).


% ------------------------------------------------------------------------
% Tell us, given a traveller, which means of transportation (if any) will 
% allow them to get from a to b
% ------------------------------------------------------------------------

% In this rule we first get all vehicles of the specific person. Then the 
% first findall creates a list of road conditions that are valid for each
% vehicle. E.g., if the vehicles are bicycle and car, it would be
% [["paved", "gravel"], ["paved", "gravel", "motorway"]]. The second findall
% uses the helper rule and finds all vehicles that will allow the person to 
% get from X to Y.
transport_means(X, Y, PersonName, AllowedVehicles) :- 
    vehicles([PersonName], Vehicles),
    findall(Conds,
            type2conditions(Vehicles, Conds),
            Result),
    findall(Vehicle,
            helper(Result, Vehicles, X, Y, Vehicle),
            Res),
    % Sort also acts as a distinct.
    sort(Res, AllowedVehicles).

helper(Conditions, Vehicles, X, Y, Vehicle) :-
    % Get a list of conditions from the Conditions list.
    member(Condition, Conditions),
    % Get the index of the Condition from the Conditions list.
    nth0(Index, Conditions, Condition),
    % Get the Vehicle from the index found above from the Vehicles list.
    nth0(Index, Vehicles, Vehicle),
    % Find a path which uses the road conditions given in Condition.
    pathBase(X, Y, _, Condition, _, _).

% ------------------------------------------------------------------------
% HELPER RULES
% ------------------------------------------------------------------------

% Describes if all elements of a list is contained in another list.
% Order dose not matter. 
contains([],_).
contains([X|XS], List) :- member(X, List), contains(XS, List).

% Describes the vehicles corresponding to the people
vehicles(People, Flattend) :-
    findall(Vehicles,
            (People, Vehicles),
            Result),
    flatten(Result, Flattend).

% Describes the road conditions corresponding to the vehicles
conditions(Vehicles, Conditions) :-
   	% Sort also acts as a distinct.
    sort(Vehicles, Distinct),
    vehicles2conditions(Distinct, Conditions).

% Describes the conditions corresponding to the vehicles
vehicles2conditions(Vehicle, Distinct) :-
    findall(Conds,
            type2conditions(Vehicle, Conds),
            Result),
    flatten(Result, Flattend),
    % Sort also acts as a distinct.
    sort(Flattend, Distinct).

% Describes the conditions from the type of the road
type2conditions(Type, Conditions) :-
    member(X, Type),
    condition(X, Conditions).

% Describes the vehicles corresponding to the people
person2vehicles(People, Result) :-
    member(X, People),
    traveller(X, Vehicle),
    findall(Type,
            vehicle2type(Vehicle, Type),
            Result).

% Describes the type of the of road from the vehicle
vehicle2type(V, Type) :-
    member(X, V),
    vehicle(X, Type).