(* ::Package:: *)

BeginPackage["package`main`"];
 
threeUPP::usage = "The algorithm takes the input which is either the directory of the text file contaning the set of characters or the set of characters and output whether there is the unique tree for that set of characters."
 
Begin["`Private`"]

FormatCharacters[characters_] := DeleteDuplicates[(StringJoin /@
    SortBy[{Sort[Characters[#[[1]]]], Sort[Characters[#[[2]]]],
    Sort[Characters[#[[3]]]]}, First]) & /@ characters];
 
Read3StateCharacters[rawcharacters_] := Module[{characters = {}, list = {}, c},
        For[i = 1, i <= Length[rawcharacters], i++,
            If[! StringMatchQ[rawcharacters[[i]],
                              RegularExpression[
                                                "[A-Za-z1-9]+(\||(\\s)*)[A-Za-z1-9]+(\||(\\s)*)[A-Za-z1-9]+"]]\
               , Print["Illigal 3-state characters (must be in form A|B|C): " <>
                       rawcharacters[[i]]]; Return[{}]];
            c = StringCases[rawcharacters[[i]],
                            RegularExpression["[A-Za-z1-9]+"]];
            AppendTo[list, Sort[Characters[c[[1]] <> c[[2]] <> c[[3]]]]];
            AppendTo[characters, c];
            ];
        If[list[[1]] != DeleteDuplicates[list[[1]]],
           Print["Illigal characters (can't duplicate): " <>
                 rawcharacters[[1]]]; Return[{}]];
        For[i = 2, i <= Length[list], i++,
            If[list[[i]] != DeleteDuplicates[list[[i]]],
               Print[
                     "Illigal characters (can't duplicate): " <>
                     rawcharacters[[i]]]; Return[{}]];
            If[list[[i]] != list[[1]],
               Print["Illigal characters (different labels): " <>
                     rawcharacters[[1]] <> " and " <> rawcharacters[[i]]];
               Return[{}]];
            ];
        FormatCharacters[characters]
        ];
 
 
 Convert3StateCharactersToSplits[characters_] := Module[{splits, f},
                                                        f[s_] :=
                                                        StringJoin[#] & /@
                                                        SortBy[{Sort[Characters[s[[1]]]], Sort[Characters[s[[2]]]]},
                                                               First];
                                                        splits = {f[{#[[1]], #[[2]] <> #[[3]]}],
                                                            f[{#[[2]], #[[1]] <> #[[3]]}],
                                                            f[{#[[3]], #[[1]] <> #[[2]]}]} & /@ characters;
                                                        splits
                                                        ];


 Convert3StateCharactersToTable[characters_] := Module[{table = {}, result = {}, s = {}},
        table = Characters[#] & /@ # & /@ characters;
        s = Take[Characters["abcdefghijklmnopqrstuvwxyz"],
                 Length[Union @@ table[[1]]]];
        For[i = 1, i <= Length[table], i++,
            AppendTo[result, Position[table[[i]], #][[1, 1]] & /@ s]];
        Transpose[result]
        ];
 
 
 ConvertTableTo3StateCharacters[matrix_] := Module[{characters = {}, s = Take[Characters["abcdefghijklmnopqrstuvwxyz"], Length[matrix]], M = Transpose[matrix],         firstState = {}, secondState = {}, thirdState = {}},
        firstState = s[[#[[1]]]] & /@ # & /@ (Position[#, 1] & /@ M);
        secondState = s[[#[[1]]]] & /@ # & /@ (Position[#, 2] & /@ M);
        thirdState = s[[#[[1]]]] & /@ # & /@ (Position[#, 3] & /@ M);
        characters =
        StringJoin[ firstState[[#]]] <> "|" <>
        StringJoin[ secondState[[#]]] <> "|" <>
        StringJoin[ thirdState[[#]]] & /@ Range[Length[M]];
        characters
        ];
 
 ConvertTableToSplits[matrix_] := Convert3StateCharactersToSplits[
                                 Read3StateCharacters[ConvertTableTo3StateCharacters[matrix]]];
 
 NotCompatible[s1_, s2_] := Intersection[Characters[s1[[1]]], Characters[ s2[[1]]]] != {} &&
       Intersection[Characters[s1[[1]]], Characters[ s2[[2]]]] != {} &&
       Intersection[Characters[s1[[2]]], Characters[ s2[[1]]]] != {} &&
       Intersection[Characters[s1[[2]]], Characters[ s2[[2]]]] != {};
 
EqualCharacterQ[c1_, c2_] := FormatCharacters[{c1}] == FormatCharacters[{c2}];
 
SortCharacter[characters_] := SortBy[characters, First];
 
DependentStatewithWitness[chars_List] := Module[{result = {}, witness = {}, size = Length[chars], f, i, j},
        DependentStateH[c1_, c2_] :=
        Module[{g, adj, position = {}, edges = {}, m, n},
               For[m = 1, m <= 3, m++,
                   For[n = 1, n <= 3, n++,
                       If[
                          Intersection[Characters[c1[[m]]],
                                       Characters[ c2[[n]]]] != {}, AppendTo[edges, {m, n + 3}]];
                       ]];
               g = Graph[
                         MapThread[
                                   UndirectedEdge, {edges[[All, 1]], edges[[All, 2]]}]];
               For[m = 1, m <= 6, m++,
                   If[VertexDegree[g, m] > 1,
                      adj = VertexDegree[g, #] & /@ AdjacencyList[g, m];
                      If[Length[Select[adj, # > 1 &]] >= 2,
                         AppendTo[position, If[m > 3, {2, m - 3}, {1, m}]]];
                      ];
                   ];
               position
               ];
        For[i = 1, i <= size - 1, i++,
            For[j = i + 1, j <= size, j++,
                f[{a_, b_}] := If[a == 1, {i, b}, {j, b}];
                result =
                Join[result,
                     f[#] & /@ DependentStateH[chars[[i]], chars[[j]]]];
                witness =
                Join[witness,
                     If[#[[1]] == 1, j , i] & /@
                     DependentStateH[chars[[i]], chars[[j]]]];
                ]];
        {result, witness}
        ];
 
DependentState[chars_List] := SortBy[DeleteDuplicates[DependentStatewithWitness[chars][[1]]],
        First];
 
 
PoppingTreeHelper[splits_] := Module[{label, tree = PathGraph[{1, 2}], A, B, id = 3, i, split, v, v0,
                                          v1, v2, l1, l2, adjacent, tempgraph, s, labelcomponents, color},
                                      If[Length[splits] == 0, Return[{{}, {}}]];
                                      label = splits[[1]];
                                      For[split = 2, split <= Length[splits], split++,
                                          A = splits[[split]][[1]];
                                          B = splits[[split]][[2]];
                                          For[i = 1, i <= Length[VertexList[tree]], i++,
                                              v0 = VertexList[tree][[i]];
                                              
                                              labelcomponents = StringJoin[#] & /@ (label[[#]]
                                                                                    & /@
                                                                                    Map[VertexIndex[tree, #] &,
                                                                                        ConnectedComponents[VertexDelete[tree, v0]], {2}]);
                                              
                                              color = ! (Length[Intersection[Characters[#], Characters[A]]] >
                                                         0 &&
                                                         
                                                         Length[Intersection[Characters[#], Characters[B]]] >
                                                         0)  & /@ labelcomponents;
                                              
                                              If[Fold[And, True, color] == True, Break[]];
                                              v0
                                              ];
                                          
                                          adjacent = AdjacencyList[tree, v0];
                                          tempgraph = VertexDelete[tree, v0];
                                          l1 =
                                          StringJoin[
                                                     Intersection[Characters[label[[VertexIndex[tree, v0]]]],
                                                                  Characters[A]]];
                                          l2 =
                                          StringJoin[
                                                     Intersection[Characters[label[[VertexIndex[tree, v0]]]],
                                                                  Characters[B]]];
                                          v1 = id++;
                                          v2 = id++;
                                          tree = VertexAdd[tree, v1];
                                          tree = VertexAdd[tree, v2];
                                          AppendTo[label, l1];
                                          AppendTo[label, l2];
                                          
                                          For[i = 1, i <= Length[adjacent], i++, v = adjacent[[i]];
                                              s =
                                              labelcomponents[[
                                                               Position[ConnectedComponents[tempgraph], v, 2][[1]][[1]]]];
                                              If[Length[Intersection[Characters[s], Characters[A]]] > 0 ,
                                                 tree = EdgeAdd[tree, v1 <-> v],  
                                                 tree = EdgeAdd[tree, v2 <-> v]];
                                              ];
                                          
                                          tree = EdgeAdd[tree, v1 <-> v2];
                                          label = Delete[label, VertexIndex[tree, v0]];
                                          tree = VertexDelete[tree, v0];
                                          ];
                                      {AdjacencyGraph[AdjacencyMatrix[tree]], label}
                                      ];
 

 PoppingTree[splits_] := Module[{tree, label},
                                tree = PoppingTreeHelper[splits][[1]];
                                label = PoppingTreeHelper[splits][[2]];
                                SetProperty[tree, 
                                            VertexLabels -> Table[i -> label[[i]], {i, Length[label]}]]
                                ];
 
threeUPPHelper[characters_] := Module[{H = {}, E = {}, E1 = {}, C = characters, size = Length[characters], splits, ds, dsc, states, witness, i,
        j, pos, inc = {}, choice1, choice2},
        splits = Convert3StateCharactersToSplits[C];
        witness = DependentStatewithWitness[C];
        ds = SortBy[DeleteDuplicates[witness[[1]]], First];
        dsc = ds[[All, 1]];
        states = Select[Split[dsc], Length[#] > 1 &];
        If[Length[states] > 0,
           states = 
           DeleteDuplicates[
                            Select[witness[[1]], #[[1]] == states[[1, 1]] &]];
           i = First[Flatten[Position[witness[[1]], states[[1]]]]];
           j = Last[Flatten[Position[witness[[1]], states[[2]]]]];
           witness = witness[[2]];
           Print[
                 "Not compatible, the subset of characters " <> 
                 ToString[
                          DeleteDuplicates[{characters[[states[[1, 1]]]], 
                     characters[[witness[[i]]]], characters[[witness[[j]]]]}]] <> 
                 " is incompatible."];
           Return[{characters[[states[[1, 1]]]], characters[[witness[[i]]]], 
            characters[[witness[[j]]]]}];
           ];
        
        E = Join @@ (Delete[splits[[#[[1]]]], #[[2]]] & /@ ds);
        H = Delete[splits, {#} & /@ dsc];
        C = Delete[C, {#} & /@ dsc];
        IncompatiblePos[spls_, h_] := Module[{k},
                                             For[k = 1, k <= Length[spls], k++,
                                                 If[NotCompatible[h[[1]], spls[[k]]], Return[1];];
                                                 If[NotCompatible[h[[2]], spls[[k]]], Return[2];];
                                                 If[NotCompatible[h[[3]], spls[[k]]], Return[3];];
                                                 ];
                                             Return[0];
                                             ];
        For[i = 1, i <= Length[H], i++,
            pos = IncompatiblePos[E, H[[i]]] ;
            If[pos > 0, AppendTo[inc, i]; 
               E = Join[E, Delete[H[[i]], pos]];];
            ];
        If[(Length[H] - Length[inc]) == 0, 
           Return[PoppingTree[DeleteDuplicates[E]]];];
        H = Delete[H, {#} & /@ inc];
        C = Delete[C, {#} & /@ inc];
        inc = {};
        For[i = 1, i <= Length[H], i++,
            If[MemberQ[E, H[[i, 1]]] && MemberQ[E, H[[i, 2]]] && 
               MemberQ[E, H[[i, 3]]], AppendTo[inc, i];];
            ];
        If[(Length[H] - Length[inc]) == 0, 
           Print["There exists the unique tree."]; 
           Return[PoppingTree[DeleteDuplicates[E]]];];
        H = Delete[H, {#} & /@ inc];
        E1 = Flatten[H, 1];
        choice1 = DeleteDuplicates[Union[E, E1]];
        E1 = Intersection[Complement[Union[E, E1], E], E1];
        choice2 = Select[choice1, # != E1[[1]] &];
        Print["Not unique! There are two distinct trees."];
        Return[{PoppingTree[choice1], PoppingTree[choice2]} // TableForm];
               
               ];
        
        

threeUPP[input_] := If[StringQ[input],
           threeUPPHelper[Read3StateCharacters[ReadList[input, String]]], 
           threeUPPHelper[FormatCharacters[input]]];

End[];
EndPackage[];



