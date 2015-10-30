The instruction to run the 3upp algorithm.
included: package, input, example_usage.nb


### The threeUPP algorithm
	The algorithm takes the input which is either the directory of the text file contaning the set of characters or the set of characters and output whether there is the unique tree for that set of characters. The output will be,

	Case I: if the set of characters are compatible:
		+, a tree if there is the unique tree
		+, two distinct tree if there isn't the unique tree

	Case II: if the set of characters are not compatible:
		+, a minimum obstruction set of 3 incompatible characters


### How to run

Make a new mathematica file, import the package main.m, and use the function threeUPP. If the user wish to use their own data, then just copy the data file into the input folder.

 	SetDirectory[NotebookDirectory[]];
	Needs["package`main`"];

	threeUPP[“input/filename”]

### Example (example_usage.nb)

	SetDirectory[NotebookDirectory[]];
	Needs["package`main`"];

	threeUPP["input/compatible_unique_1.txt"]

	threeUPP["input/compatible_twoTrees.txt"]

	threeUPP[{{"acd", "bef", "g"}, {"acg", "bef", "d"}, {"ade", "bcf", "g"}, {"ace", "bfg", "d"}, {"abcd", "eg", "f"}, {"acef", "bd", "g"}, {"acf", "bg", "de"}}]


