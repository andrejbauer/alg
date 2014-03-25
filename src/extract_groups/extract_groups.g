extract_groups := function(directoryName, start, stop)
	directoryLocation := Directory(directoryName);

	for i in [start..stop] do
		Display(i);

		sizesName := Filename(directoryLocation, ViewString(i));
		sizesOutput := OutputTextFile(sizesName, true);

		for var in AllSmallGroups(i) do
			structureDesc := StructureDescription(var);
			strStructureDesc := PrintString(structureDesc);

			split_x := SplitString(strStructureDesc, "x");
			split_dot := SplitString(strStructureDesc, ".");
			split_colon := SplitString(strStructureDesc, ":");

			if Length(split_x) = 1 or Length(split_dot) > 1 or Length(split_colon) > 1 then
				Display(structureDesc);
				multTable := MultiplicationTable(var);
				size := Size(var);

				for i in [1..size] do
					for j in [1..size] do
						AppendTo(sizesOutput, " ");
						AppendTo(sizesOutput, ViewString(multTable[i][j]));
					od;
				od;
				AppendTo(sizesOutput, "\n");
				AppendTo(sizesOutput, "\n");
			fi;
			
		od;
		CloseStream(sizesOutput);
	od;
end;
