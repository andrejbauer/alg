(1) before running the program we have to import it into GAP.
	This can be done by simply copy pasting the program from
	its file or using the command Read( filename ), which reads
	th he input from the file with the specified filename.
	
(2) Run the program extract_groups(directoryName, start, stop)
	Example:
	
	extract_groups("/cygdrive/c/Users/Grega/Desktop/MZR/Sizes", 10, 11);
	
(3) If GAP runs out of memory while it tries to extract groups it
	must be restarted and run with the -o parameter.
	
	gap.bat -o sizeOfMemory