/* This can be run after "classify_partial_option.m" has been stopped.
 * Remember to increase value_of_j_reached to the desired starting point.
 * End_time will be calculated based on start_time from "classify_partial_option.m"
 * New indicies will be appended to already existing list.
 */
// load "classification.m";

// Fs := getFunctions();
// reps := getRepresentatives();
// autom := getAutomorphismGroups();
// g := reps[i];
// automorphismGroup := autom[i];

for j in [value_of_j_reached..#Fs] do
	value_of_j_reached := j;
	if dupeq_with_l2_representatives(g, Fs[j], automorphismGroup) then
	    Append(~indicies, j);
	    j;
	end if;
end for;
end_time := Realtime(start_time);
end_time;
