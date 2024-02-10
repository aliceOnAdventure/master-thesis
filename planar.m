/* Check whether a presemifield has identity */
function hasIdentity(TT)
	FF := Parent(Random(Keys(TT))[1]);
	for potential_identity in FF do
		if potential_identity eq 0 then
			continue;
		end if;
		problem := false;
		for x in FF do
			if x eq 0 then
				continue;
			end if;
			if (TT[<x,potential_identity>] ne x) or (TT[<potential_identity,x>] ne x) then
				problem := true;
				break;
			end if;
		end for;
		if not problem then
			return [potential_identity];
		end if;
	end for;

	return [];
end function;

/* Compute ternary representation of the given number. Returns the result
 * as an inverted list: [3^0, 3^1, ..., 3^n], instead of [3^n, 3^(n-1), .., 3^0]
 */
function numberToTernary(number)
	counter := 0;
	ternary := [];
	while number gt 0 do
		remainder := number mod 3;
		number := number div 3;
		//ternary := ternary + remainder * 10^counter;
		//counter := counter + 1;
		Append(~ternary, remainder);
	end while;
	return ternary;
end function;

/* Compute algebraic degree of the given ternary function. */
function algebraicDegree(func)
	degree := 0;
	coefficient_list := Coefficients(func);
	list_size := #coefficient_list;
	for numb in {1..list_size} do
		if coefficient_list[numb] ne 0 then
			ternary := numberToTernary(numb-1);
			temp := 0;
			for tern in ternary do
				temp := temp + tern;
			end for;
			if temp gt degree then
				degree := temp;
			end if;
		end if;
	end for;
	return degree;
end function;

/* Checks if the given funciton is a planar function,
 * works for all functions
 */
function isPlanarOrNot(f)
	FF := BaseRing(Parent(f));
	PR<x> := PolynomialRing(FF);

	isPotentiallyTrue := true;

	for a in FF do
		if a eq 0 then
			continue;
		end if;
		df := Evaluate(f, x+a) - f;
		if #{ Evaluate(df, x) : x in FF } ne #FF then
			isPotentiallyTrue := false;
			break;
		end if;
	end for;

	return isPotentiallyTrue;
end function;

/* Planarity check for functions with even exponents, linear running time */
function isPlanarOrNotFast(f)
	FF := BaseRing(Parent(f));
	M := {* Evaluate(f,x) : x in FF*};
	S := SequenceToMultiset(Multiplicities(M));
	first_condition := {s : s in S} eq {1,2};
	second_condition := Multiplicity(S,1) eq 1;
	return first_condition and second_condition;
end function;

/* Will select the fastest planarity check when possible, otherwise the normal one */
function isPlanar(f)
	if algebraicDegree(f) eq 2 then
		return isPlanarOrNotFast(f);
	else
		return isPlanarOrNot(f);
	end if;
end function;

/* Check if all the functions in a list are planar. */
function isAllPlanar(Fs)
	isPlanar := true;
	for f in Fs do
		if not isPlanarOrNot(f) then;
			isPlanar := false;
			break;
		end if;
	end for;
	return isPlanar;
end function;

function genLinearCodeFromFunction(poly_f, p, n)
	GF<z> := FiniteField(p,n);
	f:= func< x| Evaluate(poly_f, x)>;
	M := Matrix(FiniteField(p), 2*n+1, p^n,
		[1: x in GF]
		cat [Trace(z^i * x): x in GF, i in [0..n-1]]
		cat [Trace(z^i * f(x)): x in GF, i in [0..n-1]]
	);
	// printf "GenMatrix :=%o\n", M;
	return LinearCode(M);
end function;

// Code for testing CCZ equivalence
function isCCZEquivalent(f1, f2, p, n)
	Code1 := genLinearCodeFromFunction(f1, p, n);
	Code2 := genLinearCodeFromFunction(f2, p, n);
	res, map := IsIsomorphic(Code1, Code2);
	return res;
end function;

// When should I use this?
function getEquivalentCodes(f1, f2, p, n)
	Code1 := genLinearCodeFromFunction(f1, p, n);
	Code2 := genLinearCodeFromFunction(f2, p, n);
	return <Code1,Code2>;
end function;

/* Check whether or not all the functions in the given
 * list are planar.
 */
function checkPlanar(allPNs)
	for func in allPNs do
		func;
		if isPlanarOrNot(func) eq false then
			return false;
		end if;
	end for;
	return true;
end function;

/* Finds the code invariant for the given function */
function constructAssociatedCode(F)
	FF := BaseRing(Parent(F));
	p := Characteristic(FF);
	n := Degree(FF);

	bits := [];
	for x in FF do
		Append(~bits, [ GF(p) ! 1 ]);
		Append(~bits, Flat(x));
		Append(~bits, Flat(Evaluate(F,x)));
	end for;
	M := Transpose(Matrix(GF(p), p^n, 2*n+1, &cat bits));
	C := LinearCode(M);
	A := AutomorphismGroup(C);

	return (Order(A));
end function;

/* Find the code invariant for a list of functions */
function constructAssociatedCodeForList(Fs)
	res := [];
	for f in Fs do
		code_invariant := constructAssociatedCode(f);
		code_invariant;
		Append(~res, code_invariant);
	end for;
	return res;
end function;

function CCZforFunction(list_to_test, p, n)
	CCZ_to_function := [];
	func_to_test := list_to_test[1];
	funcNr := 1;
	if #list_to_test eq 1 then
		return list_to_test;
	end if;

	for func in list_to_test do
		if funcNr mod 50 eq 0 then
			funcNr;
		end if;
		if isCCZEquivalent(func_to_test, func, p, n) eq true then
			Append(~CCZ_to_function, func);
		end if;
		funcNr := funcNr + 1;
	end for;
	return CCZ_to_function;
end function;

function removeElementsFromList(list, elements_to_remove)
	new_list := [];
	for elem in list do
		in_both := false;
		for remove in elements_to_remove do
			if elem eq remove then
				in_both := true;
			end if;
		end for;
		if in_both eq false then
			Append(~new_list, elem);
		end if;
	end for;
	return new_list;
end function;

// Partitions the given list into a list of list, where each inner list
// contains functions which are equivalent to the other functions in the
// same inner list and inequivalent to the functions in the other lists.
function findInequivalentFunctions(listOfPNs, p, n)
	inequivalentFunctions := [];
	while #listOfPNs gt 0 do
		CCZ := CCZforFunction(listOfPNs, p, n);
		Append(~inequivalentFunctions, CCZ);
		listOfPNs := removeElementsFromList(listOfPNs, CCZ);
		#listOfPNs;
	end while;
	return inequivalentFunctions;
end function;

/* Functions : 	a set of lists where each list contains all the planar functions from the same
 *		planar polynomial.
 * n : 		dimension
 * Partitions the given lists into CCZ equivalence classes.
 */
function partitionIntoCCZClasses(functions,p,n)
	equiv := [];
	for index in [1..#functions] do
		while #functions[index] gt 0 do
			CCZ := CCZforFunction(functions[index], p, n);
			Append(~equiv, CCZ);
			functions[index] := removeElementsFromList(functions[index], CCZ);
			#functions[index];
		end while;
	end for;
	equiv;
	result := [];
	while #equiv gt 0 do
		tempRes := equiv[1];
		isEquivalent := [true];
		for index in [2..#equiv] do
			if isCCZEquivalent(equiv[1][1], equiv[index][1], p, n) then
				Append(~isEquivalent, true);
				for elem in equiv[index] do
					Append(~tempRes, elem);
				end for;
			else
				Append(~isEquivalent, false);
			end if;
		end for;
		Append(~result, tempRes);
		updatedList := [];
		for index in [1..#isEquivalent] do
			if not isEquivalent[index] then
				Append(~updatedList, equiv[index]);
			end if;
		end for;
		equiv := updatedList;
	end while;
	return result;
end function;

/*
 *
 */
function partitionIntoClassesWithCodeInvariant(Fs)
	FF := BaseRing(Parent(Fs[1]));
	p := Characteristic(FF);
	n := Degree(FF);
	counter := 1;
	code_invariants := [];
	for f in Fs do
		if counter mod 20 eq 0 then
			counter;
		end if;
		invariant := constructAssociatedCode(f);
		Append(~code_invariants, invariant);
		counter := counter + 1;
	end for;

	invariants := SetToSequence(SequenceToSet(code_invariants));
	invariants;

	groups := [];
	for j in [1..#invariants] do
		group := [ Fs[i] : i in [1..#code_invariants] | code_invariants[i] eq invariants[j] ];
		Append(~groups, group);
	end for;
	"groups finished";
	#groups;

	result := [];
	for i in [1..#groups] do
		group := groups[i];
		counter := 0;
		while #group gt 0 do
			counter := counter + 1;
			CCZ := CCZforFunction(group, p, n);
			Append(~result, CCZ);
			group := removeElementsFromList(group, CCZ);
			if counter mod 50 eq 0 then
				counter;
			end if;
		end while;
	end for;
	return result;
end function;

/* Check CCZ equivalence of the results from expansion against the
 * the known functions in the same dimension. "newList" should be
 * a list with lists containing the classes from the classification.
 */
function checkCCZAgainstKnownFamiliy(f, newList, p, n, match)
	updatedList := [];
	for i in [1..#newList] do
		if isCCZEquivalent(f, newList[i][1], p, n) then
			i;
			Append(~match, i);
		else
			Append(~updatedList, newList[i]);
		end if;
	end for;
	return updatedList, match;
end function;

function checkAllCCZ(listOfKnown, newList, p, n)
	match := [];
	for l in listOfKnown do
		newList, match := checkCCZAgainstKnownFamiliy(l, newList,p, n, match);
	end for;
	return match;
end function;

/* Creates a truth table for the semifield operation defined by a planar function, so that
 * TT[<a,b>] = a*b. Returns the identity element as the second element.
 */
function planar2semifield(f)
	/* Construct a truth table of f first, to reduce number of polynomial evaluations. */
	FF := BaseRing(Parent(f));
	F := AssociativeArray();
	for x in FF do
		F[x] := Evaluate(f,x);
	end for;

	/* First, we create the presemifield operation via x*y = f(x+y) - f(x) - f(y) */
	TT := AssociativeArray();
	for x in FF do
		for y in FF do
			TT[<x,y>] := F[x+y] - F[x] - F[y];
		end for;
	end for;

	/* We now convert this to a semifield by taking some arbitrary non-zero a
	   and setting (x*a) '*' (a*y) = x*y. */
	a := FF ! 1;
	TTs := AssociativeArray();
	for x in FF do
		for y in FF do
			TTs[< TT[<x,a>], TT[<a,y>] >] := TT[<x,y>];
		end for;
	end for;

	return TTs, TT[<a,a>];
end function;

/* For verifying that the semifields produced by the function above have 1 as the identity */
function aux_verify_identity(TT,identity)
	FF := Parent(Random(Keys(TT))[1]);
	for x in FF do
		if TT[<x,identity>] ne x then
			return false;
		end if;
		if TT[<identity,x>] ne x then
			return false;
		end if;
	end for;
	return true;
end function;

/* Checks whether "a" is in the left nucleus of the semifield defined by "f" */
function is_in_left_nucleus(TT,a)
	FF := Parent(Random(Keys(TT))[1]);
	for x in FF do
		for y in FF do
			lhs := TT[<a, TT[<x,y>]>];
			rhs := TT[<TT[<a,x>],y>];
			if lhs ne rhs then
				return false;
			end if;
		end for;
	end for;
	return true;
end function;

/* Checks whether "a" is in the middle nucleus of the semifield defined by "f" */
function is_in_middle_nucleus(TT,a)
	FF := Parent(Random(Keys(TT))[1]);
	for x in FF do
		for y in FF do
			lhs := TT[<x, TT[<a,y>]>];
			rhs := TT[<TT[<x,a>],y>];
			if lhs ne rhs then
				return false;
			end if;
		end for;
	end for;
	return true;
end function;

/* Checks whether "a" is in the right nucleus of the semifield defined by "f" */
function is_in_right_nucleus(TT,a)
	FF := Parent(Random(Keys(TT))[1]);
	for x in FF do
		for y in FF do
			lhs := TT[<TT[<x,y>],a>];
			rhs := TT[<x, TT[<y,a>]>];
			if lhs ne rhs then
				return false;
			end if;
		end for;
	end for;
	return true;
end function;

/* Find the subfield that represents the left nucleus of a function in the given dimension. */
function left_nucleus(TT,p,n)
	FF := GF(p^n);
	possible_dimensions := Divisors(n);

	while #possible_dimensions gt 0 do
		current := possible_dimensions[#possible_dimensions];
		current_set := { x : x in GF(p^current) };
		for i in [1..#possible_dimensions-1] do
			current_set := current_set diff { x : x in GF(p^possible_dimensions[i]) };
		end for;
		alpha := Random(current_set);

		condition := is_in_left_nucleus(TT,alpha);
		if condition then
			return { x : x in GF(p^current) };
		else
			Exclude(~possible_dimensions, current);
		end if;
	end while;
	return [];
end function;

function left_nucleus_with_identity(TT,p,n,identity)
	FF := GF(p^n);
	possible_dimensions := Divisors(n);

	while #possible_dimensions gt 0 do
		current := possible_dimensions[#possible_dimensions];
		current_set := { identity * x : x in GF(p^current) };
		for i in [1..#possible_dimensions-1] do
			current_set := current_set diff { identity * x : x in GF(p^possible_dimensions[i]) };
		end for;
		alpha := Random(current_set);

		condition := is_in_left_nucleus(TT,alpha);
		if condition then
			return { identity * x : x in GF(p^current) };
		else
			Exclude(~possible_dimensions, current);
		end if;
	end while;
	return [];
end function;


/* Middle nucleus but multiplied by the semifield identity */
function middle_nucleus_with_identity(TT,p,n,identity)
	FF := GF(p^n);
	possible_dimensions := Divisors(n);

	while #possible_dimensions gt 0 do
		current := possible_dimensions[#possible_dimensions];
		current_set := { identity * x : x in GF(p^current) };
		for i in [1..#possible_dimensions-1] do
			current_set := current_set diff { identity * x : x in GF(p^possible_dimensions[i]) };
		end for;
		alpha := Random(current_set);

		condition := is_in_middle_nucleus(TT, alpha);
		if condition then
			return { identity * x : x in GF(p^current) };
		else
			Exclude(~possible_dimensions, current);
		end if;
	end while;
	return [];
end function;

/* Find the subfield that represents the middle nucleus of a function in the given dimension. */
function middle_nucleus(TT,p,n)
	FF := GF(p^n);
	possible_dimensions := Divisors(n);

	while #possible_dimensions gt 0 do
		current := possible_dimensions[#possible_dimensions];
		current_set := { x : x in GF(p^current) };
		for i in [1..#possible_dimensions-1] do
			current_set := current_set diff { x : x in GF(p^possible_dimensions[i]) };
		end for;
		alpha := Random(current_set);

		condition := is_in_middle_nucleus(TT, alpha);
		if condition then
			return { x : x in GF(p^current) };
		else
			Exclude(~possible_dimensions, current);
		end if;
	end while;
	return [];
end function;

/* Find the subfield that represents the right nucleus of a function in the given dimension. */
function right_nucleus(TT,p,n)
	FF := GF(p^n);
	possible_dimensions := Divisors(n);

	while #possible_dimensions gt 0 do
		current := possible_dimensions[#possible_dimensions];
		current_set := { x : x in GF(p^current) };
		for i in [1..#possible_dimensions-1] do
			current_set := current_set diff { x : x in GF(p^possible_dimensions[i]) };
		end for;
		alpha := Random(current_set);

		condition := is_in_right_nucleus(TT, alpha);
		if condition then
			return { x : x in GF(p^current) };
		else
			Exclude(~possible_dimensions, current);
		end if;
	end while;
	return [];
end function;

function right_nucleus_with_identity(TT,p,n,identity)
	FF := GF(p^n);
	possible_dimensions := Divisors(n);

	while #possible_dimensions gt 0 do
		current := possible_dimensions[#possible_dimensions];
		current_set := { identity * x : x in GF(p^current) };
		for i in [1..#possible_dimensions-1] do
			current_set := current_set diff { identity * x : x in GF(p^possible_dimensions[i]) };
		end for;
		alpha := Random(current_set);

		condition := is_in_right_nucleus(TT, alpha);
		if condition then
			return { identity * x : x in GF(p^current) };
		else
			Exclude(~possible_dimensions, current);
		end if;
	end while;
	return [];
end function;

/* Compute left, middle and right nuclei with the same semifield. */
function nucleus(f,p,n)
	TT := planar2semifield(f);
	ln := left_nucleus(TT,p,n);
	mn := middle_nucleus(TT,p,n);
	rn := right_nucleus(TT,p,n);
	return [#ln, #mn, #rn];
end function;


function nucleus_with_identity(f,p,n)
	TT := planar2semifield(f);
	identity := hasIdentity(TT);
	assert #identity eq 1;
	ln := left_nucleus_with_identity(TT,p,n,identity[1]);
	mn := middle_nucleus_with_identity(TT,p,n,identity[1]);
	rn := right_nucleus_with_identity(TT,p,n,identity[1]);
	return [#ln, #mn, #rn];
end function;

function nucleus_manual(f,p,n)
	TT := planar2semifield(f);
	FF := BaseRing(Parent(f));
	ln := [];
	mn := [];
	rn := [];
	for x in FF do
		if is_in_left_nucleus(TT,x) then
			Append(~ln,x);
		end if;
		if is_in_middle_nucleus(TT,x) then
			Append(~mn,x);
		end if;
		if is_in_right_nucleus(TT,x) then
			Append(~rn,x);
		end if;
	end for;
	return [#ln, #mn, #rn];
end function;
