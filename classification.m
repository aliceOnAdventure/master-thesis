load "automorphism.m";
//load "representatives.m";
/*
 * Get the finite field, polynomial ring, characteristic and degree of the function
 * @param function - Function to get properties for
 * @returns Characteristic and Degree
 */
function getFunctionProperties(func)
    FF<a> := BaseRing(Parent(func));
	PR<x> := PolynomialRing(FF);
	p := Characteristic(FF);
	n := Degree(FF);
    return FF, p, n;
end function;

/*
 * Find all the indicies of all the function in Fs which are
 * equivalent to the representative.
 * @param{Fs} List containing the functions to classify
 * Returns the indicies of the functions equivalent to the representative
 */
 function classifyAgainstOneRepWithDupeq(Fs, g, automorphismGroup)
    indicies := [];
    for i in [1..#Fs] do
        if dupeq_with_l2_representatives(g, Fs[i], automorphismGroup) then
            Append(~indicies, i);
            i;
        end if;
    end for;
    return indicies;
 end function;

/*
 * The automorphismGroup is the automorphism group of g
 * @param{Fs} List containing the known representatives
 * @param{Gs} List containing the functions to classify
 * @param{automorphismGroups} List of the automorphism group of each representatives,
 * so that Gs[i] has the automorphism group automorphismGroups[i].
 */
function classifyWithDupeqAndAutomorphism(Fs, Gs, automorphismGroups)
    notEquivalent := [];
    for i in [1..#Gs] do
        equivalent := false;
        for j in [1..#Fs] do
            if dupeq_with_l2_representatives(Fs[j], Gs[i], automorphismGroups[j]) then
                equivalent := true;
                break;
            end if;
        end for;
        if not equivalent then
            Append(~notEquivalent, Gs[i]);
        end if;
    end for;
    return notEquivalent;
end function;

/*
 * Generate linear code from function
 */
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

/*
 * Check CCZ equivalent between two functions.
 */
function isCCZEquivalent(f1, f2, p, n)
	Code1 := genLinearCodeFromFunction(f1, p, n);
	Code2 := genLinearCodeFromFunction(f2, p, n);
	res, map := IsIsomorphic(Code1, Code2);
	return res;
end function;

/*
 * Finds the code invariant for the given function
 */
function constructAssociatedCode(func)
	FF, p, n := getFunctionProperties(func);

	bits := [];
	for x in FF do
		Append(~bits, [ GF(p) ! 1 ]);
		Append(~bits, Flat(x));
		Append(~bits, Flat(Evaluate(func,x)));
	end for;
	M := Transpose(Matrix(GF(p), p^n, 2*n+1, &cat bits));
	C := LinearCode(M);
	A := AutomorphismGroup(C);

	return (Order(A));
end function;

/*
 * Partition the expansion result into lists based on CCZ equality. Meaning all
 * functions in the same list are CCZ equivalent
 * @param expansionFunctions - A list of all PN functions obtained from an expansion search
 * @returns A list of lists containing CCZ equivalent PN functions
 */
function classifyWithCCZCheck(expansionFunctions)
    assert not IsEmpty(expansionFunctions);
    FF, p, n := getFunctionProperties(expansionFunctions[1]);
    result := [];

    if #expansionFunctions eq 1 then
        return expansionFunctions;
    end if;

    while #expansionFunctions gt 0 do
        func := expansionFunctions[1];
        found := false;
        for i in [1..#result] do
            if isCCZEquivalent(func, result[i][1], p, n) then
                Append(~result[i], func);
                found := true;
                break;
            end if;
        end for;
        if not found then
            Append(~result, [func]);
        end if;
        expansionFunctions := Remove(expansionFunctions, 1);
    end while;
    return result;
end function;

/*
 * Partition the expansion result into lists based on the code invariant. Then all these lists
 * are partitioned again into smaller lists based on CCZ equivalence.
 * @param expansionFunctions - A list of all PN functions obtained from an expansion search
 * @returns A list of lists containing CCZ equivalent PN functions
 */
 function classifyWithCodeInvariant(expansionFunctions)
    assert not IsEmpty(expansionFunctions);
    // TODO: add progress report print
    progressReport := #expansionFunctions/50;
    FF, p, n := getFunctionProperties(expansionFunctions[1]);
    codeInvariantResult := [];
    codeInvariants := [];
    if #expansionFunctions eq 1 then
        return expansionFunctions;
    end if;

    while #expansionFunctions gt 0 do
        func := expansionFunctions[1];
        codeInv := constructAssociatedCode(func);
        found := false;
        for i in [1..#codeInvariantResult] do
            if codeInvariants[i] eq constructAssociatedCode(func) then
                Append(~codeInvariantResult[i], func);
                found := true;
                break;
            end if;
        end for;
        if not found then
            Append(~codeInvariantResult, [func]);
            Append(~codeInvariants, codeInv);
        end if;
        expansionFunctions := Remove(expansionFunctions, 1);
    end while;

    result := [];
    for list in codeInvariantResult do
        res := classifyWithCCZCheck(list);
        for list in res do
            Append(~result, list);
        end for;
    end for;

    return result;
 end function;

/*
 * Check if the functions from the expansion result is CCZ equivalent to
 * the representatives in the same dimension.
 * @param representatives - Chosen representatives for the given p and n
 * @param expansionFunctions - The new functions obtained by expansion search, all
 * partitioned into lists based on equivalence.
 * @returns true if all the functions are equivalent to the representatives.
 */
function isAllEquivalentToRepresentatives(representatives, expansionFunctions)
    FF, p, n := getFunctionProperties(expansionFunctions[1]);
    allEquivalent := true;
    for expansionRepList in expansionFunctions do
        expansionRep := expansionRepList[1];
        for rep in representatives do
            if not isCCZEquivalent(rep, expansionRep, p, n) then
                return false;
            end if;
        end for;
    end for;
    return allEquivalent;
end function;
