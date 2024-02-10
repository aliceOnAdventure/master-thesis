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
function constructAssociatedCodeForList(Fs, known_invariants)
	res := [];
	for f in Fs do
		code_invariant := constructAssociatedCode(f);
		Append(~res, code_invariant);
	end for;
	check := {* i in known_invariants : i in res *}; 
	check;
	return res;
end function;

/*
n := 5;
FF<a> := GF(3^n);
P<x> := PolynomialRing(FF);
F := x^162 + x^84 + a^58*x^54 + a^58*x^28 + x^6 + a^531*x^2;
F := a^75*x^2214 + x^756 + a^205*x^82 + x^28;
F := x^270 + 2*x^244 + a^449*x^162 + a^449*x^84 + a^534*x^54 + 2*x^36 + a^534*x^28 + x^10 + a^449*x^6 + a^279*x^2;
F := x^486 + x^252 + a^561*x^162 + a^561*x^84 + a^183*x^54 + a^183*x^28 + x^18 + a^561*x^6 + a^209*x^2;
F := x^2;

C := constructAssociatedCode(F);
AutomorphismGroup(C);
Order(AutomorphismGroup(C));
*/
