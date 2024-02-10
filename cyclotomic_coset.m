/* Finds the cyclotomic coset of k in GF(p^n) */
function getCyclotomicCoset(k,p,n)
	return { (k * p^l) mod (p^n-1) : l in [0..n-1] };
end function;

/* Gets all exponents of a polynomial */
function getExponents(P)
	FF := BaseRing(Parent(P));
	return { i : i in [0..#FF-1] | Coefficient(P,i) ne 0 };
end function;

/* Lost := { i : i in [1..#Fs] | getExponents(Fs[i]) subset C }; */

/* Reduce the given list of functions by removing the
 * functions with the same cyclotomic coset.
 * Fs - list of functions to reduce
 * k - exponent of the monomial used for the expansion
 * p - Characteristic of the field
 * n - Dimension of the field
 */
function reduceWithCyclotomicCoset(Fs, k, p, n)
	C := getCyclotomicCoset(k,p,n);
	ReducedList := [];
	for i in [1..#Fs] do
		if not getExponents(Fs[i]) subset C then
			Append(~ReducedList, Fs[i]);
		end if;
	end for;
	return ReducedList;
end function;

/* Write Fs to a file. */
function writeToFile(Fs, filename)
	SetLogFile(filename);
    "function getFunctions()";
	"   Fs := ";
	Fs;
    "    ;";
    "   return Fs;";
    "end function;";
    UnsetLogFile();
	return "Done";
end function;