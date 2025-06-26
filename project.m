//global representations of symbols and fields:
C := ComplexField(20);
inf := C!1e20;
Q := Rationals();
F<z,exp,cos,sin,log1p> := PolynomialRing(Q, 5); //log1p stands for log(1+z)

//calculating truncated elementary trancendental functions
function exp_approx(n)
    sum := 0;
    for k in [0..n+3] do
        sum +:= z^k / Factorial(k);
    end for;
    return sum;
end function;

function cos_approx(n)
    sum := 0;
    for k in [0..n+3] do
        sum +:= (-1)^k * z^(2*k) / Factorial(2*k);
    end for;
    return sum;
end function;

function sin_approx(n)
    sum := 0;
    for k in [0..n+3] do
        sum +:= (-1)^k * z^(2*k+1) / Factorial(2*k+1);
    end for;
    return sum;
end function;

function log1p_approx(n) //stands for log(1+z)
    sum := 0;
    for k in [1..n+3] do
        sum +:= ((-1)^(k+1)) * z^k / k;
    end for;
    return sum;
end function;

function MyPartialFractionDecomposition(f)
    //helper function to compute partial fraction decompositions of rational functions

    //first we need to determine the factorization of the denominator in order to know which field extensions are needed
    den_f := Factorisation(Denominator(f));

    //we check the field extentions
    extentions := [];
    for factor in den_f do
        if Degree(factor[1]) gt 1 then
            Append(~extentions,factor[1]);
        end if;
    end for;

    //we make the new function field and cast f to it
    if #extentions eq 0 then
        Q_ext := BaseRing(Parent(f));
    else
        Q_ext := SplittingField(extentions);
    end if;
    K<z> := RationalFunctionField(Q_ext);
    new_f := K!f;

    full_factorization := Factorisation(Denominator(new_f));

    //now we compute a partial fraction decomposition again over the extended field
    full_decomposition := SimplePartialFractionDecomposition(new_f); 

    return full_decomposition;
end function;

function MyBinomialExpansion(f, z0, domain, p)
    //function that for a given resulting component of MyPartialFractionDecomposition(), expands it into a series using
    //the generalized binomial theorem. We return this series as a sequence of tuples <coefficient,exponent>

    //we need the following values
    numerator := f[3];
    denominator := f[1];
    n := f[2]; //the multiplicity of the denominator
    b := Coefficient(denominator,0);
    a := Coefficient(denominator,1);

    //if we only have a numerator we are done immediately
    if denominator eq 1 then
        //we simply return the numerator as a sequence
        x := Coefficient(numerator,0);
        y := Coefficient(numerator,1);
        terms := [<x,0>,<y,1>];
        return terms;
    end if;
    root := Roots(denominator)[1][1];

    //to do comparisons with the root, we need to get an approximation
    min_pol := MinimalPolynomial(root);
    root := Roots(min_pol, C)[1][1];

    //we build the series expansion
    series := [];
    if b ne 0 then
        //we distinguish between two cases: either the first singularity of the domain is closer to z0 than the root of the current component, or not
        //in both cases the series should be different in order to converge in the domain
        if Abs(root-z0) gt Abs(domain[1]-z0) then 
            c := -a / b;

            for i in [0..p] do
                Append(~series, <c^i * 1/b^n * numerator * Binomial(n + i - 1, i),i>);
            end for;
        else 
            c := -b / a;

            for i in [0..p] do
                Append(~series, <c^i * 1/a^n * numerator * Binomial(n + i - 1, i),-n-i>);
            end for;
        end if;
    else
        //if b is 0 we are in the trivial case
        series := [<numerator/a,-n>];
    end if;

    return series;
end function;

function LaurentSeriesAroundPoint(f, z0, domain, p)
    //function that given a rational function, rational number, domain and precision, computes the laurent series around the point z0 on the domain truncated at the pth term

    //we must first substitute t := z - z0 => z := t + z0
    K<t> := Parent(f);
    f_sub := Evaluate(f, t + z0);

    //if f is a polynomial, we are done immediately and we return the function itself, which is a taylor series
    if Denominator(f) eq 1 then
        R := PolynomialRing(Rationals());
        f_sub := R!f_sub;
        laurent_expansion := AssociativeArray(Integers());

        //we have to truncate it properly
        for i in [0..Min(p,Degree(f_sub))] do
            coeff := Coefficient(f_sub, i);
            laurent_expansion[i] := coeff;
        end for;
        return laurent_expansion;
    end if;
    
    //we first need to calculate the full partial fraction decomposition such that all
    //denominators look like (ax+b)^n
    decomposition := MyPartialFractionDecomposition(f_sub);

    //for each part in the decomposition we determine the series and add them together
    //to the laurent expansion
    laurent_expansion := AssociativeArray(Integers());
    for component in decomposition do
        //we must first convert the function to a series (using binomial theorem)
        bin := MyBinomialExpansion(component,z0, domain, p);

        //we add the new series to our current series
        for b_term in bin do
            exponent_in_array := false;
            for i in Keys(laurent_expansion) do
                //we check if the exponents are the same and if so, we add the coefficients together
                if b_term[2] eq i then
                    c := b_term[1] + laurent_expansion[i];
                    laurent_expansion[i] := c;
                    exponent_in_array := true;
                    break;
                end if;
            end for;
            
            //if the exponent is not in the array we must initialize it
            if exponent_in_array eq false then
                laurent_expansion[b_term[2]] := b_term[1];
            end if;
        end for;   
    end for;

    //we return the laurent expansion, which can later be used to pretty print the series substituted with the (z-point)
    return laurent_expansion;
end function;

function PrettySeries(series, z0, p)
    //pretty printer for laurent/taylor series
    terms := [];
    for exp in Sort(SetToSequence(Keys(series))) do
        coeff := series[exp];
        if coeff ne 0 then
            if z0 eq 0 then
                if exp eq 0 then
                    Append(~terms, Sprint(coeff));
                elif exp eq 1 then
                    Append(~terms, Sprint(coeff) * "*z");
                else
                    Append(~terms, Sprint(coeff) * "*z^" * Sprint(exp));
                end if;
            else 
                if exp eq 0 then
                    Append(~terms, Sprint(coeff));
                elif exp eq 1 then
                    Append(~terms, Sprint(coeff) * "*(z - " * Sprint(z0) * ")");
                else
                    Append(~terms, Sprint(coeff) * "*(z - " * Sprint(z0) * ")^" * Sprint(exp));
                end if;
            end if;
        end if;
    end for;
    if z0 eq 0 then
        o_term := "O(z^" * Sprint(p+1) * ")";
    else
        o_term := "O((z - " * Sprint(z0) * ")^" * Sprint(p+1) * ")";
    end if;
    Append(~terms, o_term);

    return Join(terms, " + ");
end function;

function TranscendentalTruncated(num,den,p)
    //function to substitute symbols for transcendental functions by the truncated series

    //we first make sthe substitutions in the numerator and denominator seperately
    num_sub := Evaluate(num,exp,exp_approx(p));
    num_sub := Evaluate(num_sub,cos,cos_approx(p));
    num_sub := Evaluate(num_sub,sin,sin_approx(p));
    num_sub := Evaluate(num_sub,log1p,log1p_approx(p));
    den_sub := Evaluate(den,exp,exp_approx(p));
    den_sub := Evaluate(den_sub,cos,cos_approx(p));
    den_sub := Evaluate(den_sub,sin,sin_approx(p));
    den_sub := Evaluate(den_sub,log1p,log1p_approx(p));

    //because of typing issues we build a new numerator and denominator from scratch
    K := PolynomialRing(Q);

    //the numerator
    M := Monomials(num_sub);
    C := Coefficients(num_sub);
    new_num := K!0;
    for i in [1..#M] do
        mon := M[i];
        coeff := C[i];
        exps := Exponents(mon);
        new_num +:= K!coeff * (K.1)^exps[1];
    end for;

    //the denominator
    M := Monomials(den_sub);
    C := Coefficients(den_sub);
    new_den := K!0;
    for i in [1..#M] do
        mon := M[i];
        coeff := C[i];
        exps := Exponents(mon);
        new_den +:= K!coeff * (K.1)^exps[1];
    end for;

    return <new_num,new_den>;
end function;

function DomainsAndSingularities(num,den,z0,p)
    //helper function to determine the different annulus domains and singularities of a given function

    //we first determine the approximate singularities
    singularities := Roots(den, C);

    //we remove duplicates, i.e., we don't want multiple singularities with equal distance to z0
    sing_no_dup := [];
    for s in singularities do
        duplicate := false;
        for sd in sing_no_dup do
            if Abs(s[1] - z0) eq Abs(sd[1] - z0) then
                duplicate := true;
            end if;
        end for;
        if duplicate eq false then
            Append(~sing_no_dup, s);
        end if;
    end for;

    //we sort the singularities
    sorted_singularities := Sort(sing_no_dup, func<a, b | Abs(a[1] - z0) - Abs(b[1] - z0)>);

    //we add z0 at the beginning, infinity at the end and we again make sure we don't add z0 twice
    bounds := [C!z0];
    for s in sorted_singularities do
        if not s[1] in bounds then
            Append(~bounds, s[1]);
        end if;
    end for;
    Append(~bounds,inf);

    //we make the associative array with keys in ascending order
    domains := AssociativeArray(Integers());
    for i in [0..#bounds-2] do
        domains[i] := <bounds[i+1], bounds[i+2]>; 
    end for;

    return <domains,singularities>;
end function;


LaurentAnalysis := procedure(num, den, z0, p);
    //the main function of this project. prints all the relevent information about the laurent/taylorexpansion of a given function 

    //we print a welcome message first
    printf "performing laurent analysis with precision: %o on function: %o around point: %o\n",p, "(" * Sprint(num) * ")/(" * Sprint(den) * ")", z0;

    //if our function contains trancendental components, we need to replace them with a sufficiently truncated series to approximate it
    f := TranscendentalTruncated(num,den,p);

    //we need to obtain the singularities (to print them) and the domains (to determine the power series for)
    new_num := f[1];
    new_den := f[2];
    tup := DomainsAndSingularities(new_num,new_den,z0,p);
    domains := tup[1];
    singularities := tup[2];

    //we print the relevant information on the singularities
    print("\nApproximate singularities: ");
    for s in singularities do
        if Evaluate(new_den,s[1]) eq 0 and Evaluate(new_num,s[1]) eq 0 then
            printf "removable singularity at: %o\n", s[2], s[1];
        else
            printf "pole of order: %o at: %o\n", s[2], s[1];
        end if;
    end for;
    contains_transcendental := exists{i : i in [2..5] | Degree(num, i) ne 0};
    if contains_transcendental then
        print "essential singularity at: infinity\n";
    end if;

    //now we determine the laurent/taylor series around z0 for each domain
    for d in Keys(domains) do
        laurent_series := LaurentSeriesAroundPoint(new_num/new_den,z0,domains[d],p);

        //we also make it explicit whether the series is a taylor or a laurent series
        type_series := "taylor";
        if #singularities gt 0 then
            type_series := "laurent";
        end if;
        printf "\nThe %o series around %o on domain %o is: \n",type_series, z0, domains[d];
        print(PrettySeries(laurent_series,z0,p));

        //we print the residue
        non_zero := true;
        for exp in Keys(laurent_series) do
            if exp eq -1 then
                non_zero := false;
                printf "\nThe residue is: %o\n", laurent_series[exp];
            end if;
        end for;
        if non_zero then
            printf "\nThe residue is: %o\n", 0;
        end if;
    end for;
end procedure;

function SeriesEqual(f,z0,d,p) 
    //helper function to automatically test equality of our own implementation and magmas implementation

    //we first need to get the following values and function transformations
    f := TranscendentalTruncated(Numerator(f),Denominator(f),p);
    tup := DomainsAndSingularities(f[1],f[2],z0,p);
    domain := tup[1][d];
    f := f[1]/f[2];
    K<t> := Parent(f);
    Q := Rationals();
    L := LaurentSeriesRing(Q,p);

    //naive if statement, but we don't check any other cases than the first domain and the last domain
    if d gt 0 then
        //case where we check the series around infinity 
        f_sub := Evaluate(f, t + z0);
        f_sub := Evaluate(f_sub, 1/t);
        magma_series := L ! f_sub;
        magma_series_list := [<Coefficient(magma_series, i),-i> : i in [-p/2..p/2]];
    else
        //case where we compute the series inside the first convergence radius around z0
        f_sub := Evaluate(f, t + z0);
        magma_series := L ! f_sub;
        magma_series_list := [<Coefficient(magma_series, i),i> : i in [-p/2..p/2]];
    end if;

    //we then compute the series using our own implementation
    my_series := LaurentSeriesAroundPoint(f, z0, domain, p);

    //we compare the coefficients
    for exp in Keys(my_series) do
        term_equal := false;
        for magma_term in magma_series_list do
            if exp eq magma_term[2] then
                if my_series[exp] eq magma_term[1] then
                    term_equal := true;
                end if;
            end if;
        end for;

        if term_equal then
            return true;
        end if;
    end for;

    //we print both series in case of inequality (for debugging)
    print(magma_series_list);
    for exp in Keys(my_series) do
        print "exponent:", exp, "coefficient:", my_series[exp];
    end for;
    return false;
end function;

/////////////////////////////////////// Testing ////////////////////////////////////////////////

TestLaurentSeriesAroundPoint := procedure()
    //to test the laurent series around point function automatically for a lot of different cases

    //tests around 0
    assert SeriesEqual(1/(1-z), 0, 0, 20);
    assert SeriesEqual(1/(1-z)^2, 0, 0, 20);
    assert SeriesEqual(1/z, 0, 0, 20);
    assert SeriesEqual((z - 3)/(z^2 + 1), 0, 0, 20); 
    assert SeriesEqual(1/z^3, 0, 0, 20); 
    assert SeriesEqual(1/(z^2+2*z), 0, 0, 20);
    assert SeriesEqual(z^3 + 2*z^2 + z + 4, 0, 0, 20);
    assert SeriesEqual((4/9*z^3 - 8/9*z^2 + 4/9*z - 2/9)/(z^2 + 1/9*z + 8/9),0,0,20);

    //tests around a different point than 0
    assert SeriesEqual(z, 1, 0, 20);
    assert SeriesEqual(1/z, 1, 0, 20);
    assert SeriesEqual(1/(z^2+2*z), 1, 0, 20);
    assert SeriesEqual((z - 3)/(z^2 + 1), 1/2, 0, 20); 
    assert SeriesEqual((5/3*z^3 + 61/6*z^2 + 73/4*z + 179/24)/(z^3 + 17/6*z^2 + 17/12*z - 101/24),3/2,0,20);
    assert SeriesEqual((1/5*z^3 - 9/10*z^2 - 113/20*z - 231/40)/(z^3 + 29/10*z^2 + 3/4*z - 137/40),3/2,0,20);
    assert SeriesEqual((z^3 + 7*z^2 - 6*z + 3)/(z^3 - 4*z^2 + 5*z - 4),3/2,0,20);

    //test outside convergence radius:
    assert SeriesEqual(1/(1-z), 0, 1, 20);
    assert SeriesEqual((z - 3)/(z^2 + 1), 0, 1, 20); 
    assert SeriesEqual(1/(z^2+2*z), 0, 1, 20);
    assert SeriesEqual((4/9*z^3 - 8/9*z^2 + 4/9*z - 2/9)/(z^2 + 1/9*z + 8/9),0,1,20);

    //test outside convergence radius + alternative expansion point
    assert SeriesEqual(1/(1-z), 1/2, 1, 20);

    //tests on elementary transcendental functions
    assert SeriesEqual(2*exp, 0, 0, 20);
    assert SeriesEqual(cos + 1/z, 0, 0, 20);
    assert SeriesEqual(log1p, 0, 0, 20);
    assert SeriesEqual(sin/z, 0, 0, 20);
    assert SeriesEqual(cos,1,0,20);
    assert SeriesEqual(cos^2,1,0,20);
    assert SeriesEqual(cos*sin + exp*cos^2 + (z+cos)/(z^2+2),2,0,20);
end procedure;

TestLaurentAnalysis := procedure()
    //to test the laurent analysis manually
    //f := 3*cos + z^2/(z^3+1) + exp/z^2;
    //f := sin/z;
    f := (2*z^2 + 3*z -1)/(z^3 - z^2 + 2);
    prec := 5;
    z0 := 0;
    den := Denominator(f);
    num := Numerator(f);
    LaurentAnalysis(num,den,z0,prec);
end procedure;

TestLaurentPerformance :=  procedure() 
    //To test the performance
    //f := 4*cos^2 + z*sin + (2*z^3 + exp)/(z^4+3*z+1);
    f := 1/(z^5 - z + 1);
    n := [10,50,100,200,500,1000,2000,5000];
    n := [10,20,50,100,200];

    den := Denominator(f);
    num := Numerator(f);
    for i in n do
        time LaurentAnalysis(num,den, 0, i);
    end for;
end procedure;
