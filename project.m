F := FreeAlgebra(Rationals(), 5);
z := F.1;
exp_z := F.2;
log_z := F.3;
sin_z := F.4;
cos_z := F.5;

function MyPartialFractionDecomposition(f,p)

    //First we need to determine the factorization of the denominator in order to know which field extensions are needed
    den_f := Factorisation(Denominator(f));

    //We check the field extentions
    extentions := [];
    for factor in den_f do
        if Degree(factor[1]) gt 1 then
            Append(~extentions,factor[1]);
        end if;
    end for;

    //we make the new function field
    if #extentions eq 0 then
        Q_ext := BaseRing(Parent(f));
    else
        Q_ext, roots := SplittingField(extentions : Abs := true, Opt := true);
    end if;

    K<z> := RationalFunctionField(Q_ext);

    //now we compute a partial fraction decomposition again over the extended field
    new_f := K ! f;
    full_decomposition := PartialFractionDecomposition(new_f); //TODO make own version of this

    //TODO we should return approximate roots as well
    seq := [];
    for factor in full_decomposition do
        Append(~seq, factor);
    end for;

    return seq;
end function;

function MyBinomialExpansion(f, z0, domain, p)
    //we need the following values
    numerator := f[3];
    denominator := f[1];

    //if we only have a numerator we are done immediately
    if denominator eq 1 then
        terms := [<numerator,0>];
        return terms;
    end if;

    n := f[2]; //the multiplicity of the denominator
    b := Coefficient(denominator,0);
    a := Coefficient(denominator,1);
    root := Roots(denominator)[1][1];

    //to do comparisons with the root, we need to get an approximation
    C := ComplexField(20);
    min_pol := MinimalPolynomial(root);
    root := Roots(min_pol, C)[1][1];

    geom := [];
    if Abs(root) ge Abs(domain[2]-z0) then //inside a radius
        if b ne 0 then
            c := -a / b;

            for i in [0..p] do
                geom := geom cat [<c^i * 1/b^n * numerator * Binomial(n + i - 1, i),i>];
            end for;
        else
            //if b is 0 we are in the trivial case
            geom := [<numerator/a,-n>];
        end if;
    elif Abs(root) le Abs(domain[1]-z0) then //outside a radius
        if b ne 0 then
            c := -b / a;

            for i in [0..p] do
                geom := geom cat [<c^i * 1/b^n * numerator * Binomial(n + i - 1, i),-n-i>];
            end for;
        else
            //if b is 0 we are in the trivial case
            geom := [<numerator/a,-n>];
        end if;
    end if;

    return geom;
end function;

function LaurentSeriesAroundPoint(f, z0, domain, p)
    //z0 needs to be a point in the complex numbers
    //f needs to be a rational function
    //assert Parent(z0) eq ComplexField();

    //substitute t := z - z0 => z := t + z0
    K<t> := Parent(f);
    f_sub := Evaluate(f, t + z0);

    //if f is a polynomial, we are done immediately
    if Denominator(f) eq 1 then
        F<t> := RationalFunctionField(Rationals());
        R := PolynomialRing(BaseRing(F));
        f := R!f;
        laurent_expansion := AssociativeArray(Integers());
        for i in [0..Degree(f)] do
            coeff := Coefficient(f, i);
            if coeff ne 0 then
                laurent_expansion[i] := coeff;
            end if;
        end for;
        return laurent_expansion;
    end if;
    
    //we first need to calculate the partial fraction decomposition (where all denominators are linear (to a power))
    decomposition := MyPartialFractionDecomposition(f_sub,p);

    //for each part in the decomposition we determine the series and add them together
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
            if exponent_in_array eq false then
                laurent_expansion[b_term[2]] := b_term[1];
            end if;
        end for;   
    end for;

    //we return the laurent expansion, which can later be used to pretty print the series substituted with the (z-point)
    return laurent_expansion;
end function;

function PrettyLaurentSeries(laurent_series, point, p) //TODO don't print brackets if z = 0
    //pretty printer for laurent series
    F<z> := RationalFunctionField(Rationals());
    terms := [];
    for exp in Keys(laurent_series) do
        coeff := laurent_series[exp];
        if exp eq 0 then
            Append(~terms, Sprint(coeff));
        elif exp eq 1 then
            Append(~terms, Sprint(coeff) * "*(" * Sprint(z) * " - " * Sprint(point) * ")");
        else
            Append(~terms, Sprint(coeff) * "*(" * Sprint(z) * " - " * Sprint(point) * ")^" * Sprint(exp));
        end if;
    end for;
    o_term := "O((" * Sprint(z) * " - " * Sprint(point) * ")^" * Sprint(p+1) * ")";
    Append(~terms, o_term); //TODO only print O if we cut off the series 

    return Join(terms, " + ");
end function;

function DomainsAndSingularities(f,z0,p)
    //helper function to determine the different annulus domains and singularities of a given function
    //determine singularities
    den := Denominator(f);
    C := ComplexField(20);
    singularities := Roots(den, C);

    //remove duplicates
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

    //make the domainmap
    sorted_singularities := Sort(sing_no_dup, func<a, b | Abs(a[1] - z0) - Abs(b[1] - z0)>);
    bounds := [C!z0];
    for s in sorted_singularities do
        if not s[1] in bounds then
            Append(~bounds, s[1]);
        end if;
    end for;
    Append(~bounds,C!1e20);

    DomainMap := AssociativeArray(Integers());
    for i in [0..#bounds-2] do
        DomainMap[i] := <bounds[i+1], bounds[i+2]>; 
    end for;

    return <DomainMap,singularities>;
end function;

//the main function of this project. prints all the relevent information about the laurent/taylorexpansion of a given rational function
LaurentAnalysis := procedure(f, z0, p);
    printf "performing laurent analysis with precision: %o on function: %o around point: %o\n",p, Sprint(f), z0;

    tup := DomainsAndSingularities(f,z0,p);
    domains := tup[1];
    singularities := tup[2];

    print("\nsingularities: ");
    punctured := false;
    for s in singularities do
        printf "pole of order: %o at: %o\n", s[2], s[1];
        if s[1] eq z0 then
            punctured := true;
        end if;
    end for;

    //now we determine the laurent series for each domain
    for d in Keys(domains) do
        laurent_series := LaurentSeriesAroundPoint(f,z0,domains[d],p);

        printf "\nThe laurent/taylor series around %o on domain %o is: ", z0, d; //TODO tell user if it is taylor or laurent
        print(PrettyLaurentSeries(laurent_series,z0,p));

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

    tup := DomainsAndSingularities(f,z0,p);
    domain := tup[1][d];

    //we first compute the magma laurent series around the point
    K<t> := Parent(f);
    Q := Rationals();
    L := LaurentSeriesRing(Q,p);
    if d gt 0 then //TODO make it work outside the convergence radius
        f_sub := Evaluate(f, 1/t);
        print(f_sub);
        magma_series := L ! f_sub;
        K<z> := Parent(f);
        magma_series := Evaluate(magma_series, 1/z);
        print(magma_series);
    else
        f_sub := Evaluate(f, t + z0);
        magma_series := L ! f_sub;
    end if;
    magma_series_list := [<Coefficient(magma_series, i),i> : i in [-p/2..p/2]];

    //we then compute our own series
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
        else
            //we print both series in case of inequality (for debugging)
            print(magma_series_list);
            for exp in Keys(my_series) do
                print "exponent:", exp, "coefficient:", my_series[exp];
            end for;
            return false;
        end if;
    end for;
    print(magma_series_list);
    print(my_series);
    return false;
end function;

/////////////////////////////////////// Testing ////////////////////////////////////////////////

function RandomPolynomial(d, N)
    Q := Rationals();
    R<x> := PolynomialRing(Q);
    coeffs := [Random([-N..N]) : i in [0..d]];
    return R ! coeffs;
end function;

function RandomRationalFunction(degP, degQ, N)
    p := RandomPolynomial(degP, N);
    q := RandomPolynomial(degQ, N);
    while q eq 0 do
        q := RandomPolynomial(degQ, N);
    end while;
    return p / q;
end function;


TestLaurentSeriesAroundPoint := procedure()
    //to test the laurent series around point function automatically for a list of rational functions
    Q := Rationals();
    K<z> := RationalFunctionField(Q);

    //tests around 0
    assert SeriesEqual(1/(1-z), 0, 0, 20);
    assert SeriesEqual(1/(1-z)^2, 0, 0, 20);
    assert SeriesEqual(1/z, 0, 0, 20);
    assert SeriesEqual((z - 3)/(z^2 + 1), 0, 0, 20); 
    assert SeriesEqual(1/z^3, 0, 0, 20); 
    assert SeriesEqual(1/(z^2+2*z), 0, 0, 20);
    assert SeriesEqual(z^3 + 2*z^2 + z + 4, 0, 0, 20);

    //tests around a different point than 0
    assert SeriesEqual(z, 1, 0, 20);
    assert SeriesEqual(1/z, 1, 0, 20);
    assert SeriesEqual(1/(z^2+2*z), 1, 0, 20);
    assert SeriesEqual((z - 3)/(z^2 + 1), 1/2, 0, 20); 
    //TODO test around the complex number i

    //tests outside the convergence radius
    //assert SeriesEqual(1/(1-z), 0, 1, 20);

    //test on a random larger rational function 
    F := RandomRationalFunction(3,3,10);
    assert SeriesEqual(F,0,0,20);
    assert SeriesEqual(F,3/2,0,20);

    //TODO test on elementary trancendental functions
    assert SeriesEqual(exp_z, 0, 0, 20);
end procedure;


TestLaurentAnalysis := procedure()
    //to test the whole laurent analysis manually
    Q := Rationals();
    K<z> := RationalFunctionField(Q);
    //f := 1/(1-z);
    f := (z - 3)/(z^2 + 1);
    //f := z + 1/z;
    //f := 1/(z^2+2*z);
    prec := 20;
    z0 := 0;
    LaurentAnalysis(f,z0,prec);
end procedure;


//To test the performance

TestLaurentPerformance :=  procedure()
    F := RandomRationalFunction(5,5,10);
    time LaurentAnalysis(F,0,20);
end procedure;
//full laurent analysis on a degree 5 rational function has average time of: 52.840 s
