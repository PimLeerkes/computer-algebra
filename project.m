function MyPartialFractionDecomposition(f)
    //first we take the regular partial fraction decomposition using the magma built in function
    decomposition := PartialFractionDecomposition(f); //TODO make own version of this

    //not all denominators are linear yet, so we need to make the necessary field extentions
    extentions := [];
    for rational_function in decomposition do
        denominator := rational_function[1];
        if Degree(denominator) gt 1 then
            Append(~extentions,denominator);
        end if;
    end for;

    //if there are extentions
    if #extentions eq 0 then
        Q_ext := BaseRing(Parent(f));
    else
        Q_ext := NumberField(extentions);
    end if;

    K<z> := RationalFunctionField(Q_ext);

    //now we compute a partial fraction decomposition again over the extended field
    new_f := K ! f;
    full_decomposition := PartialFractionDecomposition(new_f);

    return full_decomposition;
end function;

function MyGeometricSeries(f, z0, domain, p)
    //we need the following values
    numerator := f[3];
    denominator := f[1];
    n := f[2]; //the multiplicity of the denominator
    b := Coefficient(denominator,0);
    a := Coefficient(denominator,1);
    C := Parent(denominator);

    root  := -b / a;
    root := C!root;
    print(root);
    z0 := C!z0;
    r2 := C!domain[2];
    r1 := C!domain[1];

    //print(domain);
    //print(z0);
    //print(root);
    //print(r2);

    geom := [];
    if Abs(root - z0) le Abs(r2 - z0) and domain[2] ne C!1e20 then //inside a radius
        if b ne 0 then
            c := -a / b;

            for i in [0..p] do
                geom := geom cat [<c^i * 1/b^n * numerator * Binomial(n + i - 1, i),i>];
            end for;
        else
            //if b is 0 we are in the trivial case
            geom := [<numerator/a,-n>];
        end if;
    elif Abs(root - z0) ge Abs(r1 - z0) then //outside a radius
        print(b);
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
        terms := [];
        for i in [0..Degree(f)] do
            coeff := Coefficient(f, i);
            if coeff ne 0 then
                Append(~terms, <coeff, i>);
            end if;
        end for;
        return <terms,z0>;
    end if;
    
    //we first need to calculate the partial fraction decomposition (where all denominators are linear (to a power))
    decomposition := MyPartialFractionDecomposition(f_sub);

    //for each part in the decomposition we determine the geometric series and add them together
    laurent_expansion := [];
    for rational_function in decomposition do
        //we must first convert the function to a geometric series
        geom := MyGeometricSeries(rational_function, z0, domain, p);
        //print(geom);

        //we add the geometric series to our current series
        for g_term in geom do
            exponent_in_list := false;
            for i in [1..#laurent_expansion] do
                if g_term[2] eq laurent_expansion[i][2] then
                    c := g_term[1] + laurent_expansion[i][1];
                    laurent_expansion[i] := <c,laurent_expansion[i][2]>;
                    exponent_in_list := true;
                end if;
            end for;
            if exponent_in_list eq false then
                laurent_expansion := laurent_expansion cat [g_term];
            end if;
        end for;   
    end for;

    //we return the laurent expansion together with the point, which can later be used to pretty print the series substituted with the (z-point)
    return <laurent_expansion, z0>;
end function;

function PrettyLaurentSeries(laurent_series, point, p) //TODO don't print brackets if z = 0
    //pretty printer for laurent series
    F<z> := RationalFunctionField(Rationals());
    terms := [];
    for term in laurent_series do
        coeff := term[1];
        exp := term[2];
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

//the main function of this project. prints all the relevent information about the laurent/taylorexpansion of a given rational function
LaurentAnalysis := procedure(f, z0, p);
    printf "performing laurent analysis with precision: %o on function: %o around point: %o\n",p, Sprint(f), z0;

    //determine singularities
    den := Denominator(f); //TODO not all are of the right form (or are they?)
    den_f := Factorization(den);

    //we must construct our field of algebraic numbers (refactor this because it also happens elsewhere)
    extentions := [];
    for factor in den_f do
        f := factor[1];
        if Degree(f) gt 1 then
            Append(~extentions,f);
        end if;
    end for;

    //if there are extentions
    if #extentions eq 0 then
        Q_ext := BaseRing(Parent(f));
    else
        Q_ext := NumberField(extentions);
    end if;

    singularities := Roots(den, Q_ext); //TODO own root finder function
    print(singularities);

    //TODO find singularities only after pfd and also make sure you only do this decomposition once.

    print("\nsingularities: ");
    punctured := false;
    for s in singularities do
        printf "pole of order: %o at: %o\n", s[2], s[1];
        if s[1] eq z0 then
            punctured := true;
        end if;
    end for;

    //determine the different domains
    sorted_sing := Sort(singularities, func<a,b | Abs(a[1] - z0) - Abs(b[1] - z0)>);
    domains := [z0] cat [s[1] : s in sorted_sing];
    //TODO get rid of duplicate radiuses

    Append(~domains,Q_ext!1e20); //TODO infinity might also be a bit too non-algebraic

    domains := [ <domains[i], domains[i+1], false, false> : i in [1..#domains by 2] ];
    if not punctured then
        domains[1] := <domains[1][1], domains[1][2], true, false>;
    end if;

    //now we determine the laurent series for each domain
    for d in domains do
        tup := LaurentSeriesAroundPoint(f,z0,d,p);
        laurent_series := tup[1];
        point := tup[2];

        printf "\nThe laurent/taylor series around %o on domain %o is: ", z0, d; //TODO tell user if it is taylor or laurent
        print(PrettyLaurentSeries(laurent_series,point,p));

        printf "\nThe convergence radius is: %o",Abs(z0-d[2]); //TODO minimum of abses?

        for term in laurent_series do
            if term[2] eq -1 then
                printf "\nThe residue is: %o", term[1];
            end if;
        end for;
    end for;
end procedure;

//TODO elementary trancendental functions/inverses of them (automatic if we don't implement ourselves)
//TODO multivariate

function SeriesEqual(f,z0,domain,p) 
    //helper function to automatically test equality of our own implementation and magmas implementation

    //we first compute the magma laurent series around the point (how to do this in a nice way?)
    K<t> := Parent(f);
    f_sub := Evaluate(f, t + z0);
    Q := Rationals();
    L := LaurentSeriesRing(Q,p);
    magma_series := L ! f_sub;


    //we then compute our own series
    my_series := LaurentSeriesAroundPoint(f, z0, domain, p)[1];

    //we compare the coefficients
    magma_series_list := [<Coefficient(magma_series, i),i> : i in [-p/2..p/2]];

    //look for the element with coefficient i
    for term in my_series do
        term_equal := false;
        for magma_term in magma_series_list do
            if term[2] eq magma_term[2] then
                if term[1] eq magma_term[1] then
                    term_equal := true;
                end if;
            end if;
        end for;

        if term_equal then
            return true;
        else
            print(magma_series_list);
            print(my_series);
            return false;
        end if;
    end for;
    return false;
end function;

/////////////////////////////////////// Testing ////////////////////////////////////////////////

TestLaurentSeriesAroundPoint := procedure()
    //to test the laurent series around point function automatically for a list of rational functions
    Q := Rationals();
    K<z> := RationalFunctionField(Q);

    //tests around 0
    assert SeriesEqual(1/(1-z), 0, <0,1,true,false>, 20);
    assert SeriesEqual(1/(1-z)^2, 0, <0,1,true,false>, 20);
    assert SeriesEqual(1/z, 0, <0,1,true,false>,20);
    assert SeriesEqual((z - 3)/(z^2 + 1),0,<0,1,true,false>, 20); 
    assert SeriesEqual(1/z^3, 0, <0,1,true,false>, 20); 
    assert SeriesEqual(1/(z^2+2*z), 0,<0,1,true,false>, 20);
    assert SeriesEqual(z^3 + 2*z^2 + z + 4, 0,<0,1,true,false>, 20);

    //tests around a different point than 0
    assert SeriesEqual(z, 1, <0,1,true,false>, 20);
    assert SeriesEqual(1/z, 1, <0,1,true,false>, 20);
    assert SeriesEqual(1/(z^2+2*z), 1, <0,1,true,false>, 20);
    assert SeriesEqual((z - 3)/(z^2 + 1), 1/2, <0,1,true,false>, 20); 

    //TODO test around the complex number i

    //multivariate TODO
end procedure;


TestLaurentAnalysis := procedure()
    //to test the whole laurent analysis manually
    Q := Rationals();
    K<z> := RationalFunctionField(Q);
    //f := 1/(1-z);
    f := (z - 3)/(z^2 + 1);
    //f := 1/(z^2+2*z);
    prec := 20;
    z0 := 0;
    LaurentAnalysis(f,z0,prec);
end procedure;
