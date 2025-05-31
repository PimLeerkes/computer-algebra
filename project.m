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

function MyGeometricSeries(f, p)
    //f needs to be of the correct form

    //we need the following three values for further computation
    numerator := f[3];
    denominator := f[1];
    n := f[2];
    b := Coefficient(denominator,0);
    a := Coefficient(denominator,1);
    x := Parent(denominator).1;

    //we factor the constant term out of the denominator n times (if nonzero)
    if b ne 0 then
        c := a / b^n;

        //we make the geometric series
        geom := 0;
        for i in [0..p] do
            geom +:= (-c*x)^i;
        end for;
        geom *:= 1/b^n * numerator;
        return geom;
    else
        //if b is 0 we are in the trivial case
        return numerator/denominator^n;
    end if;

end function;

function LaurentSeriesAroundPoint(f, z0, p)
    //z0 needs to be a point in the complex numbers
    //f needs to be a rational function
    //assert Parent(z0) eq ComplexField();

    //we first need to deretmine the singularities?
    
    //substitute t := z - z0 => z := t + z0
    K<t> := Parent(f);
    f_sub := Evaluate(f, t + z0);

    //we first need to calculate the partial fraction decomposition (where all denominators are linear (to a power))
    decomposition := MyPartialFractionDecomposition(f_sub);

    //for each part in the decomposition we determine the geometric series and add them together
    laurent_expansion := 0;
    for rational_function in decomposition do
        //we must first convert the function to a geometric series
        geom := MyGeometricSeries(rational_function, p);
        laurent_expansion +:= geom;
    end for;

    //we return the laurent expansion together with the point, which can later be used to pretty print the series
    return <laurent_expansion, z0>;
end function;

//the main function of this project. prints all the relevent information about the laurent/taylorexpansion of a given rational function
LaurentAnalysis := procedure(f, z0, p);
    print("performing laurent analysis on (rational) function");

    //determine singularities
    C := ComplexField(4);
    den := Denominator(f); //TODO not all are of the right form
    singularities := Roots(den,C);

    print("singularities: ");
    punctured := false;
    for s in singularities do
        printf "pole of order: %o at: %o\n", s[2], s[1];
        if s[1] eq z0 then
            punctured := true;
        end if;
    end for;

    //determine domains
    //domains := [];
    //if punctured eq true then
    //    domains := domains cat [<z0,z0>];
    //end if;

    laurent_series := LaurentSeriesAroundPoint(f,z0,p)[1];
    print(Type(laurent_series));
    point := LaurentSeriesAroundPoint(f,z0,p)[2];

    S<z> := PolynomialRing(Rationals());
    terms := [ Coefficient(laurent_series, i)*((z - point)^i) : i in Exponents(laurent_series) ];
    g := &+ terms;
    print(g);


    //calculate series around the domains

    //calculate residue

    //print everything
end procedure;

//TODO elementary trancendental functions/inverses of them (automatic if we don't implement ourselves)
//TODO multivariate
//TODO general rings
//TODO singularities
//TODO residues

function SeriesEqual(f,z0,p) 
    //helper function to automatically test equality of our own implementation and magmas implementation

    //we first compute the magma laurent series around the point (how to do this in a nice way?)
    K<t> := Parent(f);
    f_sub := Evaluate(f, t + z0);
    Q := Rationals();
    L := LaurentSeriesRing(Q,p);
    magma_series := L ! f_sub;

    //then we cast our laurent series to a magma laurent series to compare them
    my_series := LaurentSeriesAroundPoint(f, z0, p)[0];
    my_series := L ! my_series;

    if [Coefficient(my_series, i) : i in [-p/2..p/2]] eq
       [Coefficient(magma_series, i) : i in [-p/2..p/2]] then
       return true;
    else
        print(magma_series);
        print(my_series);
        return false;
    end if;
end function;

/////////////////////////////////////// Testing ////////////////////////////////////////////////

AutomaticTestLaurentSeriesAroundPoint := procedure()
    //to test the laurent series around point function automatically for a list of rational functions
    Q := Rationals();
    K<z> := RationalFunctionField(Q);

    //TODO z0 must be complex

    //tests around 0
    assert SeriesEqual(1/(1-z), 0, 20);
    assert SeriesEqual(1/z, 0, 20);
    assert SeriesEqual((z - 3)/(z^2 + 1), 0, 20); 
    assert SeriesEqual(1/z^3, 0, 20); 
    assert SeriesEqual(1/(z^2+2*z), 0, 20);

    //tests around a different point than 0
    assert SeriesEqual(z, 1, 20);
    assert SeriesEqual(1/z, 1, 20);
    assert SeriesEqual(1/(z^2+2*z), 1, 20);
    assert SeriesEqual((z - 3)/(z^2 + 1), 1/2, 20); 

    //TODO test around i

    //multivariate TODO
end procedure;


ManualTestLaurentSeriesAroundPoint := procedure()
    //to test the whole laurent analysis manually
    Q := Rationals();
    K<z> := RationalFunctionField(Q);
    f := 1/(1-z);
    prec := 20;
    z0 := 0;
    LaurentAnalysis(f,z0,prec);
end procedure;
