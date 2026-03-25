
EVal := function( A )
    local d, f, e, n, i;
    d := Length(A);
    f := CharacteristicPolynomial(A);
    e := DurandKerner(f, [2,2]);
    if e=fail then return false; fi;
    n := List(e, CNorm);
    n := Reversed(SortedList(n));
    for i in [1..d-1] do
        if n[i] = n[i+1] then return false; fi;
    od;
    return n;
end;

Bound := function(A)
    local e, d, a1, a2, alpha1, y, t, u, v, w, r, bA, cA;

    e := EVal(A); if e = false then return false; fi;
    d := Length(A);

    # catch players for A
    a1 := e[1];
    a2 := e[2];
    alpha1 := a1/a2;

    # evaluate A
    y := Indeterminate(FLOAT_PSEUDOFIELD, "log(delta)");
    t := 1/(d-1);
    u := (alpha1^(1/2) - 1)^(-2);
    v := (a2 * a1^t)^2;
    w := 2*(d-2)*Log(1+u*v) + 4*Log(Float(2)) - 8*y;
    r := Log(alpha1);
    bA := w/r;

    # catch players for A^-1
    a1 := e[d]^-1;
    a2 := e[d-1]^-1;
    alpha1 := a1/a2;

    # evaluate Aˆ-1
    t := 1/(d-1);
    u := (alpha1^(1/2) - 1)^(-2);
    v := (a2 * a1^t)^2;
    w := 2*(d-2)*Log(1+u*v) + 4*Log(Float(2)) - 8*y;
    r := Log(alpha1);
    cA := w/r;

    return [bA, cA];
end;

Sample := function(mats, l, k)
    local F, f, m, c, i, w, A, b, r, a, res;
    F := FreeGroup(Length(mats));
    f := GeneratorsOfGroup(F);
    m := false; 
    c := 0;
    while c < l do
        w := PseudoRandom(F: radius := Random([1..k]));
        A := MappedWord(w, f, mats);
        b := Bound(A);
        if b <> false then
            r := Length(w);
            a := List(b, x -> CoefficientsOfUnivariatePolynomial(x)[1]);
            a := Filtered(a, IsFinite);
            a := Int(Maximum(a))+1;
            if m = false or m > r*a then 
                m := r*a; 
                res := [[r, a, b, A]];
            elif m = r*a then 
                AddSet(res, [r,a,b,A]);
                c := c+1;
            else
                c := c+1;
            fi;
        fi;
    od;

    return res;
end;
        
    
