load "qc_modular.m";
P1<H,I> := ProjectiveSpace(Rationals(), 1);

function find_and_test_model(x_num, x_denom, y_num, y_denom, domain_curve, x, y, known_rat_pts : max_prime := 50, printlevel := 1, N := 20, bound := 30000, skip_enough_points_check := true)
  projective_plane<A,B,C> := ProjectiveSpace(Rationals(), 2);
  map_x := Extend(map<domain_curve -> P1 | [x_num, x_denom]>);
  map_y := Extend(map<domain_curve -> P1 | [y_num, y_denom]>);
  if printlevel gt 1 then printf "The degree of the map to P^1_x is %o.\nThe degree of the map to P^1_y is %o.\n\n", Degree(map_x), Degree(map_y); end if;


  if printlevel gt 2 then
    printf "You probably want the images of rational points to stay away from infinity, i.e., avoid x(P) = [1 : 0], y(P) = [1 : 0].\n";
    for ratpt in known_rat_pts do
      printf "For P = %o, x(P) = %o and y(P) = %o.\n", ratpt, map_x(domain_curve ! ratpt), map_y(domain_curve! ratpt);
    end for;
  end if;

  // Get alternative equations because sometimes the regular equations won't be enough
  map_all_eqs := [];
  for def_x in AllDefiningPolynomials(map_x) do
    for def_y in AllDefiningPolynomials(map_y) do
      Append(~map_all_eqs, [ def_x[1], def_x[2], def_y[1], def_y[2] ]);
    end for;
  end for;
  
  // Get Magma to compute the model and force it to be monic
  map_components := [[def_xy[1] * def_xy[4], def_xy[3] * def_xy[2], def_xy[2] * def_xy[4]] : def_xy in map_all_eqs];

  map_to_P1P1 := map<domain_curve -> projective_plane | map_components>;
  map_to_P1P1 := Restriction(map_to_P1P1, Domain(map_to_P1P1), Image(map_to_P1P1));
  map_to_P1P1_degree := Degree(map_to_P1P1);

  if printlevel gt 1 then printf "Your map to P^2 has degree %o. You want this to be 1, or else it won't be an embedding.\n", map_to_P1P1_degree; end if;
  if map_to_P1P1_degree gt 1 then 
    error("Your map to P^2 is not an embedding.");
  end if;

  image_curve_non_monic_eq := DefiningEquation(Codomain(map_to_P1P1));
  if printlevel gt 1 then printf "\nThe equation of the curve in P^1_x \\times P^1_y is \n%o.\n", Evaluate(image_curve_non_monic_eq, [x,y,1]); end if;
  image_curve_non_monic_leading_coefficient := LeadingCoefficient(Evaluate(image_curve_non_monic_eq, [x, y, 1]));

  image_curve_non_monic_degree := Degree(image_curve_non_monic_leading_coefficient);
  image_curve_non_monic_leading_term := Evaluate(image_curve_non_monic_leading_coefficient, A/C);
  image_curve := Scheme(projective_plane, [Numerator( Evaluate(image_curve_non_monic_eq, [A, B/image_curve_non_monic_leading_term, C]))]);
  map_leading_coefficients := Coefficients(image_curve_non_monic_leading_coefficient);
  
  // Write out equations explicitly
  if #map_leading_coefficients ge 2 then
    map_direct_components := [[ 
      def_xy[1] * def_xy[2]^(#map_leading_coefficients - 2) * def_xy[4], 
      def_xy[3] * (&+[map_leading_coefficients[i] * (def_xy[1]^(i - 1)) * (def_xy[2]^(#map_leading_coefficients - i))  : i in [1 .. #map_leading_coefficients] ]),
      def_xy[2]^(#map_leading_coefficients - 1) * def_xy[4]
    ] : def_xy in map_all_eqs];
  else //#map_leading_coefficients eq 1 // already monic
    map_direct_components := [[ 
      def_xy[1] * def_xy[4], 
      map_leading_coefficients[1] * def_xy[3] * def_xy[2],
      def_xy[2] * def_xy[4]
    ] : def_xy in map_all_eqs];
  end if;

  image_curve_eq := Evaluate(DefiningEquation(image_curve), [x, y, 1]);
  image_curve_eq := Parent(y) ! (image_curve_eq / LeadingCoefficient(image_curve_eq));

  if not IsIrreducible(image_curve_eq) then
    error "This model for the curve is somehow not irreducible. (Changing the prime won't help.)";
  end if;
  
  model_map := map<domain_curve -> projective_plane | map_direct_components>;
  image_ratpts := [model_map(domain_curve ! ratpt) : ratpt in known_rat_pts];
  
  scheme_at_infinity_x := Scheme(domain_curve, [dp[2] : dp in AllDefiningPolynomials(map_x)]);
  scheme_at_infinity_y := Scheme(domain_curve, [dp[2] : dp in AllDefiningPolynomials(map_y)]);
  bound := 5000;
  for ratpt in known_rat_pts do
    if (model_map(domain_curve ! ratpt))[3] eq 0 and printlevel gt 1 then printf "The image of the Q-point %o lies at infinity for this model. (Changing the prime won't help.)\n", ratpt; end if;
  end for;

  defining_eq_bad_disks := SquarefreePart(Discriminant(image_curve_eq));
  roots_in_bad_disks := Roots(defining_eq_bad_disks);
  for i in [1..#known_rat_pts] do
    ratx := map_x(domain_curve ! known_rat_pts[i]);
    if ratx[2] eq 0 then
      continue;
    end if;
    if Evaluate(defining_eq_bad_disks, ratx[1] / ratx[2]) eq 0 and printlevel gt 1 then printf "The image of the Q-point %o is bad for this model. (Changing the prime won't help.)\n", known_rat_pts[i]; end if;
  end for;
  
  bad_denominator_primes := LCM([Denominator(c) : c in Coefficients(defining_eq_bad_disks)]);

  infinite_point_data_format := recformat<p, infinite_points>;
  bad_point_data_format := recformat<p, bad_points>;

  p := 2;
  bad_point_primes_data := [];
  infinite_point_primes_data := [];
  good_primes_for_single_model := [];

  while (p le max_prime) do
    Fp:=FiniteField(p);
    if printlevel gt 1 then print "\n"; end if;
    try
      if (bad_denominator_primes mod p eq 0) then
        error "bad prime because r(x) is not p-adically integral";
      end if;
      d:=Degree(image_curve_eq);
    
      A2:=AffineSpace(Fp,2);
      Fpxy:=CoordinateRing(A2);
      image_curve_modp:=Fpxy!0;
      C:=Coefficients(image_curve_eq);
      for i:=1 to #C do
        D:=Coefficients(C[i]);
        for j:=1 to #D do
            image_curve_modp:=image_curve_modp+(Fp!D[j])*Fpxy.1^(j-1)*Fpxy.2^(i-1);
        end for;
      end for;
      if not IsIrreducible(image_curve_modp) then
        error "bad prime because the mod p reduction of the model for the curve is somehow not irreducible";
      end if;

      g:=Genus(Curve(Scheme(A2,image_curve_modp)));
      r,Delta,s:=auxpolys(image_curve_eq);
      W0:=mat_W0(image_curve_eq);
      W0inv:=W0^(-1);
      Winf:=mat_Winf(image_curve_eq);
      Winfinv:=Winf^(-1);
      W:=Winf*W0^(-1);

      if (Fp!LeadingCoefficient(Delta) eq 0) or (Degree(r) lt 1) or (not smooth(r,p)) or (not (is_integral(W0,p) and is_integral(W0inv,p) and is_integral(Winf,p) and is_integral(Winfinv,p))) then
        error "bad prime according to qc_modular";
      end if;
      if skip_enough_points_check eq false then
      // check enough points...
        partial_coleman_data_format := recformat<Q,p,N,g,W0,Winf,r,Delta,s,minpolys>;
        partial_coleman_data := rec<partial_coleman_data_format|>;
        partial_coleman_data`Q := image_curve_eq; partial_coleman_data`p := p; partial_coleman_data`N := N; partial_coleman_data`g := g; partial_coleman_data`W0 := W0; partial_coleman_data`Winf := Winf; partial_coleman_data`r := r; partial_coleman_data`Delta := Delta; partial_coleman_data`s := s;
  
        Qpoints  := Q_points(partial_coleman_data, bound); // small Q-rational points
        // Affine points where Frobenius lift is defined:
        good_Qpoints := [P : P in Qpoints | not is_bad(P, partial_coleman_data) and not P`inf];
        Qppoints := Qp_points(partial_coleman_data); // One Q_p-point for every residue disk.
  
        if #Qpoints lt g+1 then  
  	error("not enough rational points on this curve to fit the height pairing");
        end if;
      
        if #good_Qpoints lt g+1 then
  	error("not enough good rational points on this affine chart to fit the height pairing, but a different affine chart might work");
        end if;
      end if;
    catch e
      if printlevel gt 1 then printf "p = %o: %o.\n", p, e; end if;
      p := NextPrime(p);
      continue;
    end try;
    domain_curve_mod_p := Reduction(domain_curve, p);
    Fp_points_at_infinity_x := [domain_curve_mod_p ! Eltseq(pt) : pt in Points(Reduction(scheme_at_infinity_x, p))];
    Fp_points_at_infinity_y := [domain_curve_mod_p ! Eltseq(pt) : pt in Points(Reduction(scheme_at_infinity_y, p))];
    Fp_points_at_infinity := Fp_points_at_infinity_x cat Fp_points_at_infinity_y;
    infinite_points_p_data := rec<infinite_point_data_format|>;
    infinite_points_p_data`p := p; infinite_points_p_data`infinite_points := Fp_points_at_infinity;
    if #Fp_points_at_infinity gt 0 then
      if printlevel gt 1 then printf "p = %o: there are %o points at infinity for the reduction modulo p.\n", p, #Fp_points_at_infinity; end if;
      Append(~infinite_point_primes_data, infinite_points_p_data);
    end if;
    Fp_bad_roots := Roots(ChangeRing(defining_eq_bad_disks, Fp));
    Fp_bad_points := [];
    for bad_x_mod_p in Fp_bad_roots do
      bad_points_upstairs := Points(Reduction(Scheme(domain_curve, [xm[1] - (Integers() ! bad_x_mod_p[1]) * xm[2] : xm in AllDefiningPolynomials(map_x)]), p));
      Fp_bad_points := Fp_bad_points cat [domain_curve_mod_p ! Eltseq(pt) : pt in bad_points_upstairs];
    end for;
    bad_points_p_data := rec<bad_point_data_format |>;
    bad_points_p_data`p := p; bad_points_p_data`bad_points := Fp_bad_points;
    if #Fp_bad_points gt 0 then
      if printlevel gt 1 then printf "p = %o: there are %o bad points for the reduction modulo p.\n", p, #Fp_bad_points; end if;
      Append(~bad_point_primes_data, bad_points_p_data);
    end if;
    if #Fp_points_at_infinity + #Fp_bad_points eq 0 then
      if printlevel gt 1 then printf "p = %o: no issues, possible candidate for a single model.\n", p; end if;
      Append(~good_primes_for_single_model, p);
    end if;
    p := NextPrime(p);
  end while;

  return image_curve, image_curve_eq, model_map, image_ratpts, good_primes_for_single_model, infinite_point_primes_data, bad_point_primes_data;
end function;
