load "qc_modular.m";
P1<H,I> := ProjectiveSpace(Rationals(), 1);

// the main function here is find_and_test_model
//// Start: domain curve (in P^(g-1) where variables are denoted by W, X, Y, Z... we have canonical models saved in genus_*_canonical_models.m)
//// Goal: to find an affine plane patch such that no rational points from the domain curve map to bad nor infinite points. If not possible, then to have the least number of such points.
////
//// INPUT consists of eight arguments:
//// - first four are x1, x2, y1, y2 (in terms of  W, X, Y, Z..., i.e. such that x1/x2 and y1/y2 are rational functions on original homogenous space P^(g-1)) ((x1, x2, y1, y2 are in O_{P^{g-1}}(1))
//// - the fifth input is canonical model of our curve
//// - the next two inputs are simply variables for our end equation (x, y) *
//// - the last argument is a list of known rational points on a canonical model
////
//// * we used to experiment with x, -y, and similar, but in the end we managed to write all our maps so that these two arguments can always be just x and y
//// 
//// OUTPUT consists of the following:
//// 1st: resulting scheme (to repeat and understand the results, you can skip this on the first reading)
//// 2nd: Q, affine plane image of the domain curve (crucial for follow-up)
//// 3rd: components of our map from the domain curve to the projective plane
//// 4th: image of the rational points under our map to the projective plane
//// 5th: list of (potentially) good primes if Q were to be used as a single model for quadratic Chabauty, this can be empty for genus 6
//// This is also crucial for follow-up, at least for genus 4 and 5 curves.
//// The last two ouputs are lists, for each prime p these give
//// 6th: F_p-points on the domain curve that map to infinity on the image curve
//// 7th: F_p-points on the domain curve that map to bad points on the image curve
//// All computations that depend on p (5th-7th output) are performed up to max_prime, which is 50 by default.
//// This max_prime is also the only true optional parameter.
//// printlevel can give you more information about the output (set to 3 to see complete information)
//// N and bound were precision/bound arguments used in QC

function find_and_test_model_Q_only(x_num, x_denom, y_num, y_denom, domain_curve, x, y)
  map_to_P1P1 := map<domain_curve -> ProjectiveSpace(Rationals(),2) | [x_num*y_denom, x_denom*y_num, x_denom*y_denom]>;
  image_curve_non_monic_eq_xy := Evaluate(DefiningEquation(Image(map_to_P1P1)), [x, y, 1]);
  image_curve_non_monic_eq_xy := image_curve_non_monic_eq_xy / LeadingCoefficient(LeadingCoefficient(image_curve_non_monic_eq_xy));
  image_curve_non_monic_eq_xy_lc := LeadingCoefficient(image_curve_non_monic_eq_xy);
  image_curve_monic_eq := Numerator(Evaluate(image_curve_non_monic_eq_xy, y / image_curve_non_monic_eq_xy_lc));
  return image_curve_monic_eq, image_curve_non_monic_eq_xy;
end function;

function find_and_test_model(x_num, x_denom, y_num, y_denom, domain_curve, x, y, known_rat_pts : max_prime := 50, printlevel := 1, N := 20, bound := 30000)
  projective_plane<A,B,C> := ProjectiveSpace(Rationals(), 2);
  map_x := Extend(map<domain_curve -> P1 | [x_num, x_denom]>);
  map_y := Extend(map<domain_curve -> P1 | [y_num, y_denom]>);
  if printlevel gt 1 then printf "The degree of the map to P^1_x is %o.\nThe degree of the map to P^1_y is %o.\n\n", Degree(map_x), Degree(map_y); end if;
  function_field_domain_curve := FunctionField(domain_curve);

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
  image_curve_non_monic_eq := image_curve_non_monic_eq / LeadingCoefficient(LeadingCoefficient(Evaluate(image_curve_non_monic_eq, [x, y, 1])));
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
  if printlevel gt 1 then printf "\nThe equation of the affine model in A^2_{x,y} (set z = 1) is \n%o.\n", Evaluate(image_curve_non_monic_eq, [x,y,1]); end if;
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
    if Evaluate(defining_eq_bad_disks, ratx[1] / ratx[2]) eq 0 and printlevel gt 1 then printf "The image of the Q-point %o is bad for this model. (Changing the prime won't help.)\n", known_rat_pts[i]; print ratx; end if;
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
        if printlevel gt 1 then
	  print "At least one of the following is true, so we get a bad prime.";
	  printf "FpLeadingCoefficientDelta eq 0: %o\n", Fp!LeadingCoefficient(Delta) eq 0;
          Fpx:=PolynomialRing(Fp);
	  printf "Degree(r) < 1: %o\n", (Degree(r) lt 1);
	  printf "Degree(r) drops after reduction: %o\n", (not Degree(Fpx!r) eq Degree(r));
	  printf "r becomes inseparable after reduction: %o\n", (not IsSeparable(Fpx!r));
	  printf "Data not integral for W0, p: %o\n", (not is_integral(W0,p));
	  printf "Data not integral for W0inv, p: %o\n", (not is_integral(W0inv,p));
	  printf "Data not integral for Winf, p: %o\n", (not is_integral(Winf,p));
	  printf "Data not integral for Winfinv, p: %o\n", (not is_integral(Winfinv,p));
	end if;
        error "bad prime according to qc_modular";
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

  return image_curve, image_curve_eq, model_map, image_ratpts, good_primes_for_single_model, infinite_point_primes_data, bad_point_primes_data, defining_eq_bad_disks, image_curve_non_monic_leading_coefficient, image_curve_non_monic_eq;
end function;
