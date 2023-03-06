//this is a necessary part of the model_equation_finder from
//https://github.com/AWS2020QC/ModularCurvesX0plusG4-6

P1<H,I> := ProjectiveSpace(Rationals(), 1);

// the main function here is find_and_test_model
//// Start: domain curve (in P^(g-1) where variables are denoted by W, X, Y, Z... we have canonical models saved in genus_*_canonical_models.m)
//// Goal: to find an affine plane patch such that no rational points from the domain curve map to bad nor infinite points. If not possible, then to have the least number of such points.
////
//// INPUT consists of seven arguments:
//// - first four are x1, x2, y1, y2 (in terms of  W, X, Y, Z..., i.e. such that x1/x2 and y1/y2 are rational functions on original homogenous space P^(g-1)) ((x1, x2, y1, y2 are in O_{P^{g-1}}(1))
//// - the fifth input is canonical model of our curve
//// - the next two inputs are simply variables for our end equation (x, y) 

//// OUTPUT consists of the following:
//// Q, affine plane image of the domain curve (crucial for follow-up)

function find_and_test_model_Q_only(x_num, x_denom, y_num, y_denom, domain_curve, x, y)
  map_to_P1P1 := map<domain_curve -> ProjectiveSpace(Rationals(),2) | [x_num*y_denom, x_denom*y_num, x_denom*y_denom]>;
  image_curve_non_monic_eq_xy := Evaluate(DefiningEquation(Image(map_to_P1P1)), [x, y, 1]);
  image_curve_non_monic_eq_xy := image_curve_non_monic_eq_xy / LeadingCoefficient(LeadingCoefficient(image_curve_non_monic_eq_xy));
  image_curve_non_monic_eq_xy_lc := LeadingCoefficient(image_curve_non_monic_eq_xy);
  image_curve_monic_eq := Numerator(Evaluate(image_curve_non_monic_eq_xy, y / image_curve_non_monic_eq_xy_lc));
  return image_curve_monic_eq, image_curve_non_monic_eq_xy;
end function;
