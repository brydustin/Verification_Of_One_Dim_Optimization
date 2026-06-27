(* Cap theory: collects the verified numerical methods into a single import.
   Loading this theory loads every
   algorithm --- Bisection, Gradient_Descent, Fixed_Point_Method,
   Perceptron and Cholesky_Comparison --- each verified under all available
   paradigms (A: ITree/VCG, B: Lammich refinement, C: direct floating-point;
   Cholesky_Comparison has A and B). *)
theory Verified_Numerical_Methods
  imports
    Bisection
    Gradient_Descent
    Fixed_Point_Method
    Perceptron
    Cholesky_Comparison
begin

end
