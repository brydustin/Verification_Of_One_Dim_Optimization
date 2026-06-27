================================================================================
  Verified Numerical Algorithms -- Malta 2026
  One theory per algorithm, three verification paradigms (A / B / C)
================================================================================

Self-contained Isabelle/HOL theories that verify each numerical algorithm under
three paradigms.  Within every algorithm file the paradigms appear in this order:

  Paradigm A   Imperative ITree program, discharged by the VCG-based Hoare
               logic  H[_] _ [_].

  Paradigm B   The same algorithm in Lammich's Refinement Framework (the nres
               monad + WHILET); termination is a WHILET_rule obligation.

  Paradigm C   A genuine IEEE-754 floating-point version, verified DIRECTLY with
               the VCG.  It sits at the bottom of each file under a section
               headed  "Paradigm C: Floating-point ... (direct, VCG)".  The
               proof reasons about the ACTUAL float iterate -- never a real
               shadow -- and accounts for all accumulated round-off in closed
               form, so the final error bound carries no iteration-dependent
               (iter * delta) drift.  The methodology, and how it improves on
               the older shadow/triangle approach, is written up in
               Float_Verification.pdf.

The per-algorithm mathematics shared across paradigms is factored into lemmas
reused by each side.


--------------------------------------------------------------------------------
  Directory contents
--------------------------------------------------------------------------------

Algorithm theories (each carries Paradigms A, B and C unless noted):

  Bisection.thy            Bisection root-finder.  Paradigm C explicitly
                           contrasts the direct proof with the older shadow/
                           triangle ("Style-B") proof.
                           Direct float bound:  |valof l - c| <= valof tol + E.

  Fixed_Point_Method.thy   Fixed-point iteration  x |-> f x  (C1 linear and
                           quadratic convergence).  Imports Taylor_Peano.
                           Direct float bound:
                             |valof x - r| <= (valof tol + E + delta)/(1 - c).

  Gradient_Descent.thy     Gradient descent in three regimes, ordered from
                           weakest to strongest assumptions:
                             (1) general nonconvex L-smooth -> eps-stationary,
                                 O(1/eps^2)   [additive progress; no envelope];
                             (2) linear under Polyak-Lojasiewicz, fixed step 1/L
                                 [geometric envelope, factor q = 1 - alpha*mu];
                             (3) quadratic  f = 1/2 x^T Q x - b^T x  with exact
                                 line search  [Kantorovich rate
                                 r2 = ((A-a)/(A+a))^2].
                           Paradigms A, B and C for all three regimes.

  Perceptron.thy           Perceptron (Novikoff mistake bound) over genuine
                           float vectors.  Direct float bound:
                             updates <= (R / gamma)^2.

  Cholesky_Comparison.thy  Cholesky (classical  A = L L^T  and square-root-free
                           A = L D L^T); the nested control-flow subject.
                           Paradigms A and B only (no floating-point paradigm
                           yet).

Shared floating-point infrastructure:

  Float_Vector.thy         Genuine float-vector library.  The IEEE entry offers
                           only the scalar float type, so float vectors are
                           modelled as lists of floats; the file defines the
                           sequential floating-point sum (fsum) and inner
                           product (fdot) and proves their FIRST-PRINCIPLES
                           accumulated round-off bounds (fsum_error,
                           fdot_error), in the style of Higham's running-error
                           analysis.  Used by Perceptron and the vector
                           Gradient_Descent regimes.

  Float_Default.thy        The single global  IEEE.float :: default  type-class
                           instance.  The instance is global, so it lives here
                           once and is imported where needed; declaring it in
                           several algorithm theories would clash as soon as two
                           of them are imported together.

  Verified_Numerical_Methods.thy
                           Cap theory: imports Bisection, Gradient_Descent,
                           Fixed_Point_Method, Perceptron and
                           Cholesky_Comparison.  Loading it loads every verified
                           method at once.

Higher-order derivative / Taylor contribution (a foundational result of the
paper -- extensions and generalisations of Isabelle's Taylor theorem and
higher-order derivatives):

  Taylor_Peano.thy                      Taylor's theorem with Peano remainder.
                                        (Imported by Fixed_Point_Method.)

  The higher-order-differentiability development it builds on now lives in the
  separate "Higher_Diffs" session (sibling directory ../Higher_Diffs): the clean
  k-times Fréchet / C^k smoothness theories, plus the recovered 1-D
  k_times_differentiable_at / C_k_on calculus in Higher_Diffs.Legacy.  The old
  in-tree Limits_Higher_Order_Derivatives, Auxiliary_Facts,
  Higher_Differentiability and Higher_Differentiability_Multi theories have been
  removed; Taylor_Peano imports Higher_Diffs.Legacy instead.

Build / session configuration:

  ROOT                     Two sessions; see "Build", below.  Depends on the
                           sibling "Higher_Diffs" session (registered via the
                           ../ROOTS file).
  deps/Numerical_Methods_Deps.thy
                           Import-aggregator for the EXTERNAL dependencies only
                           (ITree_Numeric_VCG, Refine_Monadic, Smooth_Manifolds,
                           IEEE_Floating_Point).  No project content lives here.

Write-up:

  Float_Verification.tex   Explains the floating-point approaches: the direct
  Float_Verification.pdf   constant-envelope method versus the older shadow/
                           triangle one, the additive and counting variants, the
                           guard-bridge / oracle discipline, and the
                           first-principles float-vector inner product.


--------------------------------------------------------------------------------
  Build
--------------------------------------------------------------------------------

Use the CyPhyAssure Isabelle bundle (it provides ITree_Numeric_VCG and a
registered AFP mirror for Refine_Monadic, Smooth_Manifolds and
IEEE_Floating_Point).

IMPORTANT: the `isabelle` on PATH here is Isabelle2025-2, which is NOT the right
one.  Invoke the bundle binary explicitly:

  ISA=/home/dusty/Desktop/Isabelle2025-CyPhyAssure/bin/isabelle

Build everything (the externals heap, then machine-check every project theory).
The sibling Higher_Diffs session is registered by the ../ROOTS file, so build
from the parent directory:

  "$ISA" build -d .. Numerical_Methods

The ROOT defines two sessions, split strictly along "external vs developed-here":

  Numerical_Methods_Deps  (in deps/)  The external-dependencies heap, and ONLY
                               that.  Prebuilding it is what makes every project
                               theory open quickly while staying editable.

  Numerical_Methods       (in .)      EVERYTHING developed here: Taylor_Peano,
                               Float_Vector, Float_Default, the algorithm
                               theories (all paradigms) and the cap theory.  It
                               depends on the Higher_Diffs session.  Deliberately
                               kept out of any prebuilt heap so it all stays
                               editable/inspectable in jEdit.


--------------------------------------------------------------------------------
  Edit / inspect in jEdit (fast AND editable)
--------------------------------------------------------------------------------

Open with -R, which loads the externals (Numerical_Methods_Deps) as the prebuilt
image and presents every Numerical_Methods theory as editable source -- so the
heavy externals are not recompiled, yet all project theories and their
cross-imports (e.g. the cap theory) stay editable.  Use -d .. so the sibling
Higher_Diffs session is found:

  "$ISA" jedit -d .. -R Numerical_Methods Verified_Numerical_Methods.thy

(Open any other theory the same way, or browse out from the cap theory.)

Do NOT open with  -l Numerical_Methods : that bakes the project theories into the
loaded image, making them read-only ("Cannot update finished theory").  And
-l Numerical_Methods_Deps works only for opening a leaf theory directly; a theory
that imports other project theories (the cap) needs -R so those imports resolve
as source rather than failing with "Bad theory import Numerical_Methods.*".
