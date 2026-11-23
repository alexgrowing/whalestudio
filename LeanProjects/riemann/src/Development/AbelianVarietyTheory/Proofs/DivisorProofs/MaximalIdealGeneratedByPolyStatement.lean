import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealGeneratedByPoly
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_ideal_generated_by_poly : ∀ (k A R : Type) [CommRing k] [CommRing A] [CommRing R] [IsLocalRing R] [Algebra A R] (φ : MvPolynomial (Fin 1) k →+* A), φ.Etale → ∀ e : A →+* ℂ, Function.Injective (e.comp (φ.comp MvPolynomial.C)) → ∀ (q : Ideal A) [q.IsPrime] [IsLocalization.AtPrime R q], q = RingHom.ker e → ∃ P : Polynomial k, IsLocalRing.maximalIdeal R = Ideal.span {algebraMap A R (P.eval₂ (φ.comp MvPolynomial.C) (φ (MvPolynomial.X 0)))} ∧ (P = 0 ∨ P.derivative.eval₂ (e.comp (φ.comp MvPolynomial.C)) (e (φ (MvPolynomial.X 0))) ≠ 0) := by
  first | exact @GlobalTheory.etale_maximalIdeal_span_poly | exact GlobalTheory.etale_maximalIdeal_span_poly | (intros; apply GlobalTheory.etale_maximalIdeal_span_poly <;> assumption)
