import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedRatiosEvalIdealMulEqZeroSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftedRatios_eval_ideal_mul_eq_zero_succ : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)), a ∈ I → C.ev e i F = 0 → C.ev (e + 1) i (MvPolynomial.C a * F) = 0 := by
  first | exact @GlobalTheory.FormalAlg.JStep.ev_succ_C_mul_eq_zero | exact GlobalTheory.FormalAlg.JStep.ev_succ_C_mul_eq_zero | (intros; apply GlobalTheory.FormalAlg.JStep.ev_succ_C_mul_eq_zero <;> assumption)
