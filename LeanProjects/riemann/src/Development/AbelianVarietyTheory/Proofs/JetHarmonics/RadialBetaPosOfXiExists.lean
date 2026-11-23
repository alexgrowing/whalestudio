import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaIntegrandIntegrableOfXiExists
open MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.WeightedFormPos

open Formalism.FourierDecayAlt.P.JCx2 in

theorem radialBetaPos_of_xiExists (hXi : B.XiExists) : JC.RadialBetaPos := by
  intro Wp Wq _ _ _ _ _ _ P0 T j μ hμ
  obtain ⟨C1, hC1, hpair⟩ := rb_pairAt (T.bs j) μ hμ
  refine ⟨C1⁻¹, inv_pos.2 hC1, fun n x x' Φ Φ' ε _ hx hx' hΦ hΦ' => ?_⟩
  have h : P5.form μ 0 Φ Φ' 0 = (C1 : ℂ) * ∑ a, B.beta (T.bs j) (x a) (x' a) := by
    refine (rb_form_eq (k := P0.k) (r := P0.r - j) μ Φ Φ').trans ?_
    let f : Wd.Ix (Fin n) → (Fin (P0.r - j) → ℂ) × ℂ → ℂ := fun a q =>
      (bcWeight P0.k (P0.r - j) (Tz P0.k (P0.r - j) (T.bs j).z) (Tz P0.k (P0.r - j) (T.bs j).z') q : ℂ) *
        inner ℂ (B.hsVec (B.JF (T.bs j) (x' a) (B.gq (T.bs j) q))) (B.hsVec (B.JF (T.bs j) (x a) (B.gq (T.bs j) q)))
    have hint : ∀ a, Integrable (f a) := fun a =>
      betaIntegrand_integrable_of_xiExists hXi P0.k (P0.r - j) Wp Wq (T.bs j) _ (x a) (x' a) le_rfl
        ((hx a).2.1 _ 5) ((hx' a).2.1 _ 5)
    have hae : (fun c : Fin (P0.r - j) → ℂ => ((∏ a : Fin (P0.r - j), ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ b, P5.pairAt (k := P0.k) (r := P0.r - j) μ (Φ b) (Φ' b) c)
        =ᵐ[volume] fun c => ∑ b, (C1 : ℂ) * ∫ ζ, f b (c, ζ) := by
      filter_upwards [rb_ae_OmX] with c hc
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hpair (x b) (x' b) (Φ b) (Φ' b) (hΦ b) (hΦ' b) c hc, mul_left_comm, ← integral_const_mul]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      dsimp only
      rw [rb_weight hc]
      rfl
    refine (integral_congr_ae hae).trans ?_
    rw [integral_finsetSum _ (fun b _ => ((hint b).integral_prod_left).const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, ← integral_prod _ (hint b)]
    rfl
  rw [h]
  have hC : (C1 : ℂ) ≠ 0 := by exact_mod_cast hC1.ne'
  push_cast
  field_simp

theorem radialModuleForm_of_xiExists (hXi : B.XiExists) : JC.RadialModuleForm :=
  radial_module_form_of_parts (radialBetaPos_of_xiExists hXi) radial_module_action bessel_function_finite_class
    bessel_module module_regularity

end GlobalTheory.WeightedFormPos
