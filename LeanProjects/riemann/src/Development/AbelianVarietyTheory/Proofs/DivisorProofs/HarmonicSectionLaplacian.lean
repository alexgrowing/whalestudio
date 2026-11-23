import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeContrSelfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSquaredEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.D10ProductRuleSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedDbarPartialCommutationStatement

set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.FlatAcyc

theorem harmonic_weitzenboeck {g : ℕ} (G K : Matrix (Fin g) (Fin g) ℂ) (hKG : Kᵀ * G = 2)
    (ψ : (Fin g → ℂ) → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hdd : ∀ z a c, d10 (fun z' => d01 ψ z' (ev c)) z (ev a) = -(π : ℂ) * K a c)
    (f : (Fin g → ℂ) → Ext (0 + 0 + g)) (hf : ContDiff ℝ 2 f) (hharm : ∀ z, fibreOp G ψ f z = 0)
    (z : Fin g → ℂ) (S : Finset (Fin (0 + 0 + g))) :
    ∑ a, ∑ c, G a c * (d10 (fun z' => d01 (fun z'' => f z'' S) z' (ev c)) z (ev a) +
      d10 ψ z (ev a) * d01 (fun z'' => f z'' S) z (ev c)) = 2 * π * S.card * f z S := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hψ1 : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hf01 : ∀ v, Differentiable ℝ (fun z => d01 f z v) := fun v =>
    (contDiff_d01 hf v).differentiable one_ne_zero
  have hf10 : ∀ v, Differentiable ℝ (fun z => d10 f z v) := fun v =>
    (contDiff_d10 hf v).differentiable one_ne_zero
  have hψ10 : ∀ v, Differentiable ℝ (fun z => d10 ψ z v) := fun v =>
    (contDiff_d10 hψ v).differentiable one_ne_zero
  have hA : dbarAdjF G ψ f = fun z' => -dbarF f z' := by
    funext z'; exact eq_neg_of_add_eq_zero_right (hharm z')
  have hD : dbarF f = fun z' => -dbarAdjF G ψ f z' := by
    funext z'; exact eq_neg_of_add_eq_zero_left (hharm z')
  have h1 : dbarF (dbarAdjF G ψ f) z = 0 := by
    rw [hA, dbarF_neg, GlobalTheory.T.dbar_squared_eq_zero f hf01 (d01_d01_comm_of_contDiff hf), neg_zero]
  have h2 : dbarAdjF G ψ (dbarF f) z = 0 := by
    rw [hD, dbarAdjF_neg, GlobalTheory.T.dbarAdjF_dbarAdjF_eq_zero_of_d10_symm G ψ f hf1 hψ1 hf10 hψ10 (dholo_dholo_comm hf) (dholo_dholo_comm hψ), neg_zero]
  have h3 := GlobalTheory.T.mixed_dbar_partial_commutation G ψ f hf1 hψ1 hf01 hf10 hψ10 (dbar_dholo_comm hf) z
  rw [h1, h2, add_zero (0 : Ext (0 + 0 + g))] at h3
  have h4 := congrFun h3 S

  have hK : ∀ a c d, G a c * d01 (fun z' => d10 ψ z' (ev a)) z (ev d) = -(π : ℂ) * (K a d * G a c) := by
    intro a c d; rw [dbar_dholo_comm hψ, hdd]; ring
  have hKG' : ∀ d c, ∑ a, K a d * G a c = if d = c then 2 else 0 := by
    intro d c
    have := congrFun (congrFun hKG d) c
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
    rw [this]; simp [Matrix.ofNat_apply, Matrix.one_apply]
  have hB : (∑ a, ∑ c, ∑ d, (G a c * d01 (fun z' => d10 ψ z' (ev a)) z (ev d)) •
      wedge (dzb 0 d) (contr (dzb 0 c) (f z))) S = -(2 * π * S.card * f z S) := by
    simp only [hK, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have e : ∀ (T : Fin g → Fin g → Fin g → ℂ), ∑ a, ∑ c, ∑ d, T a c d = ∑ c, ∑ d, ∑ a, T a c d := by
      intro T; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
    refine (e _).trans ?_
    have e2 : ∀ c d, ∑ a, -(π : ℂ) * (K a d * G a c) * wedge (dzb 0 d) (contr (dzb 0 c) (f z)) S =
        -(π : ℂ) * (if d = c then 2 else 0) * wedge (dzb 0 d) (contr (dzb 0 c) (f z)) S := by
      intro c d; rw [← Finset.sum_mul, ← Finset.mul_sum, hKG']
    simp only [e2, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.mul_sum, sum_wedge_contr_apply]; ring
  rw [Pi.sub_apply, hB, Pi.neg_apply] at h4
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply] at h4
  have e1 : ∀ z' v, d01 (fun z'' => f z'' S) z' v = d01 f z' v S := fun z' v => dbar_apply_component (hf1 z') S v
  have e3 : ∀ v w, d10 (fun z' => d01 f z' v S) z w = d10 (fun z' => d01 f z' v) z w S :=
    fun v w => dz_apply_component ((hf01 v) z) S w
  simp only [e1, e3]
  linear_combination h4

end GlobalTheory.TorsionForm.FlatAcyc
