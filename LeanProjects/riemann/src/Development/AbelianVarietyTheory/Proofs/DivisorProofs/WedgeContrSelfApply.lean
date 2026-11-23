import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic

set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.FlatAcyc

section Second
variable {g : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [Module ℂ W]
  [SMulCommClass ℝ ℂ W] [ContinuousConstSMul ℂ W]

theorem dbar_eq_half_fderiv (F : (Fin g → ℂ) → W) (z v : Fin g → ℂ) :
    d01 F z v = (1 / 2 : ℂ) • (fderiv ℝ F z v + Complex.I • fderiv ℝ F z (Complex.I • v)) := rfl

theorem dholo_eq_half_fderiv (F : (Fin g → ℂ) → W) (z v : Fin g → ℂ) :
    d10 F z v = (1 / 2 : ℂ) • (fderiv ℝ F z v + (-Complex.I) • fderiv ℝ F z (Complex.I • v)) := by
  simp only [d10, neg_smul, sub_eq_add_neg]

theorem contDiff_half {F : (Fin g → ℂ) → W} (hF : ContDiff ℝ 2 F) (s : ℂ) (v : Fin g → ℂ) :
    ContDiff ℝ 1 (fun z => (1 / 2 : ℂ) • (fderiv ℝ F z v + s • fderiv ℝ F z (Complex.I • v))) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  exact ((hD.clm_apply contDiff_const).add ((hD.clm_apply contDiff_const).const_smul s)).const_smul _

theorem contDiff_d01 {F : (Fin g → ℂ) → W} (hF : ContDiff ℝ 2 F) (v : Fin g → ℂ) :
    ContDiff ℝ 1 (fun z => d01 F z v) := by
  simpa only [dbar_eq_half_fderiv] using contDiff_half hF Complex.I v

theorem contDiff_d10 {F : (Fin g → ℂ) → W} (hF : ContDiff ℝ 2 F) (v : Fin g → ℂ) :
    ContDiff ℝ 1 (fun z => d10 F z v) := by
  simpa only [dholo_eq_half_fderiv] using contDiff_half hF (-Complex.I) v

theorem fderiv_half {F : (Fin g → ℂ) → W} (hF : ContDiff ℝ 2 F) (s : ℂ) (v z w : Fin g → ℂ) :
    fderiv ℝ (fun z' => (1 / 2 : ℂ) • (fderiv ℝ F z' v + s • fderiv ℝ F z' (Complex.I • v))) z w =
      (1 / 2 : ℂ) • (fderiv ℝ (fderiv ℝ F) z w v + s • fderiv ℝ (fderiv ℝ F) z w (Complex.I • v)) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z
  have h1 : ∀ u, HasFDerivAt (fun z' => fderiv ℝ F z' u)
      ((ContinuousLinearMap.apply ℝ W u).comp (fderiv ℝ (fderiv ℝ F) z)) z := fun u =>
    (ContinuousLinearMap.apply ℝ W u).hasFDerivAt.comp z hD.hasFDerivAt
  have h2 : HasFDerivAt (fun z' => (1 / 2 : ℂ) • (fderiv ℝ F z' v + s • fderiv ℝ F z' (Complex.I • v)))
      ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ W v).comp (fderiv ℝ (fderiv ℝ F) z) +
        s • (ContinuousLinearMap.apply ℝ W (Complex.I • v)).comp (fderiv ℝ (fderiv ℝ F) z))) z :=
    ((h1 v).add ((h1 (Complex.I • v)).const_smul s)).const_smul (1 / 2 : ℂ)
  rw [h2.fderiv]
  simp

theorem d01_d01_comm_of_contDiff {F : (Fin g → ℂ) → W} (hF : ContDiff ℝ 2 F) (z v w : Fin g → ℂ) :
    d01 (fun z' => d01 F z' v) z w = d01 (fun z' => d01 F z' w) z v := by
  have hs := (hF.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  rw [dbar_eq_half_fderiv (fun z' => d01 F z' v), dbar_eq_half_fderiv (fun z' => d01 F z' w)]
  simp only [dbar_eq_half_fderiv F]
  rw [fderiv_half hF, fderiv_half hF, fderiv_half hF, fderiv_half hF,
    hs.eq v w, hs.eq v (Complex.I • w), hs.eq (Complex.I • v) w, hs.eq (Complex.I • v) (Complex.I • w)]
  module

theorem dholo_dholo_comm {F : (Fin g → ℂ) → W} (hF : ContDiff ℝ 2 F) (z v w : Fin g → ℂ) :
    d10 (fun z' => d10 F z' v) z w = d10 (fun z' => d10 F z' w) z v := by
  have hs := (hF.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  rw [dholo_eq_half_fderiv (fun z' => d10 F z' v), dholo_eq_half_fderiv (fun z' => d10 F z' w)]
  simp only [dholo_eq_half_fderiv F]
  rw [fderiv_half hF, fderiv_half hF, fderiv_half hF, fderiv_half hF,
    hs.eq v w, hs.eq v (Complex.I • w), hs.eq (Complex.I • v) w, hs.eq (Complex.I • v) (Complex.I • w)]
  module

theorem dbar_dholo_comm {F : (Fin g → ℂ) → W} (hF : ContDiff ℝ 2 F) (z v w : Fin g → ℂ) :
    d01 (fun z' => d10 F z' v) z w = d10 (fun z' => d01 F z' w) z v := by
  have hs := (hF.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  rw [dbar_eq_half_fderiv (fun z' => d10 F z' v), dholo_eq_half_fderiv (fun z' => d01 F z' w)]
  simp only [dholo_eq_half_fderiv F, dbar_eq_half_fderiv F]
  rw [fderiv_half hF, fderiv_half hF, fderiv_half hF, fderiv_half hF,
    hs.eq v w, hs.eq v (Complex.I • w), hs.eq (Complex.I • v) w, hs.eq (Complex.I • v) (Complex.I • w)]
  module

end Second

theorem d01_neg {g m : ℕ} (F : (Fin g → ℂ) → Ext m) (z v : Fin g → ℂ) :
    d01 (fun z' => -F z') z v = -d01 F z v := by
  simp only [d01, fderiv_fun_neg, ContinuousLinearMap.neg_apply]; module

theorem dholo_neg {g m : ℕ} (F : (Fin g → ℂ) → Ext m) (z v : Fin g → ℂ) :
    d10 (fun z' => -F z') z v = -d10 F z v := by
  simp only [d10, fderiv_fun_neg, ContinuousLinearMap.neg_apply]; module

theorem wedge_neg {m : ℕ} (i : Fin m) (w : Ext m) : wedge i (-w) = -wedge i w := by
  simpa using wedge_smul i (-1) w

theorem contr_neg {m : ℕ} (i : Fin m) (w : Ext m) : contr i (-w) = -contr i w := by
  simpa using contr_smul i (-1) w

theorem dbarF_neg {g : ℕ} (F : (Fin g → ℂ) → Ext (0 + 0 + g)) (z : Fin g → ℂ) :
    dbarF (fun z' => -F z') z = -dbarF F z := by
  simp only [dbarF, d01_neg, wedge_neg, Finset.sum_neg_distrib]

theorem dbarAdjF_neg {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (ψ : (Fin g → ℂ) → ℂ)
    (F : (Fin g → ℂ) → Ext (0 + 0 + g)) (z : Fin g → ℂ) :
    dbarAdjF G ψ (fun z' => -F z') z = -dbarAdjF G ψ F z := by
  simp only [dbarAdjF, dholo_neg, smul_neg, ← neg_add, contr_neg, Finset.sum_neg_distrib]

theorem wedge_contr_self_apply {m : ℕ} (i : Fin m) (w : Ext m) (S : Finset (Fin m)) :
    wedge i (contr i w) S = if i ∈ S then w S else 0 := by
  have h := congrFun (wedge_contr_add i w) S
  simp only [Pi.add_apply] at h
  split_ifs with hi
  · have : contr i (wedge i w) S = 0 := by simp [contr, hi]
    rw [this, add_zero] at h; exact h
  · simp [wedge, hi]

theorem dzb_bijective {g : ℕ} : Function.Bijective (dzb 0 : Fin g → Fin (0 + 0 + g)) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, by simp⟩
  intro a b h; simpa [dzb] using h

theorem sum_wedge_contr_apply {g : ℕ} (w : Ext (0 + 0 + g)) (S : Finset (Fin (0 + 0 + g))) :
    ∑ c : Fin g, wedge (dzb 0 c) (contr (dzb 0 c) w) S = S.card * w S := by
  simp only [wedge_contr_self_apply]
  rw [Fintype.sum_bijective _ dzb_bijective _ (fun i => if i ∈ S then w S else 0) (fun _ => rfl)]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.TorsionForm.FlatAcyc
