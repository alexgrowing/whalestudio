import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.FrameInvMulVecNegativeVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFrame

open Formalism.FourierDecayAlt.P.SettingConstruction

section forms
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)

lemma quasi_reflection (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v)
    (hne : Formalism.QuantumDeterminants.herm H u u ≠ Formalism.QuantumDeterminants.herm H u v) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  set d := u - v with hd
  set s := Formalism.QuantumDeterminants.herm H u d with hs
  have hs' : s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H u v := by rw [hs, hd, herm_sub_right]
  have hs0 : s ≠ 0 := by rw [hs']; exact sub_ne_zero.mpr hne
  have hss : star s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H v u := by
    rw [hs, herm_symm H hH, hd, herm_sub_left]
  have hq : Formalism.QuantumDeterminants.herm H d d = s + star s := by
    rw [hss, hs', hd]
    simp only [herm_sub_left, herm_sub_right]
    linear_combination -huv
  set a : ℂ := s⁻¹ with ha'
  have ha : a * s = 1 := inv_mul_cancel₀ hs0
  have hsa : star a * star s = 1 := by rw [← star_mul', ha, star_one]
  refine ⟨rk H d 1 (-a), unitary_of_form H _ fun x y => ?_, ?_, fun x hxu hxv => ?_⟩
  · rw [rk_mulVec, rk_mulVec]
    have hY : star (Formalism.QuantumDeterminants.herm H y d) = Formalism.QuantumDeterminants.herm H d y := herm_symm H hH y d
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, star_mul', hY, hq,
      star_neg, star_one]
    linear_combination (star a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * ha +
      (a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * hsa
  · rw [rk_mulVec, ← hs, neg_mul, ha, hd]
    simp
  · rw [rk_mulVec, hd, herm_sub_right, hxu, hxv]
    simp

lemma exists_isometry (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v) (h0 : Formalism.QuantumDeterminants.herm H u u ≠ 0) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  by_cases hne : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H u v
  swap
  · exact quasi_reflection H hH u v huv hne
  have e1 : Formalism.QuantumDeterminants.herm H ((-1 : ℂ) • u) ((-1 : ℂ) • u) = Formalism.QuantumDeterminants.herm H u u := by
    simp only [herm_smul_left, herm_smul_right]; simp
  obtain ⟨g₁, h1, h2, h3⟩ := quasi_reflection H hH u ((-1 : ℂ) • u) e1.symm (by
    rw [herm_smul_right]
    intro h; apply h0
    simp only [star_neg, star_one] at h
    linear_combination h / 2)
  obtain ⟨g₂, k1, k2, k3⟩ := quasi_reflection H hH ((-1 : ℂ) • u) v (e1.trans huv) (by
    rw [e1, herm_smul_left, ← hne]
    intro h; apply h0
    linear_combination h / 2)
  refine ⟨g₂ * g₁, ?_, ?_, fun x hxu hxv => ?_⟩
  · calc (g₂ * g₁)ᴴ * H * (g₂ * g₁) = g₁ᴴ * (g₂ᴴ * H * g₂) * g₁ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [k1, h1]
  · rw [← Matrix.mulVec_mulVec, h2, k2]
  · have : Formalism.QuantumDeterminants.herm H x ((-1 : ℂ) • u) = 0 := by rw [herm_smul_right, hxu, mul_zero]
    rw [← Matrix.mulVec_mulVec, h3 x hxu this, k3 x this hxv]

end forms

open PI.UpqRep PI.HwUniqW

variable {k r : ℕ}

lemma herm_right_bvec (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.herm (Hpk k r) y (bvec i) = epsI k r i * y (piI k r i) := by
  rw [← Hpk_mulVec_apply]
  simp [Formalism.QuantumDeterminants.herm, bvec, Pi.star_single]

lemma herm_bvec_eq_zero {y : Fin (2 * r + k + 1) → ℂ} (hy : inWb k r y) {i : Fin (2 * r + k + 1)}
    (hi : i.val < r ∨ r + k < i.val) : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec i) y = 0 := by
  rw [← herm_symm _ Hpk_conjTranspose, herm_right_bvec, hy (piI k r i), mul_zero, star_zero]
  rw [piI_val]
  have := i.isLt
  split_ifs <;> omega

lemma exists_isFrameW (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ g, IsFrameW k r z g := by
  set T := Tz k r z with hTdef
  set u : Fin (2 * r + k + 1) → ℂ := ((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)) with hu
  have hw : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) = -1 := by
    have hp : piI k r (wI k r (Fin.last k)) = wI k r (Fin.last k) := by
      unfold piI; rw [if_pos (by simp [wI])]
    rw [herm_right_bvec, hp, bvec_apply, if_pos rfl]
    simp [epsI, wI]
  have huu : Formalism.QuantumDeterminants.herm (Hpk k r) u u = -(T : ℂ) := by
    rw [hu, herm_smul_left, herm_smul_right, hw]
    have h1 : star ((Real.sqrt T : ℝ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ) := Complex.conj_ofReal _
    have h2 : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]
    rw [h1]
    linear_combination -h2
  have hzz : Formalism.QuantumDeterminants.herm (Hpk k r) z z = -(T : ℂ) := by
    have h1 : star (Formalism.QuantumDeterminants.herm (Hpk k r) z z) = Formalism.QuantumDeterminants.herm (Hpk k r) z z :=
      herm_symm _ Hpk_conjTranspose z z
    have h2 : T = -(Formalism.QuantumDeterminants.herm (Hpk k r) z z).re := rfl
    rw [h2, Complex.ofReal_neg, neg_neg]
    exact (Complex.conj_eq_iff_re.mp h1).symm
  have huW : inWb k r u := by
    intro i hi
    rw [hu, Pi.smul_apply, bvec_apply, if_neg, smul_zero]
    rintro rfl
    simp [wI] at hi
  obtain ⟨g, h1, h2, h3⟩ := exists_isometry (Hpk k r) Hpk_conjTranspose u z (huu.trans hzz.symm) (by
    rw [huu, neg_ne_zero]; exact_mod_cast hT.ne')
  refine ⟨g, h1, fun a => ⟨?_, ?_⟩, h2⟩
  · have ha : (eI k r a).val < r ∨ r + k < (eI k r a).val := Or.inl a.isLt
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)
  · have ha : (esI k r a).val < r ∨ r + k < (esI k r a).val := by
      have := a.isLt
      right; simp only [esI]; omega
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)

lemma blockW_fix (x : Matrix (Fin k) (Fin k) ℂ) {j : Fin (2 * r + k + 1)} (hj : ¬ InB k r j) :
    blockW k r x *ᵥ bvec j = bvec j := by
  funext i
  rw [mulVec_bvec_apply, bvec_apply]
  by_cases hi : InB k r i
  · rw [blockW_in_out _ hi hj, if_neg (ne_of_inB hi hj)]
  · rw [blockW_out _ hi]

lemma blockW_mem_UH {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    blockW k r x ∈ UH (Hpk k r) := by
  show (blockW k r x)ᴴ * Hpk k r * blockW k r x = Hpk k r
  rw [blockW_conjTranspose, ← Hpk_blockW_comm, Matrix.mul_assoc, blockW_mul, mem_UJset_allPos.mp hx,
    blockW_one, Matrix.mul_one]

lemma conj_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : IsFrameW k r z g) {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    g * blockW k r x * g⁻¹ ∈ UWset k r z := by
  refine ⟨mul_mem_UH (mul_mem_UH hg.1 (blockW_mem_UH hx)) (inv_mem_UH hg.1), fun a => ⟨?_, ?_⟩, ?_⟩
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).1,
      blockW_fix x (by unfold InB eI; simp only; omega), (hg.2.1 a).1]
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).2,
      blockW_fix x (by unfold InB esI; simp only; omega), (hg.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, frame_inv_mulVec_negativeVector hg, Matrix.mulVec_smul,
      blockW_fix x (by unfold InB wI; simp), hg.2.2]

theorem frame_exists : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∃ g, PI.UpqRep.IsFrameW k r z g ∧ (∀ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), g * PI.UpqRep.blockW k r x * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z) ∧ ∀ y ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), y = g * PI.UpqRep.blockW k r x * g⁻¹ := by
  intro k r z hz hT
  have hT' : 0 < PI.UpqRep.Tz k r z := hT
  obtain ⟨g, hg⟩ := exists_isFrameW z hz hT'
  refine ⟨g, hg, fun x hx => conj_mem_UW hg hx, fun y hy => ?_⟩
  obtain ⟨x, hx, -, e⟩ := UW_eq_conj hT' hg hy
  exact ⟨x, hx, e⟩

end GlobalTheory.BesselFrame
