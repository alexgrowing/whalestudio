import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf

noncomputable section

open Matrix MeasureTheory Formalism.L2.SG.HidaSetting Formalism.QuantumDeterminants
open scoped InnerProductSpace

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.L2.SG.Pf.WFL

variable {k r : ℕ}

theorem idx_cases (i : Fin (2 * r + k + 1)) :
    (∃ a : Fin r, i = eI k r a) ∨ (∃ c : Fin (k + 1), i = wI k r c) ∨ (∃ a : Fin r, i = esI k r a) := by
  have hi := i.isLt
  by_cases h : i.val < r
  · exact Or.inl ⟨⟨i.val, h⟩, Fin.ext rfl⟩
  · by_cases h2 : i.val ≤ r + k
    · refine Or.inr (Or.inl ⟨⟨i.val - r, by omega⟩, Fin.ext ?_⟩)
      simp only [wI]; omega
    · refine Or.inr (Or.inr ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext ?_⟩)
      simp only [esI, Fin.val_mk]; omega

def colQ (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (wf : Fin k → Fin (2 * r + k + 1) → ℂ)
    (z0 : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h : j.val < r then e ⟨j.val, h⟩
  else if h2 : j.val < r + k then wf ⟨j.val - r, by omega⟩
  else if h3 : j.val = r + k then z0
  else f ⟨2 * r + k - j.val, by have := j.isLt; omega⟩

section Col
variable (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (wf : Fin k → Fin (2 * r + k + 1) → ℂ)
  (z0 : Fin (2 * r + k + 1) → ℂ)

theorem eI_val (a : Fin r) : (eI k r a).val = a.val := rfl
theorem wI_val (c : Fin (k + 1)) : (wI k r c).val = r + c.val := rfl
theorem esI_val (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := rfl

theorem colQ_eI (a : Fin r) : colQ e f wf z0 (eI k r a) = e a := by
  unfold colQ; rw [dif_pos (by rw [eI_val]; exact a.isLt)]; rfl

theorem colQ_wI (c : Fin (k + 1)) (hc : c.val < k) : colQ e f wf z0 (wI k r c) = wf ⟨c.val, hc⟩ := by
  unfold colQ
  rw [dif_neg (by rw [wI_val]; omega), dif_pos (by rw [wI_val]; omega)]
  congr 1; apply Fin.ext; show r + c.val - r = c.val; omega

theorem colQ_wI_last (c : Fin (k + 1)) (hc : c.val = k) : colQ e f wf z0 (wI k r c) = z0 := by
  unfold colQ
  rw [dif_neg (by rw [wI_val]; omega), dif_neg (by rw [wI_val]; omega), dif_pos (by rw [wI_val]; omega)]

theorem colQ_esI (a : Fin r) : colQ e f wf z0 (esI k r a) = f a := by
  have ha := a.isLt
  unfold colQ
  rw [dif_neg (by rw [esI_val]; omega), dif_neg (by rw [esI_val]; omega), dif_neg (by rw [esI_val]; omega)]
  congr 1; apply Fin.ext; show 2 * r + k - (2 * r + k - a.val) = a.val; omega

def Qm : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of fun i j => colQ e f wf z0 j i

theorem Qm_mulVec_bvec (j : Fin (2 * r + k + 1)) : Qm e f wf z0 *ᵥ bvec j = colQ e f wf z0 j := by
  ext i; simp [Qm, bvec, mulVec, dotProduct, Pi.single_apply]

end Col

theorem hJ_swap {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  simp only [hJ, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp <;> ring

theorem gram_apply {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (Mᴴ * Formalism.REAL.Jm ε * M) i j = hJ ε (fun t => M t i) (fun t => M t j) := by
  simp only [hJ, Matrix.mul_apply, conjTranspose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum, Pi.star_apply,
    mul_assoc]
  exact Finset.sum_comm

structure IsFrameJ {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 : Fin (2 * r + k + 1) → ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ez : ∀ a, hJ ε (e a) z0 = 0
  fz : ∀ a, hJ ε (f a) z0 = 0
  zz : hJ ε z0 z0 = -1
  ww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0
  ew : ∀ c a, hJ ε (e c) (wf a) = 0
  fw : ∀ c a, hJ ε (f c) (wf a) = 0
  zw : ∀ a, hJ ε z0 (wf a) = 0

theorem Hpk_sig (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = (GBasic.sig k r i).val then GBasic.sgn k r i else 0 := by
  rw [GBasic.Hpk_eq]; simp only [Fin.ext_iff]

theorem sig_eI (a : Fin r) : (GBasic.sig k r (eI k r a)).val = 2 * r + k - a.val := by
  rw [GBasic.sig_lo _ _ _ (by rw [eI_val]; exact a.isLt), eI_val]
theorem sig_wI (c : Fin (k + 1)) : (GBasic.sig k r (wI k r c)).val = r + c.val := by
  rw [GBasic.sig_mid _ _ _ (by rw [wI_val]; omega) (by rw [wI_val]; have := c.isLt; omega), wI_val]
theorem sig_esI (a : Fin r) : (GBasic.sig k r (esI k r a)).val = a.val := by
  rw [GBasic.sig_hi _ _ _ (by rw [esI_val]; have := a.isLt; omega), esI_val]; have := a.isLt; omega

section HpkVals
variable (k r)
theorem sgn_eI (a : Fin r) : GBasic.sgn k r (eI k r a) = 1 := by
  unfold GBasic.sgn; rw [if_neg (by rw [eI_val]; have := a.isLt; omega)]
theorem sgn_esI (a : Fin r) : GBasic.sgn k r (esI k r a) = 1 := by
  unfold GBasic.sgn; rw [if_neg (by rw [esI_val]; have := a.isLt; omega)]
theorem Hpk_ee (a b : Fin r) : Hpk k r (eI k r a) (eI k r b) = 0 := by
  rw [Hpk_sig, if_neg (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]; have := a.isLt; have := b.isLt; omega)]
theorem Hpk_ew (a : Fin r) (c : Fin (k + 1)) : Hpk k r (eI k r a) (wI k r c) = 0 := by
  rw [Hpk_sig, if_neg (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]; have := a.isLt; have := c.isLt; omega)]
theorem Hpk_ef (a b : Fin r) : Hpk k r (eI k r a) (esI k r b) = if a = b then 1 else 0 := by
  rw [Hpk_sig]
  by_cases hab : a = b
  · subst hab; rw [if_pos (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]), if_pos rfl, sgn_eI]
  · have : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rw [if_neg (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]; have := a.isLt; have := b.isLt; omega), if_neg hab]
theorem Hpk_we (c : Fin (k + 1)) (a : Fin r) : Hpk k r (wI k r c) (eI k r a) = 0 := by
  rw [Hpk_sig, if_neg (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]; have := a.isLt; omega)]
theorem Hpk_ww (c d : Fin (k + 1)) : Hpk k r (wI k r c) (wI k r d) =
    if c = d then (if c.val = k then -1 else 1) else 0 := by
  rw [Hpk_sig]
  by_cases hcd : c = d
  · subst hcd; rw [if_pos (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]), if_pos rfl]; unfold GBasic.sgn
    by_cases hck : c.val = k
    · rw [if_pos (by rw [wI_val]; omega), if_pos hck]
    · rw [if_neg (by rw [wI_val]; omega), if_neg hck]
  · have : c.val ≠ d.val := fun h => hcd (Fin.ext h)
    rw [if_neg (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]; omega), if_neg hcd]
theorem Hpk_wf (c : Fin (k + 1)) (a : Fin r) : Hpk k r (wI k r c) (esI k r a) = 0 := by
  rw [Hpk_sig, if_neg (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]; have := a.isLt; have := c.isLt; omega)]
theorem Hpk_fe (a b : Fin r) : Hpk k r (esI k r a) (eI k r b) = if a = b then 1 else 0 := by
  rw [Hpk_sig]
  by_cases hab : a = b
  · subst hab; rw [if_pos (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]), if_pos rfl, sgn_esI]
  · have : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rw [if_neg (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]; omega), if_neg hab]
theorem Hpk_fw (a : Fin r) (c : Fin (k + 1)) : Hpk k r (esI k r a) (wI k r c) = 0 := by
  rw [Hpk_sig, if_neg (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]; have := a.isLt; omega)]
theorem Hpk_ff (a b : Fin r) : Hpk k r (esI k r a) (esI k r b) = 0 := by
  rw [Hpk_sig, if_neg (by simp only [sig_eI, sig_wI, sig_esI, eI_val, wI_val, esI_val]; have := a.isLt; have := b.isLt; omega)]
end HpkVals

theorem gramQ {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0) :
    (Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * Qm e f wf z0 = Hpk k r := by
  ext i j
  rw [gram_apply]
  have hc : ∀ j, (fun t => Qm e f wf z0 t j) = colQ e f wf z0 j := fun j => by ext t; rfl
  rw [hc, hc]
  rcases idx_cases (k := k) (r := r) i with ⟨a, rfl⟩ | ⟨c, rfl⟩ | ⟨a, rfl⟩ <;>
  rcases idx_cases (k := k) (r := r) j with ⟨b, rfl⟩ | ⟨d, rfl⟩ | ⟨b, rfl⟩
  · rw [colQ_eI, colQ_eI, hF.ee, Hpk_ee]
  · by_cases hdk : d.val < k
    · rw [colQ_eI, colQ_wI _ _ _ _ _ hdk, hF.ew, Hpk_ew]
    · rw [colQ_eI, colQ_wI_last _ _ _ _ _ (by have := d.isLt; omega), hF.ez, Hpk_ew]
  · rw [colQ_eI, colQ_esI, hF.ef, Hpk_ef]
  · by_cases hck : c.val < k
    · rw [colQ_wI _ _ _ _ _ hck, colQ_eI, hJ_swap, hF.ew, star_zero, Hpk_we]
    · rw [colQ_wI_last _ _ _ _ _ (by have := c.isLt; omega), colQ_eI, hJ_swap, hF.ez, star_zero, Hpk_we]
  · rw [Hpk_ww]
    by_cases hck : c.val < k <;> by_cases hdk : d.val < k
    · rw [colQ_wI _ _ _ _ _ hck, colQ_wI _ _ _ _ _ hdk, hF.ww]
      by_cases hcd : c = d
      · subst hcd; rw [if_pos rfl, if_pos rfl, if_neg (by omega)]
      · have hv : c.val ≠ d.val := fun h => hcd (Fin.ext h)
        have h1 : ¬ (⟨c.val, hck⟩ : Fin k) = ⟨d.val, hdk⟩ := fun h => hv (Fin.mk.inj h)
        rw [if_neg h1, if_neg hcd]
    · rw [colQ_wI _ _ _ _ _ hck, colQ_wI_last _ _ _ _ _ (by have := d.isLt; omega), hJ_swap, hF.zw, star_zero,
        if_neg (fun h => by subst h; omega)]
    · rw [colQ_wI_last _ _ _ _ _ (by have := c.isLt; omega), colQ_wI _ _ _ _ _ hdk, hF.zw,
        if_neg (fun h => by subst h; omega)]
    · have e1 : c = d := Fin.ext (by have := c.isLt; have := d.isLt; omega)
      subst e1
      rw [colQ_wI_last _ _ _ _ _ (by have := c.isLt; omega), hF.zz, if_pos rfl, if_pos (by have := c.isLt; omega)]
  · by_cases hck : c.val < k
    · rw [colQ_wI _ _ _ _ _ hck, colQ_esI, hJ_swap, hF.fw, star_zero, Hpk_wf]
    · rw [colQ_wI_last _ _ _ _ _ (by have := c.isLt; omega), colQ_esI, hJ_swap, hF.fz, star_zero, Hpk_wf]
  · rw [colQ_esI, colQ_eI, hJ_swap, hF.ef, Hpk_fe]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (Ne.symm hab), if_neg hab, star_zero]
  · by_cases hdk : d.val < k
    · rw [colQ_esI, colQ_wI _ _ _ _ _ hdk, hF.fw, Hpk_fw]
    · rw [colQ_esI, colQ_wI_last _ _ _ _ _ (by have := d.isLt; omega), hF.fz, Hpk_fw]
  · rw [colQ_esI, colQ_esI, hF.ff, Hpk_ff]

section Frame
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

variable (ε e f wf z0) in

def Qi : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Hpk k r * (Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε

theorem cay_BA {m : ℕ} {A B J H : Matrix (Fin m) (Fin m) ℂ} (hA : Aᴴ * J * A = H) (hH : H * H = 1)
    (hB : B = H * Aᴴ * J) : B * A = 1 := by
  subst hB; rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, hH]

theorem cay_AB {m : ℕ} {A B J H : Matrix (Fin m) (Fin m) ℂ} (hA : Aᴴ * J * A = H) (hH : H * H = 1)
    (hB : B = H * Aᴴ * J) : A * B = 1 :=
  (mul_eq_one_comm_of_card_eq (Fin m) (Fin m) ℂ rfl).mp (cay_BA hA hH hB)

theorem cay_AHA {m : ℕ} {A B J H : Matrix (Fin m) (Fin m) ℂ} (hA : Aᴴ * J * A = H) (hH : H * H = 1)
    (hJ : J * J = 1) (hB : B = H * Aᴴ * J) : A * H * Aᴴ = J := by
  have h := cay_AB hA hH hB
  rw [hB] at h
  calc A * H * Aᴴ = A * H * Aᴴ * (J * J) := by rw [hJ, Matrix.mul_one]
    _ = (A * (H * Aᴴ * J)) * J := by simp only [Matrix.mul_assoc]
    _ = J := by rw [h, Matrix.one_mul]

theorem cay_BHB {m : ℕ} {A B J H : Matrix (Fin m) (Fin m) ℂ} (hA : Aᴴ * J * A = H) (hH : H * H = 1)
    (hJ : J * J = 1) (hJh : Jᴴ = J) (hHh : Hᴴ = H) (hB : B = H * Aᴴ * J) : Bᴴ * H * B = J := by
  have h3 := cay_AHA hA hH hJ hB
  subst hB
  simp only [conjTranspose_mul, hJh, hHh, conjTranspose_conjTranspose]
  calc _ = J * (A * (H * H) * H * Aᴴ) * J := by simp only [Matrix.mul_assoc]
    _ = J := by rw [hH, Matrix.mul_one, h3, hJ, Matrix.one_mul]

theorem cay_conj {m : ℕ} {A B J H g : Matrix (Fin m) (Fin m) ℂ} (hA : Aᴴ * J * A = H) (hBHB : Bᴴ * H * B = J)
    (hg : gᴴ * J * g = J) : (B * g * A)ᴴ * H * (B * g * A) = H := by
  simp only [conjTranspose_mul]
  calc _ = Aᴴ * (gᴴ * (Bᴴ * H * B) * g) * A := by simp only [Matrix.mul_assoc]
    _ = Aᴴ * J * A := by rw [hBHB, hg, Matrix.mul_assoc]
    _ = H := hA

theorem Qi_mul_Qm (hF : IsFrameJ ε e f wf z0) : Qi ε e f wf z0 * Qm e f wf z0 = 1 :=
  cay_BA (gramQ hF) (GBasic.Hpk_sq k r) rfl

theorem Qm_mul_Qi (hF : IsFrameJ ε e f wf z0) : Qm e f wf z0 * Qi ε e f wf z0 = 1 :=
  cay_AB (gramQ hF) (GBasic.Hpk_sq k r) rfl

theorem QiHQi (hF : IsFrameJ ε e f wf z0) :
    (Qi ε e f wf z0)ᴴ * Hpk k r * Qi ε e f wf z0 = Formalism.REAL.Jm ε :=
  cay_BHB (gramQ hF) (GBasic.Hpk_sq k r) (Formalism.REAL.Jm_mul_self ε) (Formalism.REAL.Jm_conjTranspose ε) (GBasic.Hpk_herm k r) rfl

theorem conj_mem_UH (hF : IsFrameJ ε e f wf z0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε) :
    Qi ε e f wf z0 * g * Qm e f wf z0 ∈ UH (Hpk k r) :=
  cay_conj (gramQ hF) (QiHQi hF) hg

theorem Hpk_mulVec (t : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ t) i = GBasic.sgn k r i * t (GBasic.sig k r i) := by
  simp [mulVec, dotProduct, GBasic.Hpk_eq]

theorem Qi_mulVec (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Qi ε e f wf z0 *ᵥ y) i = GBasic.sgn k r i * hJ ε (colQ e f wf z0 (GBasic.sig k r i)) y := by
  unfold Qi
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Hpk_mulVec]
  congr 1
  all_goals simp only [hJ, mulVec, dotProduct, conjTranspose_apply, Qm, Matrix.of_apply, Pi.star_apply]

theorem sig_eI_eq (a : Fin r) : GBasic.sig k r (eI k r a) = esI k r a := Fin.ext (by rw [sig_eI, esI_val])

theorem Qi_mulVec_eI (y : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Qi ε e f wf z0 *ᵥ y) (eI k r a) = hJ ε (f a) y := by
  rw [Qi_mulVec, sgn_eI, sig_eI_eq, colQ_esI, one_mul]

theorem Qi_mulVec_col (hF : IsFrameJ ε e f wf z0) (j : Fin (2 * r + k + 1)) :
    Qi ε e f wf z0 *ᵥ colQ e f wf z0 j = bvec j := by
  rw [← Qm_mulVec_bvec, Matrix.mulVec_mulVec, Qi_mul_Qm hF, Matrix.one_mulVec]

theorem bvec_apply (i j : Fin (2 * r + k + 1)) : bvec j i = if i = j then 1 else 0 := by
  simp [bvec, Pi.single_apply]

theorem mat_apply_bvec {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : M i j = (M *ᵥ bvec j) i := by
  simp [mulVec, dotProduct, bvec, Pi.single_apply]

theorem conj_apply (i j : Fin (2 * r + k + 1)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (Qi ε e f wf z0 * g * Qm e f wf z0) i j = (Qi ε e f wf z0 *ᵥ (g *ᵥ colQ e f wf z0 j)) i := by
  rw [mat_apply_bvec (Qi ε e f wf z0 * g * Qm e f wf z0) i j, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Qm_mulVec_bvec]

theorem coord_span_zero (i : Fin (2 * r + k + 1)) (S : Set (Fin (2 * r + k + 1) → ℂ))
    (hS : ∀ x ∈ S, (Qi ε e f wf z0 *ᵥ x) i = 0) {y : Fin (2 * r + k + 1) → ℂ} (hy : y ∈ Submodule.span ℂ S) :
    (Qi ε e f wf z0 *ᵥ y) i = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Matrix.mulVec_smul, Pi.smul_apply, hx, smul_zero]

theorem Qi_e (hF : IsFrameJ ε e f wf z0) (b : Fin r) : Qi ε e f wf z0 *ᵥ e b = bvec (eI k r b) := by
  rw [← colQ_eI e f wf z0 b, Qi_mulVec_col hF]

theorem Qi_f (hF : IsFrameJ ε e f wf z0) (b : Fin r) : Qi ε e f wf z0 *ᵥ f b = bvec (esI k r b) := by
  rw [← colQ_esI e f wf z0 b, Qi_mulVec_col hF]

theorem conj_mem_UWset (hF : IsFrameJ ε e f wf z0) {zB z : Fin (2 * r + k + 1) → ℂ}
    (hz : Qm e f wf z0 *ᵥ zB = z) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε) (he : ∀ a, h *ᵥ e a = e a) (hf : ∀ a, h *ᵥ f a = f a)
    (hzz : h *ᵥ z = z) : Qi ε e f wf z0 * h * Qm e f wf z0 ∈ UWset k r zB := by
  refine ⟨conj_mem_UH hF hU, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Qm_mulVec_bvec, colQ_eI, he, Qi_e hF]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Qm_mulVec_bvec, colQ_esI, hf, Qi_f hF]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz, hzz, ← hz, Matrix.mulVec_mulVec, Qi_mul_Qm hF,
      Matrix.one_mulVec]

theorem Qi_e_apply (hF : IsFrameJ ε e f wf z0) (b : Fin r) (i : Fin (2 * r + k + 1)) (hi : i ≠ eI k r b) :
    (Qi ε e f wf z0 *ᵥ e b) i = 0 := by
  rw [Qi_e hF, bvec_apply, if_neg hi]

theorem conj_mem_Nset (hF : IsFrameJ ε e f wf z0) {z : Fin (2 * r + k + 1) → ℂ}
    (hz0 : ∃ t : ℂ, z0 = t • z) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : nᴴ * Formalism.REAL.Jm ε * n = Formalism.REAL.Jm ε) (hN : InN ε e z n) :
    Qi ε e f wf z0 * n * Qm e f wf z0 ∈ Nset k r := by
  refine ⟨conj_mem_UH hF hU, ?_, ?_⟩
  · intro a i hai
    rw [conj_apply, colQ_eI]
    obtain ⟨y, hy, hny⟩ : ∃ y ∈ spanLt e a.val, n *ᵥ e a = e a + y :=
      ⟨(n - 1) *ᵥ e a, hN.1.1 a, by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel⟩
    rw [hny, Matrix.mulVec_add, Pi.add_apply, Qi_e hF, bvec_apply]
    have h0 : (Qi ε e f wf z0 *ᵥ y) i = 0 := by
      refine coord_span_zero i _ ?_ hy
      rintro x ⟨b, hb, rfl⟩
      refine Qi_e_apply hF b i ?_
      intro h; have := congrArg Fin.val h; rw [eI_val] at this; simp only [Set.mem_setOf_eq] at hb; omega
    rw [h0, add_zero]
  · intro i j hj1 hj2 hi
    obtain ⟨c, rfl⟩ : ∃ c : Fin (k + 1), j = wI k r c := ⟨⟨j.val - r, by omega⟩, Fin.ext (by rw [wI_val]; simp only; omega)⟩
    rw [conj_apply]
    have hperp : ∀ a, hJ ε (e a) (colQ e f wf z0 (wI k r c)) = 0 := by
      intro a
      by_cases hck : c.val < k
      · rw [colQ_wI _ _ _ _ _ hck, hF.ew]
      · rw [colQ_wI_last _ _ _ _ _ (by have := c.isLt; omega), hF.ez]
    obtain ⟨y, hy, hny⟩ : ∃ y ∈ spanLt e r, n *ᵥ colQ e f wf z0 (wI k r c) = colQ e f wf z0 (wI k r c) + y :=
      ⟨(n - 1) *ᵥ colQ e f wf z0 (wI k r c), hN.2 _ hperp, by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel⟩
    rw [hny, Matrix.mulVec_add, Pi.add_apply, Qi_mulVec_col hF, bvec_apply]
    have h0 : (Qi ε e f wf z0 *ᵥ y) i = 0 := by
      refine coord_span_zero i _ ?_ hy
      rintro x ⟨b, hb, rfl⟩
      refine Qi_e_apply hF b i ?_
      intro h; have := congrArg Fin.val h; rw [eI_val] at this; have := b.isLt; omega
    rw [h0, add_zero]

end Frame

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

theorem gram_apply' {n : ℕ} (G M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (Mᴴ * G * M) i j = star (fun t => M t i) ⬝ᵥ (G *ᵥ fun t => M t j) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum, Pi.star_apply,
    mul_assoc]
  exact Finset.sum_comm

theorem sig_esI_eq (a : Fin r) : GBasic.sig k r (esI k r a) = eI k r a := Fin.ext (by rw [sig_esI, eI_val])

theorem sig_wI_eq (c : Fin (k + 1)) : GBasic.sig k r (wI k r c) = wI k r c := Fin.ext (by rw [sig_wI, wI_val])

theorem sgn_wI (c : Fin (k + 1)) (hc : c.val < k) : GBasic.sgn k r (wI k r c) = 1 := by
  unfold GBasic.sgn; rw [if_neg (by rw [wI_val]; omega)]

theorem UW_row {zB : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r zB) (a : Fin r) (j : Fin (2 * r + k + 1)) : h (eI k r a) j = if j = eI k r a then 1 else 0 := by
  obtain ⟨hU, hfix, -⟩ := hh
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  have e1 : h (eI k r a) j = (Hpk k r *ᵥ (h *ᵥ bvec j)) (esI k r a) := by
    rw [Hpk_mulVec, sgn_esI, sig_esI_eq, one_mul, ← mat_apply_bvec]
  have e2 : (Hpk k r *ᵥ (h *ᵥ bvec j)) (esI k r a) = (hᴴ * Hpk k r * h) (esI k r a) j := by
    rw [gram_apply']
    have hc1 : (fun t => h t (esI k r a)) = bvec (esI k r a) := by
      rw [← (hfix a).2]; ext t; rw [← mat_apply_bvec]
    have hc2 : (fun t => h t j) = h *ᵥ bvec j := by ext t; rw [← mat_apply_bvec]
    rw [hc1, hc2]
    simp [dotProduct, bvec, Pi.single_apply]
  rw [e1, e2, hU', GBasic.Hpk_eq, sig_esI_eq, sgn_esI]

theorem ellA_UW_mul {zB : Fin (2 * r + k + 1) → ℂ} {h m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r zB) (a : Fin r) : ellA k r zB (h * m) a = ellA k r zB m a := by
  have hrow : ∀ y : Fin (2 * r + k + 1) → ℂ, (h *ᵥ y) (eI k r a) = y (eI k r a) := by
    intro y
    simp only [mulVec, dotProduct, UW_row hh, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold ellA
  split
  · rw [mat_apply_bvec (h * m), ← Matrix.mulVec_mulVec, hrow, ← mat_apply_bvec]
  · rw [← Matrix.mulVec_mulVec, hrow]

theorem psiGen_UW_mul {zB : Fin (2 * r + k + 1) → ℂ} (c : Fin r → ℂ)
    {h m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r zB) :
    psiGen k r zB c (h * m) = psiGen k r zB c m := by
  unfold psiGen; simp only [ellA_UW_mul hh]

section Frame2
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem ellA_conj (hF : IsFrameJ ε e f wf z0) {zB z : Fin (2 * r + k + 1) → ℂ} (hz : Qm e f wf z0 *ᵥ zB = z)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) :
    ellA k r zB (Qi ε e f wf z0 * g * Qm e f wf z0) a = rootCoord ε e f z g a := by
  unfold ellA rootCoord nxt
  split
  · rw [conj_apply, colQ_eI, Qi_mulVec_eI]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz, Qi_mulVec_eI]

theorem psi_conj (hF : IsFrameJ ε e f wf z0) {zB z : Fin (2 * r + k + 1) → ℂ} (hz : Qm e f wf z0 *ᵥ zB = z)
    {gg : ℕ} (hg : 0 < gg) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psiGen k r zB (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) (Qi ε e f wf z0 * g * Qm e f wf z0) =
      psiR ε gg e f z g := by
  unfold psiGen psiR
  simp only [ellA_conj hF hz]
  congr 1
  set x : Fin r → ℂ := fun a => rootCoord ε e f z g a with hx
  have hre : (∑ a, ((4 * Real.pi / gg : ℝ) : ℂ) * x a).re = (4 * Real.pi / gg) * ∑ a, (x a).re := by
    rw [Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Complex.re_ofReal_mul _ _
  have hsum : ∑ a, (x a + star (x a)) = ((2 * ∑ a, (x a).re : ℝ) : ℂ) := by
    push_cast; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [Complex.star_def, Complex.add_conj]; push_cast; ring
  show Complex.I * ((∑ a, ((4 * Real.pi / gg : ℝ) : ℂ) * x a).re : ℂ) =
    2 * Real.pi * Complex.I * ((∑ a, (x a + star (x a))) / (gg : ℂ))
  rw [hre, hsum]
  have hg' : (gg : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  push_cast
  field_simp
  ring

theorem hJ_colQ_Qm (hF : IsFrameJ ε e f wf z0) (i : Fin (2 * r + k + 1)) (v : Fin (2 * r + k + 1) → ℂ) :
    hJ ε (colQ e f wf z0 i) (Qm e f wf z0 *ᵥ v) = (Hpk k r *ᵥ v) i := by
  rw [← gramQ hF, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [hJ, mulVec, dotProduct, conjTranspose_apply, Qm, Matrix.of_apply, Pi.star_apply]

variable (ε e f wf z0) in

def piB {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (πl : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    V →L[ℂ] V :=
  πl (fun a b => hJ ε (wf a) ((Qm e f wf z0 * g * Qi ε e f wf z0) *ᵥ wf b))

theorem blockW_wI (h : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    blockW k r h (wI k r ⟨a.val, by omega⟩) (wI k r ⟨b.val, by omega⟩) = h a b := by
  unfold blockW
  rw [dif_pos ⟨by rw [wI_val]; omega, by rw [wI_val]; simp only [Fin.val_mk]; have := a.isLt; omega⟩,
    dif_pos ⟨by rw [wI_val]; omega, by rw [wI_val]; simp only [Fin.val_mk]; have := b.isLt; omega⟩]
  congr 1 <;> apply Fin.ext <;> simp only [wI_val] <;> omega

theorem piB_blockW (hF : IsFrameJ ε e f wf z0) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (πl : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)) (h : Matrix (Fin k) (Fin k) ℂ) :
    piB ε e f wf z0 πl (blockW k r h) = πl h := by
  unfold piB
  congr 1
  ext a b
  have hw : ∀ c : Fin k, wf c = colQ e f wf z0 (wI k r ⟨c.val, by omega⟩) := fun c => by
    rw [colQ_wI _ _ _ _ _ (by simp only; exact c.isLt)]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw b, Qi_mulVec_col hF, hw a, hJ_colQ_Qm hF, Hpk_mulVec,
    sgn_wI _ (by simp only; exact a.isLt), sig_wI_eq, one_mul, ← mat_apply_bvec, blockW_wI]

theorem piB_conj (hF : IsFrameJ ε e f wf z0) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (πl : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    piB ε e f wf z0 πl (Qi ε e f wf z0 * h * Qm e f wf z0) = πl (fun a b => hJ ε (wf a) (h *ᵥ wf b)) := by
  unfold piB
  have : Qm e f wf z0 * (Qi ε e f wf z0 * h * Qm e f wf z0) * Qi ε e f wf z0 = h := by
    simp only [← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul]
    rw [Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.mul_one]
  rw [this]

end Frame2

def zBv (k r : ℕ) (T : ℝ) : Fin (2 * r + k + 1) → ℂ := ((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))

def z0v {n : ℕ} (T : ℝ) (z : Fin n → ℂ) : Fin n → ℂ := (((Real.sqrt T)⁻¹ : ℝ) : ℂ) • z

theorem Qm_zB {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ}
    {T : ℝ} (hT : 0 < T) (z : Fin (2 * r + k + 1) → ℂ) : Qm e f wf (z0v T z) *ᵥ zBv k r T = z := by
  unfold zBv
  rw [Matrix.mulVec_smul, Qm_mulVec_bvec, colQ_wI_last _ _ _ _ _ (by simp), z0v, smul_smul]
  have h1 : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ h1, Complex.ofReal_one, one_smul]

theorem Tz_zB {T : ℝ} (hT : 0 ≤ T) : Tz k r (zBv k r T) = T := by
  unfold Tz herm zBv
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  have h1 : star (bvec (wI k r (Fin.last k))) ⬝ᵥ (Hpk k r *ᵥ bvec (wI k r (Fin.last k))) = -1 := by
    have := GBasic.herm_bvec k r (wI k r (Fin.last k)) (wI k r (Fin.last k))
    unfold herm at this
    rw [this, Hpk_ww, if_pos rfl, if_pos (by simp)]
  rw [h1]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [show ((Real.sqrt T : ℝ) : ℂ) * (((Real.sqrt T : ℝ) : ℂ) * -1) = ((-(Real.sqrt T * Real.sqrt T) : ℝ) : ℂ) by
    push_cast; ring]
  rw [Complex.ofReal_re, Real.mul_self_sqrt hT, neg_neg]

theorem inWb_zB (T : ℝ) : inWb k r (zBv k r T) := by
  intro i hi
  simp only [zBv, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul]
  rw [if_neg (fun h => by subst h; rw [wI_val] at hi; (simp at hi) <;> omega), mul_zero]

theorem frameW_one (T : ℝ) (hT : 0 ≤ T) : IsFrameW k r (zBv k r T) 1 := by
  refine ⟨by show (1 : Matrix _ _ ℂ)ᴴ * Hpk k r * 1 = Hpk k r; simp, fun a => ⟨by simp, by simp⟩, ?_⟩
  rw [Matrix.one_mulVec, Tz_zB hT]; rfl

theorem hcTypeW_piB {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0)
    {T : ℝ} (hT : 0 ≤ T) {u : Fin k → ℝ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {πl : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)} (hπ : IsHCTypeU k u πl) :
    IsHCTypeW k r (zBv k r T) u (piB ε e f wf z0 πl) := by
  refine ⟨1, frameW_one T hT, ?_⟩
  have : (fun h => piB ε e f wf z0 πl (1 * blockW k r h * (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹))
      = πl := by
    funext h; rw [inv_one, Matrix.mul_one, Matrix.one_mul, piB_blockW hF]
  rw [this]; exact hπ

section Meas
variable {ε : Fin (2 * r + k + 1) → Bool}

def toUJ (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε,
    (mul_eq_one_comm_of_card_eq (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ rfl).mp (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]⟩, hM⟩

theorem uMat_toUJ (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) : uMat (toUJ M hM) = M := rfl

theorem uMat_mem (g : Formalism.REAL.UJ ε) : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2

theorem uMat_mul (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem uMat_one : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

def cM (A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (g : Formalism.REAL.UJ ε) : Mt k r :=
  (A * uMat g * B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)

theorem cM_closedEmb {A B A' B' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hA : A' * A = 1) (hB : B * B' = 1) : Topology.IsClosedEmbedding (cM (ε := ε) A B) := by
  have hA2 : A * A' = 1 := (mul_eq_one_comm_of_card_eq (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ rfl).mp hA
  have hB2 : B' * B = 1 := (mul_eq_one_comm_of_card_eq (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ rfl).mp hB
  let L : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ ≃ₜ Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    { toFun := fun M => A * M * B
      invFun := fun M => A' * M * B'
      left_inv := fun M => by
        simp only [← Matrix.mul_assoc, hA, Matrix.one_mul]; rw [Matrix.mul_assoc, hB, Matrix.mul_one]
      right_inv := fun M => by
        simp only [← Matrix.mul_assoc, hA2, Matrix.one_mul]; rw [Matrix.mul_assoc, hB2, Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact L.isClosedEmbedding.comp ((Formalism.REAL.isClosedEmbeddingMatrix _ ε).1)

theorem cM_measEmb {A B A' B' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hA : A' * A = 1) (hB : B * B' = 1) : MeasurableEmbedding (cM (ε := ε) A B) :=
  (cM_closedEmb hA hB).measurableEmbedding

theorem lmulM_cM (s A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (g : Formalism.REAL.UJ ε) :
    lmulM s (cM A B g) = cM (s * A) B g := by
  unfold lmulM cM
  show s * (A * uMat g * B) = s * A * uMat g * B
  simp only [Matrix.mul_assoc]

end Meas

section Meas2
variable {ε : Fin (2 * r + k + 1) → Bool}

theorem muG_ne_zero : Formalism.REAL.muG ε ≠ 0 := fun h => by
  have := isOpen_univ.measure_pos (Formalism.REAL.muG ε) Set.univ_nonempty
  rw [h] at this; simp at this

theorem measurable_lmulM (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (lmulM (k := k) (r := r) s) := by
  exact Continuous.measurable (by unfold lmulM; exact continuous_const.matrix_mul continuous_id)

structure CayPair (ε : Fin (2 * r + k + 1) → Bool) (P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Prop where
  cay : P0ᴴ * Formalism.REAL.Jm ε * P0 = Hpk k r
  B_zero_shape_eq_index : B0 = Hpk k r * P0ᴴ * Formalism.REAL.Jm ε

theorem CayPair.BP {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (h : CayPair ε P0 B0) :
    B0 * P0 = 1 := cay_BA h.cay (GBasic.Hpk_sq k r) h.B_zero_shape_eq_index
theorem CayPair.PB {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (h : CayPair ε P0 B0) :
    P0 * B0 = 1 := cay_AB h.cay (GBasic.Hpk_sq k r) h.B_zero_shape_eq_index
theorem CayPair.BHB {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (h : CayPair ε P0 B0) :
    B0ᴴ * Hpk k r * B0 = Formalism.REAL.Jm ε :=
  cay_BHB h.cay (GBasic.Hpk_sq k r) (Formalism.REAL.Jm_mul_self ε) (Formalism.REAL.Jm_conjTranspose ε) (GBasic.Hpk_herm k r) h.B_zero_shape_eq_index

theorem isHaarOn_G {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : CayPair ε P0 B0) :
    IsHaarOn (UH (Hpk k r)) ((Formalism.REAL.muG ε).map (cM B0 P0)) := by
  have emb := cM_measEmb (ε := ε) (A := B0) (B := P0) (A' := P0) (B' := B0) hP.PB hP.PB
  refine ⟨emb.sigmaFinite_map, (Measure.map_ne_zero_iff emb.measurable.aemeasurable).mpr muG_ne_zero, ?_, ?_⟩
  · rw [emb.map_apply]
    convert measure_empty (μ := Formalism.REAL.muG ε)
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact cay_conj hP.cay hP.BHB (uMat_mem g)
  · intro s hs
    have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
    have ht : (P0 * s * B0)ᴴ * Formalism.REAL.Jm ε * (P0 * s * B0) = Formalism.REAL.Jm ε := by
      simp only [conjTranspose_mul]
      calc _ = B0ᴴ * (sᴴ * (P0ᴴ * Formalism.REAL.Jm ε * P0) * s) * B0 := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε := by rw [hP.cay, hs', hP.BHB]
    set t := toUJ (P0 * s * B0) ht
    rw [Measure.map_map (measurable_lmulM s) emb.measurable]
    have hfun : lmulM s ∘ cM B0 P0 = cM B0 P0 ∘ (fun g : Formalism.REAL.UJ ε => t * g) := by
      funext g
      simp only [Function.comp, lmulM_cM]
      unfold cM
      rw [uMat_mul, uMat_toUJ]
      simp only [← Matrix.mul_assoc, hP.BP, Matrix.one_mul]
      try rfl
    rw [hfun, ← Measure.map_map emb.measurable (measurable_const_mul t), map_mul_left_eq_self]

end Meas2

section Meas3
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

variable (ε e f wf z0) in

def HNset (zB : Fin (2 * r + k + 1) → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {s | Qi ε e f wf z0 * uMat s * Qm e f wf z0 ∈ Sset k r zB}

def IsLocHaar (S : Set (Formalism.REAL.UJ ε)) (μ : Measure (Formalism.REAL.UJ ε)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ

def IsLocQuot (μS ν : Measure (Formalism.REAL.UJ ε)) : Prop :=
  ∀ F : Formalism.REAL.UJ ε → ENNReal, Measurable F →
    ∫⁻ x, F x ∂(Formalism.REAL.muG ε) = ∫⁻ x, (∫⁻ s, F (s * x) ∂μS) ∂ν

theorem mem_UH_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r))
    (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  simp only [conjTranspose_mul]
  calc _ = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem Sset_sub_UH {zB : Fin (2 * r + k + 1) → ℂ} {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ Sset k r zB) : s ∈ UH (Hpk k r) := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact mem_UH_mul hh.1 hm.1

theorem conjQ_UJ (hF : IsFrameJ ε e f wf z0) {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) :
    (Qm e f wf z0 * s * Qi ε e f wf z0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * s * Qi ε e f wf z0) = Formalism.REAL.Jm ε := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  simp only [conjTranspose_mul]
  calc _ = (Qi ε e f wf z0)ᴴ * (sᴴ * ((Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * Qm e f wf z0) * s) * Qi ε e f wf z0 := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [gramQ hF, hs', QiHQi hF]

theorem Qi_Qm_conj (hF : IsFrameJ ε e f wf z0) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Qi ε e f wf z0 * (Qm e f wf z0 * s * Qi ε e f wf z0) * Qm e f wf z0 = s := by
  simp only [← Matrix.mul_assoc, Qi_mul_Qm hF, Matrix.one_mul]
  rw [Matrix.mul_assoc, Qi_mul_Qm hF, Matrix.mul_one]

theorem isHaarOn_S (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} {μS : Measure (Formalism.REAL.UJ ε)}
    (hS : IsLocHaar (HNset ε e f wf z0 zB) μS) :
    IsHaarOn (Sset k r zB) (μS.map (cM (Qi ε e f wf z0) (Qm e f wf z0))) := by
  have emb := cM_measEmb (ε := ε) (A := Qi ε e f wf z0) (B := Qm e f wf z0) (A' := Qm e f wf z0)
    (B' := Qi ε e f wf z0) (Qm_mul_Qi hF) (Qm_mul_Qi hF)
  obtain ⟨hsf, hne, hcon, hinv⟩ := hS
  haveI := hsf
  refine ⟨emb.sigmaFinite_map, (Measure.map_ne_zero_iff emb.measurable.aemeasurable).mpr hne, ?_, ?_⟩
  · rw [emb.map_apply]
    exact (congrArg μS (Set.ext fun g => Iff.rfl)).trans hcon
  · intro s hs
    have ht := conjQ_UJ hF (Sset_sub_UH hs)
    set t := toUJ (Qm e f wf z0 * s * Qi ε e f wf z0) ht
    have htS : t ∈ HNset ε e f wf z0 zB := by
      show Qi ε e f wf z0 * uMat t * Qm e f wf z0 ∈ Sset k r zB
      rw [uMat_toUJ, Qi_Qm_conj hF]; exact hs
    rw [Measure.map_map (measurable_lmulM s) emb.measurable]
    have hfun : lmulM s ∘ cM (Qi ε e f wf z0) (Qm e f wf z0) =
        cM (Qi ε e f wf z0) (Qm e f wf z0) ∘ (fun g : Formalism.REAL.UJ ε => t * g) := by
      funext g
      simp only [Function.comp, lmulM_cM]
      unfold cM
      rw [uMat_mul, uMat_toUJ]
      simp only [← Matrix.mul_assoc, Qi_mul_Qm hF, Matrix.one_mul]
      try rfl
    rw [hfun, ← Measure.map_map emb.measurable (measurable_const_mul t), hinv t htS]

theorem cM_comp_mul (hF : IsFrameJ ε e f wf z0) (P0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (s x : Formalism.REAL.UJ ε) :
    (fun i j => (Matrix.of (cM (Qi ε e f wf z0) (Qm e f wf z0) s) * Matrix.of (cM (Qi ε e f wf z0) P0 x)) i j) =
      cM (Qi ε e f wf z0) P0 (s * x) := by
  have h : (Qi ε e f wf z0 * uMat s * Qm e f wf z0) * (Qi ε e f wf z0 * uMat x * P0) =
      Qi ε e f wf z0 * uMat (s * x) * P0 := by
    rw [uMat_mul]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (Qi ε e f wf z0 * uMat s), Qm_mul_Qi hF, Matrix.mul_one]
  funext i j
  exact congrFun (congrFun h i) j

theorem cM_left (hF : IsFrameJ ε e f wf z0) {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ht : (Qm e f wf z0 * B0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * B0) = Formalism.REAL.Jm ε) (g : Formalism.REAL.UJ ε) :
    cM (Qi ε e f wf z0) P0 (toUJ (Qm e f wf z0 * B0) ht * g) = cM B0 P0 g := by
  have h : Qi ε e f wf z0 * uMat (toUJ (Qm e f wf z0 * B0) ht * g) * P0 = B0 * uMat g * P0 := by
    rw [uMat_mul, uMat_toUJ]
    simp only [← Matrix.mul_assoc, Qi_mul_Qm hF, Matrix.one_mul]
  exact h

theorem isQuotMeas_B (hF : IsFrameJ ε e f wf z0) {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : CayPair ε P0 B0) {μS ν : Measure (Formalism.REAL.UJ ε)} (hQ : IsLocQuot μS ν) :
    IsQuotMeas ((Formalism.REAL.muG ε).map (cM B0 P0)) (μS.map (cM (Qi ε e f wf z0) (Qm e f wf z0)))
      (ν.map (cM (Qi ε e f wf z0) P0)) := by
  have embG := cM_measEmb (ε := ε) (A := B0) (B := P0) (A' := P0) (B' := B0) hP.PB hP.PB
  have embS := cM_measEmb (ε := ε) (A := Qi ε e f wf z0) (B := Qm e f wf z0) (A' := Qm e f wf z0)
    (B' := Qi ε e f wf z0) (Qm_mul_Qi hF) (Qm_mul_Qi hF)
  have embX := cM_measEmb (ε := ε) (A := Qi ε e f wf z0) (B := P0) (A' := Qm e f wf z0) (B' := B0)
    (Qm_mul_Qi hF) hP.PB
  intro F hFm
  rw [embG.lintegral_map, embX.lintegral_map]
  simp only [embS.lintegral_map, cM_comp_mul hF]
  have ht : (Qm e f wf z0 * B0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * B0) = Formalism.REAL.Jm ε := by
    simp only [conjTranspose_mul]
    calc _ = B0ᴴ * ((Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * Qm e f wf z0) * B0 := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [gramQ hF, hP.BHB]
  have h1 := hQ (fun y => F (cM (Qi ε e f wf z0) P0 y)) (hFm.comp embX.measurable)
  rw [← h1]
  calc ∫⁻ g, F (cM B0 P0 g) ∂(Formalism.REAL.muG ε)
      = ∫⁻ g, F (cM (Qi ε e f wf z0) P0 (toUJ (Qm e f wf z0 * B0) ht * g)) ∂(Formalism.REAL.muG ε) := by
        simp only [cM_left hF ht]
    _ = ∫⁻ y, F (cM (Qi ε e f wf z0) P0 y) ∂(Formalism.REAL.muG ε) :=
        lintegral_mul_left_eq_self (fun y => F (cM (Qi ε e f wf z0) P0 y)) _

end Meas3

section Loc
open Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay

variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem cX_mem_UH (hF : IsFrameJ ε e f wf z0) {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : CayPair ε P0 B0) (x : Formalism.REAL.UJ ε) :
    (Qi ε e f wf z0 * uMat x * P0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  show (Qi ε e f wf z0 * uMat x * P0)ᴴ * Hpk k r * (Qi ε e f wf z0 * uMat x * P0) = Hpk k r
  simp only [conjTranspose_mul]
  calc _ = P0ᴴ * ((uMat x)ᴴ * ((Qi ε e f wf z0)ᴴ * Hpk k r * Qi ε e f wf z0) * uMat x) * P0 := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [QiHQi hF, uMat_mem, hP.cay]

theorem one_mem_Sset (zB : Fin (2 * r + k + 1) → ℂ) : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Sset k r zB := by
  refine ⟨1, ⟨?_, fun a => ⟨by simp, by simp⟩, by simp⟩, 1, ⟨?_, ?_, ?_⟩, by simp⟩
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r; simp
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r; simp
  · intro a i _; simp [Matrix.one_apply, eq_comm]
  · intro i j _ _ _; simp [Matrix.one_apply, eq_comm]

def nuLoc (zB : Fin (2 * r + k + 1) → ℂ) (x : Formalism.REAL.UJ ε) : ℝ :=
  ⨅ t : HNset ε e f wf z0 zB, opn (uMat ((t : Formalism.REAL.UJ ε) * x))

theorem opn_ABC (A M B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    opn (A * M * B) ≤ (opn A * opn B) * opn M := by
  calc opn (A * M * B) ≤ opn (A * M) * opn B := Formalism.L2.SG.WuDecayPf.opn_mul_le _ _
    _ ≤ (opn A * opn M) * opn B :=
        mul_le_mul_of_nonneg_right (Formalism.L2.SG.WuDecayPf.opn_mul_le _ _) (Formalism.L2.SG.WuDecayPf.opn_nonneg _)
    _ = (opn A * opn B) * opn M := by ring

theorem nuLoc_le_one (zB : Fin (2 * r + k + 1) → ℂ) (t : Formalism.REAL.UJ ε) (ht : t ∈ HNset ε e f wf z0 zB)
    (x : Formalism.REAL.UJ ε) : nuLoc (e := e) (f := f) (wf := wf) (z0 := z0) zB x ≤ opn (uMat (t * x)) := by
  unfold nuLoc
  exact ciInf_le (f := fun t : HNset ε e f wf z0 zB => opn (uMat ((t : Formalism.REAL.UJ ε) * x)))
    ⟨0, by rintro _ ⟨i, rfl⟩; exact Formalism.L2.SG.WuDecayPf.opn_nonneg _⟩ ⟨t, ht⟩

theorem nuLoc_le (hF : IsFrameJ ε e f wf z0) {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : CayPair ε P0 B0) (zB : Fin (2 * r + k + 1) → ℂ) (x : Formalism.REAL.UJ ε) :
    nuLoc (e := e) (f := f) (wf := wf) (z0 := z0) zB x ≤
      (opn (Qm e f wf z0) * opn B0) * nuH k r zB (Qi ε e f wf z0 * uMat x * P0) := by
  have hc : 0 ≤ opn (Qm e f wf z0) * opn B0 :=
    mul_nonneg (Formalism.L2.SG.WuDecayPf.opn_nonneg _) (Formalism.L2.SG.WuDecayPf.opn_nonneg _)
  unfold nuH
  rw [Real.mul_iInf_of_nonneg hc]
  haveI : Nonempty (Sset k r zB) := ⟨⟨1, one_mem_Sset zB⟩⟩
  refine le_ciInf fun tB => ?_
  obtain ⟨M, hM⟩ := tB
  have ht : (Qm e f wf z0 * M * Qi ε e f wf z0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * M * Qi ε e f wf z0) =
      Formalism.REAL.Jm ε := conjQ_UJ hF (Sset_sub_UH hM)
  have htS : toUJ (Qm e f wf z0 * M * Qi ε e f wf z0) ht ∈ HNset ε e f wf z0 zB := by
    show Qi ε e f wf z0 * uMat (toUJ (Qm e f wf z0 * M * Qi ε e f wf z0) ht) * Qm e f wf z0 ∈ Sset k r zB
    rw [uMat_toUJ, Qi_Qm_conj hF]; exact hM
  have h1 := nuLoc_le_one zB _ htS x
  have heq : uMat (toUJ (Qm e f wf z0 * M * Qi ε e f wf z0) ht * x) =
      Qm e f wf z0 * (M * (Qi ε e f wf z0 * uMat x * P0)) * B0 := by
    rw [uMat_mul, uMat_toUJ]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc _ P0 B0, hP.PB, Matrix.mul_one]
  rw [heq] at h1
  exact h1.trans (opn_ABC _ _ _)

end Loc

section Pack
open Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay

variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem fdegH_map {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : CayPair ε P0 B0) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) :
    fdegH ((Formalism.REAL.muG ε).map (cM B0 P0)) (fun M => σ (P0 * M * B0)) w = fdegOf (Formalism.REAL.muG ε) σ w := by
  have embG := cM_measEmb (ε := ε) (A := B0) (B := P0) (A' := P0) (B' := B0) hP.PB hP.PB
  unfold fdegH fdegOf coefOn
  rw [embG.integral_map]
  congr 2; funext g
  have : P0 * (B0 * uMat g * P0) * B0 = uMat g := by
    simp only [← Matrix.mul_assoc, hP.PB, Matrix.one_mul]
    rw [Matrix.mul_assoc, hP.PB, Matrix.mul_one]
  exact congrArg (fun M => ‖⟪w, σ M w⟫_ℂ‖ ^ 2) this

theorem cMprod {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : CayPair ε P0 B0)
    (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x g : Formalism.REAL.UJ ε) :
    @HMul.hMul (Mat k r) (Mat k r) (Mat k r) _ (cM A P0 x) (Matrix.of (cM B0 P0 g)) = Matrix.of (cM A P0 (x * g)) := by
  show (A * uMat x * P0) * (B0 * uMat g * P0) = A * uMat (x * g) * P0
  rw [uMat_mul]; simp only [← Matrix.mul_assoc]; rw [Matrix.mul_assoc _ P0 B0, hP.PB, Matrix.mul_one]

theorem locPack (hB : BesselNVGap) (hCW : CoefWeightedLoc) (hWl : WlocExists) (hε : ε = eps48 k r)
    (hk : 1 ≤ k) (hke : Even k) {T : ℝ} (hT : 0 < T) {gg : ℕ} (hg : 0 < gg)
    {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (hu : Formalism.QuantumDeterminants.IsHCParam u)
    (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) (hI : InterlacingCondition k r u v b) (hH : HalfIntegralDifference k r u v b)
    (hGap : GapBig k r b) {z : Fin (2 * r + k + 1) → ℂ} (hz0 : z0 = z0v T z) (hF : IsFrameJ ε e f wf z0)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hDS : IsDS ε (lam48 k r v b) σ)
    {w : H} (hw : IsLowUnit ε (lam48 k r v b) σ w)
    {Vl : Type} [NormedAddCommGroup Vl] [InnerProductSpace ℂ Vl] [FiniteDimensional ℂ Vl]
    {πl : Matrix (Fin k) (Fin k) ℂ → (Vl →L[ℂ] Vl)} (hπ : IsHCTypeU k u πl)
    {μS ν : Measure (Formalism.REAL.UJ ε)} (hS : IsLocHaar (HNset ε e f wf z0 (zBv k r T)) μS) (hQ : IsLocQuot μS ν) :
    ∃ W : Formalism.REAL.UJ ε → Vl, Continuous W ∧
      (∀ s x : Formalism.REAL.UJ ε, ∀ h ∈ UWset k r (zBv k r T), ∀ m ∈ Nset k r,
        Qi ε e f wf z0 * uMat s * Qm e f wf z0 = h * m →
        W (s * x) = psiR ε gg e f z (uMat s) • piB ε e f wf z0 πl h (W x)) ∧
      (∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
          W (x * g)) (Formalism.REAL.muG ε) ∧
        ∫ g, (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
          ∂(Formalism.REAL.muG ε) = W x) ∧
      ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤ ∧ ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν = 1 ∧
      ∫⁻ x, ‖W x‖ₑ * ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0) (zBv k r T) x ^ N1H k r) ∂ν < ⊤ ∧
      ∃ (α : Formalism.REAL.UJ ε → ℂ) (Ω : Set (Formalism.REAL.UJ ε)) (a : ℝ), IsCompact Ω ∧ 1 ∈ Ω ∧
        Measurable α ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
        ∀ x, Integrable (fun g => α g • W (x * g)) (Formalism.REAL.muG ε) ∧
          ∫ g, α g • W (x * g) ∂(Formalism.REAL.muG ε) = W x := by
  obtain ⟨P0, hP0⟩ := Formalism.MainNotions.S.Inh.exists_isCayleyU_eps48 k r hk
  have hCP : CayPair ε P0 (Hpk k r * P0ᴴ * Formalism.REAL.Jm ε) := ⟨hε ▸ hP0.1.2, rfl⟩
  generalize hB0 : Hpk k r * P0ᴴ * Formalism.REAL.Jm ε = B0 at hCP
  have hinv : P0⁻¹ = B0 := Matrix.inv_eq_left_inv hCP.BP
  have hσB1 : (fun g => (fun M => σ (P0 * M * B0)) (P0⁻¹ * g * P0)) = σ := by
    funext g
    simp only [hinv]
    congr 1
    simp only [← Matrix.mul_assoc, hCP.PB, Matrix.one_mul]
    rw [Matrix.mul_assoc, hCP.PB, Matrix.mul_one]
  have hP0' : IsCayleyU k r ε P0 := hε ▸ hP0
  have hDSB : IsDSHpk k r (eps48 k r) (lam48 k r v b) (fun M => σ (P0 * M * B0)) :=
    hε ▸ ⟨P0, hP0', by rw [hσB1]; exact hDS⟩
  have hwB : IsLowUnitH k r (eps48 k r) (lam48 k r v b) (fun M => σ (P0 * M * B0)) w :=
    hε ▸ ⟨P0, hP0', by rw [hσB1]; exact hw⟩
  have hS48 : RealPlaceNumericalSetting k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) u v b := by
    refine ⟨hk, hke, inWb_zB T, by rw [Tz_zB hT.le]; exact hT, fun _ => ?_, hu, hl, hI, hH, hGap⟩
    have : (0 : ℝ) < 4 * Real.pi / gg := by positivity
    show ((4 * Real.pi / gg : ℝ) : ℂ) ≠ 0
    exact_mod_cast this.ne'
  have hπB := hcTypeW_piB hF hT.le hπ
  have hG := isHaarOn_G hCP
  have hSB := isHaarOn_S hF hS
  have hQB := isQuotMeas_B hF hCP hQ
  obtain ⟨WB, hcont, hequiv, hrep, hL1, hL2, hwt, α, Ω, a, hΩc, h1Ω, hΩU, hαm, hαs, hαb, hαr⟩ :=
    hWl hB hCW k r (zBv k r T) _ u v b hS48 H _ hDSB Vl (piB ε e f wf z0 πl) hπB w hwB _ _ _ hG hSB hQB
  have embG := cM_measEmb (ε := ε) (A := B0) (B := P0) (A' := P0) (B' := B0) hCP.PB hCP.PB
  have embX := cM_measEmb (ε := ε) (A := Qi ε e f wf z0) (B := P0) (A' := Qm e f wf z0) (B' := B0)
    (Qm_mul_Qi hF) hCP.PB
  have hXU : ∀ x, Matrix.of (cM (Qi ε e f wf z0) P0 x) ∈ UH (Hpk k r) := cX_mem_UH hF hCP
  have hfd : fdegH ((Formalism.REAL.muG ε).map (cM B0 P0)) (fun M => σ (P0 * M * B0)) w = fdegOf (Formalism.REAL.muG ε) σ w :=
    fdegH_map hCP σ w
  have hσg : ∀ g : Formalism.REAL.UJ ε, σ (P0 * (Matrix.of (cM B0 P0 g) : Mat k r) * B0) = σ (uMat g) := by
    intro g
    show σ (P0 * (B0 * uMat g * P0) * B0) = σ (uMat g)
    congr 1; simp only [← Matrix.mul_assoc, hCP.PB, Matrix.one_mul]; rw [Matrix.mul_assoc, hCP.PB, Matrix.mul_one]
  refine ⟨fun x => WB (cM (Qi ε e f wf z0) P0 x), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcont.comp_continuous (cM_closedEmb (Qm_mul_Qi hF) hCP.PB).continuous hXU
  · intro s x h hh m hm hsm
    have h1 : Matrix.of (cM (Qi ε e f wf z0) P0 (s * x)) = h * m * Matrix.of (cM (Qi ε e f wf z0) P0 x) := by
      rw [← hsm]
      show Qi ε e f wf z0 * uMat (s * x) * P0 = Qi ε e f wf z0 * uMat s * Qm e f wf z0 * (Qi ε e f wf z0 * uMat x * P0)
      rw [uMat_mul]; simp only [← Matrix.mul_assoc]; rw [Matrix.mul_assoc _ (Qm e f wf z0), Qm_mul_Qi hF, Matrix.mul_one]
    have hz : Qm e f wf z0 *ᵥ zBv k r T = z := hz0 ▸ Qm_zB hT z
    show WB (Matrix.of (cM (Qi ε e f wf z0) P0 (s * x))) = _
    rw [h1, hequiv h hh m hm _ (hXU x), ← psiGen_UW_mul _ hh, ← hsm, psi_conj hF hz hg]
    rfl
  · intro x
    obtain ⟨hint, hval⟩ := hrep _ (hXU x)
    have hint2 := embG.integrable_map_iff.mp hint
    have hpt : ∀ g : Formalism.REAL.UJ ε, ((fun g' : Mt k r => eFun ((Formalism.REAL.muG ε).map (cM B0 P0))
        (fun M => σ (P0 * M * B0)) w (Matrix.of g') •
        WB (@HMul.hMul (Mat k r) (Mat k r) (Mat k r) _ (cM (Qi ε e f wf z0) P0 x) (Matrix.of g'))) ∘ cM B0 P0) g =
        (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
          WB (cM (Qi ε e f wf z0) P0 (x * g)) := by
      intro g
      simp only [Function.comp_apply, eFun]
      rw [hfd, hσg, cMprod hCP]
      rfl
    refine ⟨hint2.congr (ae_of_all _ hpt), ?_⟩
    rw [← integral_congr_ae (ae_of_all _ hpt)]
    exact (embG.integral_map _).symm.trans hval
  · refine lt_of_eq_of_lt ?_ hL1
    exact (embX.lintegral_map (μ := ν) (fun y : Mt k r => ‖WB (Matrix.of y)‖ₑ)).symm
  · refine Eq.trans ?_ hL2
    unfold l2SG
    rw [embX.lintegral_map]
    simp only [enorm_eq_nnnorm]
    rfl
  · have hc : 0 ≤ opn (Qm e f wf z0) * opn B0 :=
      mul_nonneg (Formalism.L2.SG.WuDecayPf.opn_nonneg _) (Formalism.L2.SG.WuDecayPf.opn_nonneg _)
    have hN : 0 ≤ N1H k r := by unfold N1H; positivity
    have hpt : ∀ x : Formalism.REAL.UJ ε, ‖WB (cM (Qi ε e f wf z0) P0 x)‖ₑ *
        ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0) (zBv k r T) x ^ N1H k r) ≤
        ENNReal.ofReal ((opn (Qm e f wf z0) * opn B0) ^ N1H k r) * (‖WB (cM (Qi ε e f wf z0) P0 x)‖ₑ *
          ENNReal.ofReal (nuH k r (zBv k r T) (cM (Qi ε e f wf z0) P0 x) ^ N1H k r)) := by
      intro x
      have h0 : 0 ≤ nuLoc (e := e) (f := f) (wf := wf) (z0 := z0) (zBv k r T) x :=
        Real.iInf_nonneg fun _ => Formalism.L2.SG.WuDecayPf.opn_nonneg _
      have h0' : 0 ≤ nuH k r (zBv k r T) (cM (Qi ε e f wf z0) P0 x) :=
        Real.iInf_nonneg fun _ => Formalism.L2.SG.WuDecayPf.opn_nonneg _
      have hle := nuLoc_le hF hCP (zBv k r T) x
      rw [mul_left_comm]
      refine mul_le_mul' le_rfl ?_
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc _), ← Real.mul_rpow hc h0']
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h0 hle hN)
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_eq_of_lt ?_ hwt)
    exact (embX.lintegral_map (μ := ν) (fun y : Mt k r =>
      ‖WB (Matrix.of y)‖ₑ * ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of y) ^ N1H k r))).symm
  · refine ⟨fun g => α (cM B0 P0 g), cM B0 P0 ⁻¹' Ω, a, (cM_closedEmb hCP.PB hCP.PB).isCompact_preimage hΩc, ?_,
      hαm.comp embG.measurable, fun y hy => hαs _ hy, fun y => hαb _, ?_⟩
    · show Matrix.of (cM B0 P0 (1 : Formalism.REAL.UJ ε)) ∈ Ω
      have : Matrix.of (cM B0 P0 (1 : Formalism.REAL.UJ ε)) = (1 : Mat k r) := by
        show B0 * uMat 1 * P0 = 1; rw [uMat_one, Matrix.mul_one, hCP.BP]
      rw [this]; exact h1Ω
    · intro x
      obtain ⟨hint, hval⟩ := hαr _ (hXU x)
      have hint2 := embG.integrable_map_iff.mp hint
      have hpt : ∀ g : Formalism.REAL.UJ ε, ((fun g' : Mt k r => α (Matrix.of g') •
          WB (@HMul.hMul (Mat k r) (Mat k r) (Mat k r) _ (cM (Qi ε e f wf z0) P0 x) (Matrix.of g'))) ∘ cM B0 P0) g =
          α (cM B0 P0 g) • WB (cM (Qi ε e f wf z0) P0 (x * g)) := by
        intro g
        simp only [Function.comp_apply]
        rw [cMprod hCP]
        rfl
      refine ⟨hint2.congr (ae_of_all _ hpt), ?_⟩
      rw [← integral_congr_ae (ae_of_all _ hpt)]
      exact (embG.integral_map _).symm.trans hval

end Pack

section Steps

def BesselLevi : Prop :=
  ∀ (k r : ℕ) (T : ℝ), 0 < T → ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
    s ∈ UH (Hpk k r) →
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0) →
    (∀ i : Fin (2 * r + k + 1), r ≤ i.val →
      (s *ᵥ (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))) i =
        (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) i) →
    s ∈ Sset k r (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))

def BesselSGroup : Prop :=
  ∀ (k r : ℕ) (T : ℝ), 0 < T →
    (∀ s ∈ Sset k r (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))),
      ∀ t ∈ Sset k r (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))),
        s * t ∈ Sset k r (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))) ∧
    ∀ s ∈ Sset k r (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))),
      Hpk k r * sᴴ * Hpk k r ∈ Sset k r (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))

def TensInt : Prop :=
  ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ v, MeasurableSpace (X v)] (μ : ∀ v, Measure (X v))
    [∀ v, SigmaFinite (μ v)] (V : ι → Type) [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
    [∀ v, FiniteDimensional ℂ (V v)] (Vπ : Type) [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ]
    [FiniteDimensional ℂ Vπ] (tens : (∀ v, V v) → Vπ),
    (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ →
    ∀ G : ∀ v, X v → V v, (∀ v, Integrable (G v) (μ v)) →
      Integrable (fun y : ∀ v, X v => tens (fun v => G v (y v))) (Measure.pi μ) ∧
        ∫ y, tens (fun v => G v (y v)) ∂(Measure.pi μ) = tens (fun v => ∫ t, G v t ∂(μ v))

def QuotProdK : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ι → ℕ) (ε : ∀ v, Fin (n v) → Bool)
    (N H : ∀ v, Set (Formalism.REAL.UJ (ε v))),
    (∀ v, IsClosed (N v)) → (∀ v, IsCompact (H v)) →
    (∀ v, (1 : Formalism.REAL.UJ (ε v)) ∈ N v ∧ (∀ a ∈ N v, ∀ b ∈ N v, a * b ∈ N v) ∧ ∀ a ∈ N v, a⁻¹ ∈ N v) →
    (∀ v, (1 : Formalism.REAL.UJ (ε v)) ∈ H v ∧ (∀ a ∈ H v, ∀ b ∈ H v, a * b ∈ H v) ∧ ∀ a ∈ H v, a⁻¹ ∈ H v) →
    (∀ v, ∀ h ∈ H v, ∀ m ∈ N v, h * m * h⁻¹ ∈ N v) →
    (∀ v (μ : Measure (Formalism.REAL.UJ (ε v))), SigmaFinite μ → μ ≠ 0 → μ (N v)ᶜ = 0 →
      (∀ s ∈ N v, μ.map (fun x => s * x) = μ) → ∀ s ∈ N v, μ.map (fun x => x * s) = μ) →
    ∀ muN muH nuQ : Measure (∀ v, Formalism.REAL.UJ (ε v)),
      (SigmaFinite muN ∧ muN ≠ 0 ∧ muN (Set.pi Set.univ N)ᶜ = 0 ∧
        ∀ s ∈ Set.pi Set.univ N, muN.map (fun x => s * x) = muN) →
      (SigmaFinite muH ∧ muH ≠ 0 ∧ muH (Set.pi Set.univ H)ᶜ = 0 ∧
        ∀ s ∈ Set.pi Set.univ H, muH.map (fun x => s * x) = muH) →
      (∀ f : (∀ v, Formalism.REAL.UJ (ε v)) → ENNReal, Measurable f →
        ∫⁻ x, f x ∂(Measure.pi fun v => Formalism.REAL.muG (ε v)) =
          ∫⁻ x, (∫⁻ s, f (s * x) ∂((muN.prod muH).map (fun p => p.1 * p.2))) ∂nuQ) →
      ∃ (μS νl : ∀ v, Measure (Formalism.REAL.UJ (ε v))) (C : ENNReal), C ≠ 0 ∧ C ≠ ⊤ ∧
        (∀ v, (SigmaFinite (μS v) ∧ μS v ≠ 0 ∧ μS v {s | ∃ m ∈ N v, ∃ h ∈ H v, s = m * h}ᶜ = 0 ∧
          ∀ s ∈ {s | ∃ m ∈ N v, ∃ h ∈ H v, s = m * h}, (μS v).map (fun x => s * x) = μS v) ∧
          ∀ F : Formalism.REAL.UJ (ε v) → ENNReal, Measurable F →
            ∫⁻ x, F x ∂(Formalism.REAL.muG (ε v)) = ∫⁻ x, (∫⁻ s, F (s * x) ∂(μS v)) ∂(νl v)) ∧
        ∀ F : ∀ v, Formalism.REAL.UJ (ε v) → ENNReal, (∀ v, Measurable (F v)) →
          (∀ v, ∀ m ∈ N v, ∀ h ∈ H v, ∀ x, F v (m * h * x) = F v x) →
          ∫⁻ x, ∏ v, F v (x v) ∂nuQ = C * ∏ v, ∫⁻ y, F v y ∂(νl v)

end Steps

end Formalism.L2.SG.Pf.WFL
