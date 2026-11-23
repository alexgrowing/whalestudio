import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NfMid

variable {k r : ℕ}

theorem herm_bvec_right (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec i) = GBasic.sgn k r i * v (GBasic.sig k r i) := by
  simp [herm, bvec, dotProduct, mulVec, Pi.single_apply, GBasic.Hpk_eq]

theorem herm_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  have ha := a.isLt
  have h1 : GBasic.sig k r (eI k r a) = esI k r a := Fin.ext (GBasic.sig_lo k r _ ha)
  have h2 : GBasic.sgn k r (eI k r a) = 1 := if_neg (by simp only [eI]; omega)
  rw [herm_bvec_right, h1, h2, one_mul]

theorem herm_es (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  have ha := a.isLt
  have h1 : GBasic.sig k r (esI k r a) = eI k r a := by
    apply Fin.ext
    rw [GBasic.sig_hi k r _ (by simp only [esI]; omega)]
    simp only [esI, eI]; omega
  have h2 : GBasic.sgn k r (esI k r a) = 1 := if_neg (by simp only [esI]; omega)
  rw [herm_bvec_right, h1, h2, one_mul]

theorem herm_star (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  rw [← star_dotProduct, star_mulVec, GBasic.Hpk_herm, dotProduct_mulVec]

theorem herm_smul_right (v w : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    herm (Hpk k r) v (c • w) = star c * herm (Hpk k r) v w := by
  simp [herm, star_smul]

theorem herm_smul_left (v w : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    herm (Hpk k r) (c • v) w = c * herm (Hpk k r) v w := by
  simp [herm, mulVec_smul]

theorem herm_add_right (v w u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (w + u) = herm (Hpk k r) v w + herm (Hpk k r) v u := by
  simp [herm, star_add]

theorem herm_add_left (v w u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (w + u) v = herm (Hpk k r) w v + herm (Hpk k r) u v := by
  simp [herm, mulVec_add]

theorem herm_sub_left (v w u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (w - u) v = herm (Hpk k r) w v - herm (Hpk k r) u v := by
  simp [herm, mulVec_sub]

theorem det_H : IsUnit (Hpk k r).det := isUnit_det_of_left_inverse (GBasic.Hpk_sq k r)

theorem unit_det {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det := ((unitary_group_holds _ _ det_H).2.2 g hg).1

theorem inv_mem {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r := ((unitary_group_holds _ _ det_H).2.2 g hg).2

theorem herm_isom {ι : Type} [Fintype ι] [DecidableEq ι] {H g : Matrix ι ι ℂ} (hg : g ∈ UH H) (v w : ι → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg']

theorem mul_inv_vec {g : Mat k r} (hg : g ∈ GG k r) (v : Fin (2 * r + k + 1) → ℂ) : g *ᵥ (g⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, mul_nonsing_inv _ (unit_det hg), one_mulVec]

theorem inv_mul_vec {g : Mat k r} (hg : g ∈ GG k r) (v : Fin (2 * r + k + 1) → ℂ) : g⁻¹ *ᵥ (g *ᵥ v) = v := by
  rw [mulVec_mulVec, nonsing_inv_mul _ (unit_det hg), one_mulVec]

theorem herm_adj {g : Mat k r} (hg : g ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) w = herm (Hpk k r) v (g⁻¹ *ᵥ w) := by
  rw [← herm_isom hg v (g⁻¹ *ᵥ w), mul_inv_vec hg]

theorem inv_eig {g : Mat k r} (hg : g ∈ GG k r) {c : ℂ} (hc : c ≠ 0) {v w : Fin (2 * r + k + 1) → ℂ}
    (h : g *ᵥ v = c • w) : g⁻¹ *ᵥ w = c⁻¹ • v := by
  have := inv_mul_vec hg v
  rw [h, mulVec_smul] at this
  rw [← this, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem zhat_inv (z z' : Fin (2 * r + k + 1) → ℂ) {g : Mat k r} (hg : g ∈ GG k r) :
    Zhat k r z' z g⁻¹ = (Zhat k r z z' g)ᴴ := by
  ext a b
  rw [conjTranspose_apply]
  unfold Zhat
  rw [herm_adj hg, ← herm_star]

theorem dmin_inv (z z' : Fin (2 * r + k + 1) → ℂ) {g : Mat k r} (hg : g ∈ GG k r) (l : Fin (r + 2)) :
    ‖Dmin k r z' z g⁻¹ l‖ = ‖Dmin k r z z' g l‖ := by
  unfold Dmin
  rw [zhat_inv z z' hg, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, norm_star]

theorem zr_eq (g : Mat k r) (a b : Fin r) :
    Zr k r g a b = herm (Hpk k r) (g *ᵥ bvec (eI k r b)) (bvec (eI k r a)) := by
  rw [herm_e]; simp [Zr, bvec]

theorem zr_inv {g : Mat k r} (hg : g ∈ GG k r) : Zr k r g⁻¹ = (Zr k r g)ᴴ := by
  ext a b
  rw [conjTranspose_apply, zr_eq, zr_eq, herm_adj hg, ← herm_star]

theorem blockAnti_conjTranspose {n : ℕ} {β : Fin n → ℕ} {Z : Matrix (Fin n) (Fin n) ℂ} (h : BlockAnti β Z) :
    BlockAnti β Zᴴ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by rw [det_conjTranspose]; simpa using h2, fun a b hab => ?_, fun a b a' b' hab hab' hβ => ?_⟩
  · rw [conjTranspose_apply] at hab
    exact (h3 b a (by simpa using hab)).symm
  · rw [conjTranspose_apply] at hab hab'
    have e1 : Z b a ≠ 0 := by simpa using hab
    have e2 : Z b' a' ≠ 0 := by simpa using hab'
    have hb : β b = β b' := by rw [h3 b a e1, h3 b' a' e2, hβ]
    obtain ⟨p1, p2, p3⟩ := h4 b a b' a' e1 e2 hb
    obtain ⟨-, -, q3⟩ := h4 b' a' b a e2 e1 hb.symm
    refine ⟨by simpa [conjTranspose_apply] using p1, fun haa => ?_, fun haa => ?_⟩
    · rcases lt_trichotomy b b' with h | h | h
      · exact absurd (p3 h) (by rw [haa]; exact lt_irrefl _)
      · exact h
      · exact absurd (q3 h) (by rw [haa]; exact lt_irrefl _)
    · rcases lt_trichotomy b b' with h | h | h
      · exact absurd (p3 h) (not_lt.2 haa.le)
      · exact absurd (p2 h) haa.ne
      · exact h

theorem inWb_iff (v : Fin (2 * r + k + 1) → ℂ) :
    inWb k r v ↔ ∀ a : Fin r, v (eI k r a) = 0 ∧ v (esI k r a) = 0 := by
  constructor
  · intro h a
    have ha := a.isLt
    exact ⟨h _ (Or.inl ha), h _ (Or.inr (by simp only [esI]; omega))⟩
  · intro h i hi
    have := i.isLt
    rcases hi with hi | hi
    · exact (h ⟨i.val, hi⟩).1
    · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := Fin.ext (by simp only [esI]; omega)
      rw [e]; exact (h _).2

theorem sum_mid (f : Fin (2 * r + k + 1) → ℂ) (hf : inWb k r f) : ∑ i, f i = ∑ j : Fin (k + 1), f (wI k r j) := by
  symm
  refine Fintype.sum_of_injective (wI k r) (fun a b h => Fin.ext ?_) _ _ (fun i hi => hf i ?_) fun _ => rfl
  · have := congrArg Fin.val h
    simp only [wI] at this; omega
  · by_contra hc
    exact hi ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩

theorem herm_mid (v w : Fin (2 * r + k + 1) → ℂ) (hw : inWb k r w) :
    herm (Hpk k r) v w = herm (Hb k) (fun j => v (wI k r j)) fun j => w (wI k r j) := by
  unfold herm dotProduct
  rw [sum_mid _ (fun i hi => by simp [hw i hi])]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := j.isLt
  have h1 : GBasic.sig k r (wI k r j) = wI k r j :=
    GBasic.sig_mid k r _ (by simp only [wI]; omega) (by simp only [wI]; omega)
  have h2 : GBasic.sgn k r (wI k r j) = if j = Fin.last k then -1 else 1 := by
    simp [GBasic.sgn, wI, Fin.ext_iff]
  simp [Hb, mulVec_diagonal, mulVec, dotProduct, GBasic.Hpk_eq, h1, h2, diagonal_apply]

theorem herm_span_zero {s : Set (Fin (2 * r + k + 1) → ℂ)} {v : Fin (2 * r + k + 1) → ℂ}
    (h : ∀ u ∈ s, herm (Hpk k r) v u = 0) {u : Fin (2 * r + k + 1) → ℂ} (hu : u ∈ Submodule.span ℂ s) :
    herm (Hpk k r) v u = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp [herm]
  | add x y _ _ hx hy => rw [herm_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [herm_smul_right, hx, mul_zero]

theorem herm_Wb_XstJ {j : ℕ} {w u : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (hu : u ∈ XstJ k r j) :
    herm (Hpk k r) w u = 0 := by
  refine herm_span_zero ?_ hu
  rintro _ ⟨a, rfl⟩
  rw [herm_es]; exact ((inWb_iff w).1 hw _).1

theorem esI_inj {a b : Fin r} : esI k r a = esI k r b ↔ a = b := by
  have := a.isLt; have := b.isLt
  simp only [esI, Fin.ext_iff]; omega

theorem herm_XstJ {j : ℕ} (hj : j ≤ r) (v : Fin (2 * r + k + 1) → ℂ) {u : Fin (2 * r + k + 1) → ℂ} (hu : u ∈ XstJ k r j) :
    herm (Hpk k r) v u = ∑ a : Fin j, star (u (esI k r (Fin.castLE hj a))) * v (eI k r (Fin.castLE hj a)) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hx
    rw [herm_es, Finset.sum_eq_single (⟨a.val, ha⟩ : Fin j)]
    · have : Fin.castLE hj (⟨a.val, ha⟩ : Fin j) = a := rfl
      simp [this, bvec]
    · intro b _ hb
      have : esI k r (Fin.castLE hj b) ≠ esI k r a := fun h => by
        have := congrArg Fin.val (esI_inj.1 h)
        exact hb (Fin.ext this)
      simp [bvec, this]
    · simp
  | zero => simp [herm]
  | add x y _ _ hx hy => rw [herm_add_right, hx, hy, ← Finset.sum_add_distrib]; simp [add_mul]
  | smul c x _ hx => rw [herm_smul_right, hx, Finset.mul_sum]; simp [mul_assoc]

variable {j : ℕ} {hj : j ≤ r} {β : Fin r → ℕ} {c : ℂ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r}

theorem c_ne (h : IsNormal0 k r hj β c z z' g) : c ≠ 0 := by
  intro h0; have := h.2.1; rw [h0] at this; simp at this

theorem isNormal0_inv (h : IsNormal0 k r hj β c z z' g) : IsNormal0 k r hj β c⁻¹ z' z g⁻¹ := by
  have hc := c_ne h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨inv_mem h1, by rw [norm_inv, h2, inv_one], inv_eig h1 hc h3, h4, h5, fun a ha => ?_,
    fun a ha => ⟨inv_eig h1 hc (h7 a ha).1, inv_eig h1 hc (h7 a ha).2⟩, ?_⟩
  · rw [nonsing_inv_nonsing_inv _ (unit_det h1)]
    exact ⟨(h6 a ha).2, (h6 a ha).1⟩
  · rw [zr_inv h1, ← Matrix.conjTranspose_submatrix]
    exact blockAnti_conjTranspose h8

theorem herm_Wb_inv_e (h : IsNormal0 k r hj β c z z' g) {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) :
    herm (Hpk k r) w (g⁻¹ *ᵥ bvec (eI k r a)) = 0 := by
  by_cases ha : a.val < j
  · exact herm_Wb_XstJ hw (h.2.2.2.2.2.1 a ha).1
  · rw [((isNormal0_inv h).2.2.2.2.2.2.1 a (not_lt.1 ha)).1, herm_smul_right, herm_e, ((inWb_iff w).1 hw _).2, mul_zero]

theorem inWb_mulVec (h : IsNormal0 k r hj β c z z' g) {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) :
    inWb k r (g *ᵥ w) := by
  rw [inWb_iff]
  intro a
  refine ⟨?_, by rw [← herm_e (g *ᵥ w), herm_adj h.1, herm_Wb_inv_e h hw]⟩
  by_cases ha : a.val < j
  · have key : ((Zr k r g).submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ *ᵥ
        (fun b : Fin j => (g *ᵥ w) (eI k r (Fin.castLE hj b))) = 0 := by
      funext b
      have e1 := herm_XstJ hj (g *ᵥ w) (h.2.2.2.2.2.1 (Fin.castLE hj b) b.isLt).2
      rw [herm_isom h.1, herm_e, ((inWb_iff w).1 hw _).2] at e1
      rw [Pi.zero_apply, e1]
      rw [mulVec, dotProduct]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [Zr, bvec]
    have := Matrix.eq_zero_of_mulVec_eq_zero (blockAnti_conjTranspose h.2.2.2.2.2.2.2).2.1 key
    exact congrFun this ⟨a.val, ha⟩
  · rw [← herm_es (g *ᵥ w), herm_adj h.1, ((isNormal0_inv h).2.2.2.2.2.2.1 a (not_lt.1 ha)).2, herm_smul_right, herm_es,
      ((inWb_iff w).1 hw _).1, mul_zero]

theorem inWb_bvec (i : Fin (k + 1)) : inWb k r (bvec (wI k r i)) := by
  intro p hp
  have : p ≠ wI k r i := by
    rintro rfl
    have := i.isLt
    simp only [wI] at hp; omega
  simp [bvec, this]

theorem wI_inj {a b : Fin (k + 1)} : wI k r a = wI k r b ↔ a = b := by
  simp only [wI, Fin.ext_iff]; omega

theorem exists_mid (hg : g ∈ GG k r) (hW : ∀ w, inWb k r w → inWb k r (g *ᵥ w)) :
    ∃ m ∈ UH (Hb k), ∀ w, inWb k r w → g *ᵥ w = mEmb k r m *ᵥ w := by
  refine ⟨g.submatrix (wI k r) (wI k r), ?_, fun w hw => ?_⟩
  · show _ = _
    ext a b
    have e1 := herm_isom hg (bvec (wI k r b)) (bvec (wI k r a))
    rw [herm_mid _ _ (hW _ (inWb_bvec a)), herm_mid _ _ (inWb_bvec a)] at e1
    rw [Matrix.mul_assoc]
    convert e1 using 1
    · simp [herm, bvec, Matrix.mul_apply, dotProduct, mulVec, Pi.single_apply]
    · simp [herm, bvec, dotProduct, mulVec, Pi.single_apply, wI_inj]
  · funext i
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hW w hw i hi]
      symm
      rw [mulVec, dotProduct]
      refine Finset.sum_eq_zero fun p _ => ?_
      have : ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ p.val ∧ p.val ≤ r + k)) := by omega
      simp only [mEmb, dif_neg this]
      split_ifs with hp
      · rw [← hp, hw i hi, mul_zero]
      · rw [zero_mul]
    · rw [mulVec, mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p.val < r ∨ r + k < p.val
      · simp only [hw p hp, mul_zero]
      · have : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ p.val ∧ p.val ≤ r + k) := by omega
        simp only [mEmb, dif_pos this, submatrix_apply]
        congr 2 <;> exact Fin.ext (by simp only [wI]; omega)

theorem tz_eq (h : IsNormal0 k r hj β c z z' g) : Tz k r z' = Tz k r z := by
  unfold Tz
  rw [← herm_isom h.1 z' z', h.2.2.1, herm_smul_left, herm_smul_right, ← mul_assoc, Complex.star_def, Complex.mul_conj',
    h.2.1]
  simp

theorem dj_pos (h : IsNormal0 k r hj β c z z' g) : 0 < Dj k r hj z z' g := by
  unfold Dj Dmin
  rw [norm_pos_iff]
  convert h.2.2.2.2.2.2.2.2.1 using 2
  ext a b
  have ha : a.val < r := lt_of_lt_of_le a.isLt hj
  have hb : b.val < r := lt_of_lt_of_le b.isLt hj
  simp only [submatrix_apply, Zhat, zr_eq, fvec, Fin.coe_castLE, dif_pos ha, dif_pos hb]
  rfl

theorem herm_Xsp_fvec (hz' : inWb k r z') {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) (a : Fin (r + 1)) :
    herm (Hpk k r) x (fvec k r z' a) = 0 := by
  rw [herm_star, star_eq_zero]
  refine herm_span_zero ?_ hx
  rintro _ ⟨b, rfl⟩
  rw [herm_e]
  unfold fvec
  split_ifs with ha
  · have : esI k r b ≠ eI k r ⟨a.val, ha⟩ := by
      have := b.isLt
      simp only [esI, eI, Ne, Fin.ext_iff]; omega
    simp [bvec, this]
  · exact ((inWb_iff z').1 hz' b).2

theorem mem_hcom_sup (h : IsNormal0 k r hj β c z z' g) (hz' : inWb k r z') (w : Fin (2 * r + k + 1) → ℂ) :
    w ∈ Hcom k r z z' g ⊔ Xsp k r ↔ ∀ a : Fin (r + 1), herm (Hpk k r) w (fvec k r z' a) = 0 := by
  constructor
  · intro hw a
    obtain ⟨y, hy, x, hx, rfl⟩ := Submodule.mem_sup.1 hw
    rw [herm_add_left, (hy a).1, herm_Xsp_fvec hz' hx, add_zero]
  · intro hw
    set x : Fin (2 * r + k + 1) → ℂ := ∑ b : Fin r, w (eI k r b) • bvec (eI k r b) with hxdef
    have hx : x ∈ Xsp k r :=
      Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    have h1 : ∀ a : Fin (r + 1), herm (Hpk k r) (w - x) (fvec k r z' a) = 0 := fun a => by
      rw [herm_sub_left, hw a, herm_Xsp_fvec hz' hx, sub_zero]
    have h2 : inWb k r (w - x) := by
      rw [inWb_iff]
      intro a
      constructor
      · have hinj : ∀ b : Fin r, eI k r a = eI k r b ↔ a = b := fun b => by simp [eI, Fin.ext_iff]
        simp [hxdef, Finset.sum_apply, bvec, Pi.single_apply, hinj]
      · have := h1 a.castSucc
        simp only [fvec, Fin.coe_castSucc, a.isLt, dif_pos] at this
        rwa [herm_e] at this
    refine Submodule.mem_sup.2 ⟨w - x, fun a => ⟨h1 a, ?_⟩, x, hx, sub_add_cancel w x⟩
    unfold fvec
    split_ifs with ha
    · exact herm_Wb_inv_e h h2 _
    · have := h1 a
      simp only [fvec, dif_neg ha] at this
      rw [(isNormal0_inv h).2.2.1, herm_smul_right, this, mul_zero]

theorem normal0_middle : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → Tz k r z' = Tz k r z ∧ (∃ m ∈ UH (Hb k), ∀ w, inWb k r w → g₀ *ᵥ w = mEmb k r m *ᵥ w) ∧ IsNormal0 k r hj β c⁻¹ z' z g₀⁻¹ ∧ 0 < Dj k r hj z z' g₀ ∧ Dj k r hj z' z g₀⁻¹ = Dj k r hj z z' g₀ ∧ (∀ l : Fin (r + 2), ‖Dmin k r z' z g₀⁻¹ l‖ = ‖Dmin k r z z' g₀ l‖) ∧ ∀ w, w ∈ Hcom k r z z' g₀ ⊔ Xsp k r ↔ ∀ a : Fin (r + 1), herm (Hpk k r) w (fvec k r z' a) = 0 :=
  fun _ _ _ _ z z' _ _ _ _ hz' _ h =>
    ⟨tz_eq h, exists_mid h.1 fun _ => inWb_mulVec h, isNormal0_inv h, dj_pos h, dmin_inv z z' h.1 _,
      dmin_inv z z' h.1, mem_hcom_sup h hz'⟩

end GlobalTheory.Amp.NfMid
