import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.NegOnePowMulSelf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.ContinuousRootCoords
import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds

open Matrix

noncomputable section

namespace PI.AmpRootHaarW

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon PI.AmpRootJacW

variable {k r : ℕ}

theorem Hpk_eI (b : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r b) j = if j = esI k r b then 1 else 0 := by
  rw [Hpk_apply]
  have hb := b.isLt
  have hj := j.isLt
  have he : (esI k r b).val = 2 * r + k - b.val := rfl
  have hE : (eI k r b).val = b.val := rfl
  simp only [hτ, hs, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mulVec_eI (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    (Hpk k r *ᵥ y) (eI k r b) = y (esI k r b) := by
  simp only [Matrix.mulVec, dotProduct, Hpk_eI, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem Hpk_mulVec_low {w : Fin (2 * r + k + 1) → ℂ} (hw : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → w i = 0)
    (i : Fin (2 * r + k + 1)) (hi : i.val ≤ r + k) : (Hpk k r *ᵥ w) i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  rw [Hpk_apply]
  split_ifs with h
  · rw [hw j (by unfold hτ at h; split_ifs at h <;> omega), mul_zero]
  · rw [zero_mul]

theorem esI_of (j : Fin (2 * r + k + 1)) (hj : r + k < j.val) :
    esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
  apply Fin.ext
  show 2 * r + k - (2 * r + k - j.val) = j.val
  have := j.isLt
  omega

theorem fvec_high {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin (r + 1)) (i : Fin (2 * r + k + 1))
    (hi : r + k < i.val) : fvec k r z a i = 0 := by
  unfold fvec
  split_ifs with h
  · unfold bvec
    rw [Pi.single_eq_of_ne]
    intro he
    have h' := congrArg Fin.val he
    have hv : (eI k r ⟨a.val, h⟩).val = a.val := rfl
    omega
  · exact hz i (Or.inr hi)

theorem fvec_cs (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r) : fvec k r z (Fin.castSucc c) = bvec (eI k r c) := by
  unfold fvec
  rw [dif_pos (show (Fin.castSucc c).val < r from c.isLt)]
  rfl

theorem nset_fix {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r)
    {y : Fin (2 * r + k + 1) → ℂ} (hy : ∀ b : Fin r, y (esI k r b) = 0)
    (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) : (a *ᵥ y) i = y i := by
  have hterm : ∀ j, a i j * y j = if j = i then y i else 0 := by
    intro j
    by_cases hj1 : j.val < r
    · have h2 := ha.2.1 ⟨j.val, hj1⟩ i (by show j.val ≤ i.val; omega)
      have hej : eI k r ⟨j.val, hj1⟩ = j := Fin.ext rfl
      rw [hej, if_neg (fun h => by rw [h] at hi; omega)] at h2
      rw [h2, zero_mul, if_neg (fun h => by rw [h] at hj1; omega)]
    · by_cases hj2 : j.val ≤ r + k
      · rw [ha.2.2 i j (by omega) hj2 hi]
        by_cases hij : i = j
        · subst hij
          simp
        · rw [if_neg hij, if_neg (Ne.symm hij), zero_mul]
      · have hyj : y j = 0 := by
          have := hy ⟨2 * r + k - j.val, by have := j.isLt; omega⟩
          rwa [esI_of j (by omega)] at this
        rw [hyj, mul_zero]
        split_ifs with hji
        · subst hji
          exact hyj.symm
        · rfl
  simp only [Matrix.mulVec, dotProduct, hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem zhat_mulVec_inj {z z' : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : Point ℂ (r + 1)} (hP : ZhatO k r z z' g = ptMat p) {β : Fin (r + 1) → ℂ}
    (h : Zhat k r z z' g *ᵥ β = 0) : β = 0 := by
  funext j
  show β j = 0
  have h1 := congrFun h (ptσ p j)
  simp only [Matrix.mulVec, dotProduct, zhat_pt hP, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Pi.zero_apply, ptσ_invol] at h1
  exact (mul_eq_zero.mp h1).resolve_left (ptζ_ne p _)

theorem fm_low (z' : Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1) → ℂ)
    (hx : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → x i = 0) :
    Fm k r z' *ᵥ (fun b : Fin (r + 1) => if h : b.val < r then x (eI k r ⟨b.val, h⟩) else 0) = x := by
  funext i
  have hc : ∀ c : Fin r, (if h : (Fin.castSucc c).val < r then x (eI k r ⟨(Fin.castSucc c).val, h⟩) else 0)
      = x (eI k r c) := by
    intro c
    rw [dif_pos (show (Fin.castSucc c).val < r from c.isLt)]
    rfl
  have hl : (if h : (Fin.last r).val < r then x (eI k r ⟨(Fin.last r).val, h⟩) else 0) = 0 := by
    rw [dif_neg (show ¬ (Fin.last r).val < r from lt_irrefl r)]
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_castSucc]
  simp only [hc, hl, mul_zero, add_zero, Fm, Matrix.of_apply, fvec_cs, bvec]
  by_cases hi : i.val < r
  · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
    · have hei : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
      rw [hei, Pi.single_eq_same, one_mul]
    · intro c _ hc'
      rw [Pi.single_eq_of_ne, zero_mul]
      intro he
      apply hc'
      have h' := congrArg Fin.val he
      have hv : (eI k r c).val = c.val := rfl
      exact Fin.ext (by rw [← hv, ← h'])
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [hx i (by omega)]
    apply Finset.sum_eq_zero
    intro c _
    rw [Pi.single_eq_of_ne, zero_mul]
    intro he
    have h' := congrArg Fin.val he
    have hv : (eI k r c).val = c.val := rfl
    have := c.isLt
    omega

theorem cap_zero {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) {p : Point ℂ (r + 1)}
    (hP : ZhatO k r z z' g = ptMat p) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → w i = 0)
    (hw' : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (g⁻¹ *ᵥ w) i = 0) : w = 0 := by
  have hgg : g * g⁻¹ = 1 := uh_mul_inv hg
  have hgw : g *ᵥ (g⁻¹ *ᵥ w) = w := by rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  have hrep := fm_low z' (g⁻¹ *ᵥ w) hw'
  have hZ : Zhat k r z z' g *ᵥ (fun b : Fin (r + 1) =>
      if h : b.val < r then (g⁻¹ *ᵥ w) (eI k r ⟨b.val, h⟩) else 0) = (Fm k r z)ᴴ *ᵥ (Hpk k r *ᵥ w) := by
    rw [zhat_eq, ← Matrix.mulVec_mulVec, hrep, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgw]
  have hzero : (Fm k r z)ᴴ *ᵥ (Hpk k r *ᵥ w) = 0 := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Fm, Matrix.of_apply, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i.val ≤ r + k
    · have := Hpk_mulVec_low hw i hi
      simp only [Matrix.mulVec, dotProduct] at this
      rw [this, mul_zero]
    · rw [fvec_high hz a i (by omega), star_zero, zero_mul]
  have hc0 := zhat_mulVec_inj hP (hZ.trans hzero)
  have hgw0 : g⁻¹ *ᵥ w = 0 := by rw [← hrep, hc0, Matrix.mulVec_zero]
  rw [← hgw, hgw0, Matrix.mulVec_zero]

theorem rstab_fix {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) {p : Point ℂ (r + 1)}
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) {v : Fin (2 * r + k + 1) → ℂ}
    (h1 : ∀ b : Fin r, v (esI k r b) = 0) (h2 : ∀ b : Fin r, (g⁻¹ *ᵥ v) (esI k r b) = 0) : a *ᵥ v = v := by
  have hgg : g * g⁻¹ = 1 := uh_mul_inv hg
  have hd1 : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (a *ᵥ v - v) i = 0 := by
    intro i hi
    rw [Pi.sub_apply, nset_fix ha.1 h1 i hi, sub_self]
  have hd2 : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (g⁻¹ *ᵥ (a *ᵥ v - v)) i = 0 := by
    intro i hi
    have e : g⁻¹ *ᵥ (a *ᵥ v) = (g⁻¹ * a * g) *ᵥ (g⁻¹ *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (g⁻¹ * a), hgg, Matrix.mul_one]
    rw [Matrix.mulVec_sub, Pi.sub_apply, e, nset_fix ha.2 h2 i hi, sub_self]
  exact sub_eq_zero.mp (cap_zero hz hg hP hd1 hd2)

def GV (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun i j => gramVec k r z z' g j i

theorem gramM_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    gramM k r z z' g = (GV k r z z' g)ᴴ * (Hpk k r * GV k r z z' g) := by
  ext i j
  simp only [gramM, herm, GV, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply]

theorem gv_inl (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    ((GV k r z z' g)ᴴ *ᵥ y) (Sum.inl (Fin.castSucc b)) = y (eI k r b) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, GV, Matrix.of_apply, gramVec, fvec_cs,
    bvec, Pi.single_apply]
  rw [Finset.sum_eq_single (eI k r b)]
  · simp
  · intro c _ hc
    simp [hc]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem gv_inr (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    ((GV k r z z' g)ᴴ *ᵥ y) (Sum.inr (Fin.castSucc b)) = (gᴴ *ᵥ y) (eI k r b) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, GV, Matrix.of_apply, gramVec, fvec_cs,
    bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem uh_ct_H {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  calc gᴴ * Hpk k r = gᴴ * Hpk k r * (g * g⁻¹) := by rw [uh_mul_inv hg, Matrix.mul_one]
    _ = Hpk k r * g⁻¹ := by rw [← Matrix.mul_assoc, h]

theorem perp_esI {z z' : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) {v : Fin (2 * r + k + 1) → ℂ} (hv : (GV k r z z' g)ᴴ *ᵥ (Hpk k r *ᵥ v) = 0) :
    (∀ b : Fin r, v (esI k r b) = 0) ∧ (∀ b : Fin r, (g⁻¹ *ᵥ v) (esI k r b) = 0) := by
  refine ⟨fun b => ?_, fun b => ?_⟩
  · have := congrFun hv (Sum.inl (Fin.castSucc b))
    rw [gv_inl, Hpk_mulVec_eI] at this
    exact this
  · have := congrFun hv (Sum.inr (Fin.castSucc b))
    rw [gv_inr, Matrix.mulVec_mulVec, uh_ct_H hg, ← Matrix.mulVec_mulVec, Hpk_mulVec_eI] at this
    exact this

theorem mat_eq_zero_of_span {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
    (V : Matrix (Fin m) ι ℂ) (hdet : IsUnit (Vᴴ * (H * V)).det) (d : Matrix (Fin m) (Fin m) ℂ)
    (h1 : d * V = 0) (h2 : ∀ v, Vᴴ *ᵥ (H *ᵥ v) = 0 → d *ᵥ v = 0) : d = 0 := by
  set G := Vᴴ * (H * V) with hG
  have hGi : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
  have hv : ∀ v, d *ᵥ v = 0 := by
    intro v
    set c := G⁻¹ *ᵥ (Vᴴ *ᵥ (H *ᵥ v)) with hc
    have hu : Vᴴ *ᵥ (H *ᵥ (v - V *ᵥ c)) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec (M := H) (N := V),
        Matrix.mulVec_mulVec (M := Vᴴ) (N := H * V), ← hG, hc, Matrix.mulVec_mulVec (M := G) (N := G⁻¹),
        hGi, Matrix.one_mulVec, sub_self]
    have h3 := h2 _ hu
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec (M := d) (N := V), h1, Matrix.zero_mulVec, sub_zero] at h3
    exact h3
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem rstab_inj {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    {p : Point ℂ (r + 1)} (hP : ZhatO k r z z' g = ptMat p) (hdet : (gramM k r z z' g).det ≠ 0)
    {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ RStab k r g) (hb : b ∈ RStab k r g)
    (hab : flagMat k r z a = flagMat k r z b) : a = b := by
  have hx : g⁻¹ * a * g ∈ Nset k r := ha.2
  have hy : g⁻¹ * b * g ∈ Nset k r := hb.2
  have hra := flag_rel hz hz' hg ha
  have hrb := flag_rel hz hz' hg hb
  rw [hab] at hra
  have hUd : IsUnit (flagMat k r z b)ᴴ.det := by
    rw [Matrix.det_conjTranspose, Matrix.det_of_upperTriangular (flagMat_upper hb.1),
      Finset.prod_eq_one fun i _ => flagMat_diag hb.1 i, star_one]
    exact isUnit_one
  have hZ : Zhat k r z z' g * (flagMat k r z' (g⁻¹ * a * g) - flagMat k r z' (g⁻¹ * b * g)) = 0 := by
    have e : (flagMat k r z b)ᴴ * (Zhat k r z z' g *
        (flagMat k r z' (g⁻¹ * a * g) - flagMat k r z' (g⁻¹ * b * g))) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hra, hrb, sub_self]
    have e2 := congrArg (fun M => ((flagMat k r z b)ᴴ)⁻¹ * M) e
    simp only [Matrix.mul_zero] at e2
    rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUd, Matrix.one_mul] at e2
  have hM : flagMat k r z' (g⁻¹ * a * g) - flagMat k r z' (g⁻¹ * b * g) = 0 := by
    ext i c
    have hcol : (fun l => (flagMat k r z' (g⁻¹ * a * g) - flagMat k r z' (g⁻¹ * b * g)) l c) = 0 := by
      apply zhat_mulVec_inj hP
      funext m
      have := congrFun (congrFun hZ m) c
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    exact congrFun hcol i
  have hfl' := sub_eq_zero.mp hM
  have hcols : ∀ j, a *ᵥ gramVec k r z z' g j = b *ᵥ gramVec k r z z' g j := by
    intro j
    rcases j with c | c
    · have hA := mul_Fm hz ha.1
      have hB := mul_Fm hz hb.1
      have hAB : a * Fm k r z = b * Fm k r z := by rw [hA, hB, hab]
      funext m
      have := congrFun (congrFun hAB m) c
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fm, gramVec] using this
    · have hA := mul_Fm hz' hx
      have hB := mul_Fm hz' hy
      have hAB : (g⁻¹ * a * g) * Fm k r z' = (g⁻¹ * b * g) * Fm k r z' := by rw [hA, hB, hfl']
      have hgg : g * g⁻¹ = 1 := uh_mul_inv hg
      have key : ∀ e : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
          e *ᵥ (g *ᵥ fvec k r z' c) = g *ᵥ ((g⁻¹ * e * g) *ᵥ fvec k r z' c) := by
        intro e
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hgg,
          Matrix.one_mul]
      show a *ᵥ (g *ᵥ fvec k r z' c) = b *ᵥ (g *ᵥ fvec k r z' c)
      rw [key a, key b]
      congr 1
      funext m
      have := congrFun (congrFun hAB m) c
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fm] using this
  have hd1 : (a - b) * GV k r z z' g = 0 := by
    ext m j
    have := congrFun (hcols j) m
    simp only [Matrix.mul_apply, Matrix.sub_apply, GV, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
      Matrix.zero_apply]
    simp only [Matrix.mulVec, dotProduct] at this
    rw [this, sub_self]
  have hd2 : ∀ v, (GV k r z z' g)ᴴ *ᵥ (Hpk k r *ᵥ v) = 0 → (a - b) *ᵥ v = 0 := by
    intro v hv
    obtain ⟨h1, h2⟩ := perp_esI hg hv
    rw [Matrix.sub_mulVec, rstab_fix hz hg hP ha h1 h2, rstab_fix hz hg hP hb h1 h2, sub_self]
  have hdet' : IsUnit ((GV k r z z' g)ᴴ * (Hpk k r * GV k r z z' g)).det := by
    rw [← gramM_eq]
    exact isUnit_iff_ne_zero.mpr hdet
  exact sub_eq_zero.mp (mat_eq_zero_of_span (Hpk k r) (GV k r z z' g) hdet' (a - b) hd1 hd2)

theorem flagZ_eq {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    {p : Point ℂ (r + 1)} (hP : ZhatO k r z z' g = ptMat p)
    {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ RStab k r g) :
    flagMat k r z a = 1 + vM (rootPat p) (rootCoords k r z p (fun i j => a i j)) := by
  ext i j
  rw [Matrix.add_apply]
  simp only [vM, rootCoords]
  by_cases hq : (i, j) ∈ rootPat p
  · rw [dif_pos hq]
    have hij : i ≠ j := ne_of_lt (mem_rootPat.mp hq).1
    rw [Matrix.one_apply_ne hij, zero_add]
    rfl
  · rw [dif_neg hq, add_zero]
    by_cases hji : j ≤ i
    · rw [flagMat_lower ha.1 i j hji, Matrix.one_apply]
    · have hij : i < j := not_le.mp hji
      have hne : blockIdx p.1 i.val ≠ blockIdx p.1 j.val := fun h => hq (mem_rootPat.mpr ⟨hij, h⟩)
      have hlt : (ptσ p i).val < (ptσ p j).val :=
        blk_lt p.1 i.val j.val hij (by rw [p.2.2]; exact j.isLt) hne
      rw [(flag_offblock hz hz' hg hP ha i j hlt).2, Matrix.one_apply_ne (ne_of_lt hij)]

theorem rootCoords_injOn {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    {p : Point ℂ (r + 1)} (hP : ZhatO k r z z' g = ptMat p) (hdet : (gramM k r z z' g).det ≠ 0) :
    Set.InjOn (rootCoords k r z p) {x : Mt k r | Matrix.of x ∈ RStab k r g} := by
  intro x hx y hy hxy
  have h1 := flagZ_eq hz hz' hg hP hx
  have h2 := flagZ_eq hz hz' hg hP hy
  have hfl : flagMat k r z (Matrix.of x) = flagMat k r z (Matrix.of y) := by
    show flagMat k r z x = flagMat k r z y
    rw [h1, h2]
    congr 1
    exact congrArg (vM (rootPat p)) hxy
  exact Matrix.of.injective (rstab_inj hz hz' hg hP hdet hx hy hfl)

end PI.AmpRootHaarW
