import Mathlib
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

open Matrix

noncomputable section

namespace PI.MirrorSection₂

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

section Grp

variable {k r : ℕ}

theorem hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  let t : Fin (2 * r + k + 1) :=
    ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩
  rw [Finset.sum_eq_single t]
  · simp only [Hpk, t, Fin.ext_iff]
    split_ifs <;> first | omega | norm_num
  · intro l _ hl
    have hl' : l.val ≠ t.val := fun h => hl (Fin.ext h)
    simp only [t] at hl'
    simp only [Hpk, Fin.ext_iff]
    split_ifs at hl' ⊢ <;> first | omega | norm_num
  · simp

theorem uh_mul {a b : B.Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem uh_inv {a : B.Mat k r} (ha : a ∈ UH (Hpk k r)) :
    a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 ∧ a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hl : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc Hpk k r * aᴴ * Hpk k r * a = Hpk k r * (aᴴ * Hpk k r * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha', hpk_sq]
  have hinv : a⁻¹ = Hpk k r * aᴴ * Hpk k r := Matrix.inv_eq_left_inv hl
  have h1 : a⁻¹ * a = 1 := by rw [hinv]; exact hl
  have h2 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a (Matrix.isUnit_det_of_left_inverse hl)
  refine ⟨h2, h1, ?_⟩
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2]; simp

theorem col_eq (g : B.Mat k r) (j : Fin (2 * r + k + 1)) : g *ᵥ bvec j = fun i => g i j := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

def lowS (k r a : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) where
  carrier := {y | ∀ i : Fin (2 * r + k + 1), a ≤ i.val → y i = 0}
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

theorem eI_val (a : Fin r) : (eI k r a).val = a.val := rfl

theorem maps_low {n : B.Mat k r} (hn : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      n i (eI k r a) = if i = eI k r a then 1 else 0) {a : ℕ} (har : a ≤ r) :
    ∀ y ∈ lowS k r a, n *ᵥ y ∈ lowS k r a := by
  intro y hy i hi
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : a ≤ l.val
  · rw [hy l hl, mul_zero]
  · have hlr : l.val < r := by omega
    have hle : (eI k r ⟨l.val, hlr⟩) = l := Fin.ext rfl
    have := hn ⟨l.val, hlr⟩ i (by simp; omega)
    rw [hle] at this
    rw [this, if_neg (by intro h; rw [h] at hi; omega), zero_mul]

theorem onto_low {g : B.Mat k r} (hg : g⁻¹ * g = 1) {a : ℕ} (hmaps : ∀ y ∈ lowS k r a, g *ᵥ y ∈ lowS k r a) :
    ∀ y ∈ lowS k r a, ∃ x ∈ lowS k r a, g *ᵥ x = y := by
  let f : lowS k r a →ₗ[ℂ] lowS k r a := (Matrix.mulVecLin g).restrict hmaps
  have hinj : Function.Injective f := by
    intro x x' hxx
    have h1 : g *ᵥ (x : Fin (2 * r + k + 1) → ℂ) = g *ᵥ x' := congrArg Subtype.val hxx
    have h2 := congrArg (fun v => g⁻¹ *ᵥ v) h1
    simp only [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec] at h2
    exact Subtype.ext h2
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

theorem n_inv {n : B.Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Nset k r := by
  have hu := uh_inv hn.1
  have hC1 := hn.2.1
  refine ⟨hu.2.2, ?_, ?_⟩
  · intro a i hai
    have hmaps := maps_low hC1 (a := a.val) a.isLt.le
    have hy : bvec (eI k r a) - n *ᵥ bvec (eI k r a) ∈ lowS k r a.val := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hC1 a l hl]
      simp [bvec, Pi.single_apply]
    obtain ⟨x, hx, hgx⟩ := onto_low hu.2.1 hmaps _ hy
    have hx2 : n *ᵥ (x + bvec (eI k r a)) = bvec (eI k r a) := by
      rw [Matrix.mulVec_add, hgx]
      abel
    have hx3 : n⁻¹ *ᵥ bvec (eI k r a) = x + bvec (eI k r a) := by
      rw [← hx2, Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec, hx2]
    have e := congrFun hx3 i
    rw [col_eq] at e
    simp only at e
    rw [e]
    simp only [Pi.add_apply]
    rw [hx i hai, zero_add]
    simp [bvec, Pi.single_apply]
  · intro i j hj1 hj2 hi
    have hmaps := maps_low hC1 (a := r) le_rfl
    have hy : bvec j - n *ᵥ bvec j ∈ lowS k r r := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hn.2.2 l j hj1 hj2 hl]
      simp [bvec, Pi.single_apply]
    obtain ⟨x, hx, hgx⟩ := onto_low hu.2.1 hmaps _ hy
    have hx2 : n *ᵥ (x + bvec j) = bvec j := by
      rw [Matrix.mulVec_add, hgx]
      abel
    have hx3 : n⁻¹ *ᵥ bvec j = x + bvec j := by
      rw [← hx2, Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec, hx2]
    have e := congrFun hx3 i
    rw [col_eq] at e
    simp only at e
    rw [e]
    simp only [Pi.add_apply]
    rw [hx i hi, zero_add]
    simp [bvec, Pi.single_apply]

theorem fix_low {g : B.Mat k r} (hfix : ∀ b : Fin r, g *ᵥ bvec (eI k r b) = bvec (eI k r b)) {a : ℕ}
    (har : a ≤ r) : ∀ y ∈ lowS k r a, g *ᵥ y = y := by
  intro y hy
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have hterm : ∀ l : Fin (2 * r + k + 1), g i l * y l = if i = l then y l else 0 := by
    intro l
    by_cases hl : a ≤ l.val
    · rw [hy l hl]
      simp
    · have hlr : l.val < r := by omega
      have hle : (eI k r ⟨l.val, hlr⟩) = l := Fin.ext rfl
      have := congrFun (hfix ⟨l.val, hlr⟩) i
      rw [col_eq, hle] at this
      simp only at this
      rw [this]
      by_cases hil : i = l
      · subst hil
        simp [bvec]
      · simp [bvec, Pi.single_apply, hil]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  simp

theorem herm_inv {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ x) (h *ᵥ y) = herm (Hpk k r) x y := by
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hh']

theorem hpk_row_esI (b : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r b) l = if l = eI k r b then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_row_eI (b : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r b) l = if l = esI k r b then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem herm_esI (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) y (bvec (esI k r b)) = y (eI k r b) := by
  unfold herm
  simp [bvec, dotProduct, Pi.single_apply, Matrix.mulVec, hpk_row_esI]

theorem herm_eI (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) y (bvec (eI k r b)) = y (esI k r b) := by
  unfold herm
  simp [bvec, dotProduct, Pi.single_apply, Matrix.mulVec, hpk_row_eI]

theorem uw_inWb {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : inWb k r (h *ᵥ v) := by
  intro l hl
  rcases hl with hl | hl
  · have hle : eI k r ⟨l.val, hl⟩ = l := Fin.ext rfl
    have key : (h *ᵥ v) (eI k r ⟨l.val, hl⟩) = 0 := by
      rw [← herm_esI (h *ᵥ v) ⟨l.val, hl⟩, ← (hh.2.1 ⟨l.val, hl⟩).2, herm_inv hh.1, herm_esI]
      exact hv _ (Or.inl hl)
    rwa [hle] at key
  · have hb : 2 * r + k - l.val < r := by omega
    have hle : esI k r ⟨2 * r + k - l.val, hb⟩ = l := by
      apply Fin.ext
      simp only [esI]
      omega
    have key : (h *ᵥ v) (esI k r ⟨2 * r + k - l.val, hb⟩) = 0 := by
      rw [← herm_eI (h *ᵥ v) ⟨2 * r + k - l.val, hb⟩, ← (hh.2.1 ⟨2 * r + k - l.val, hb⟩).1, herm_inv hh.1,
        herm_eI]
      rw [hle]
      exact hv l (Or.inr hl)
    rwa [hle] at key

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  have hu := uh_inv hh.1
  have back : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec]
  exact ⟨hu.2.2, fun a => ⟨back _ (hh.2.1 a).1, back _ (hh.2.1 a).2⟩, back _ hh.2.2⟩

theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ} {a b : B.Mat k r} (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z) :
    a * b ∈ UWset k r z := by
  refine ⟨uh_mul ha.1 hb.1, fun c => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).1, (ha.2.1 c).1]
  · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).2, (ha.2.1 c).2]
  · rw [← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]

theorem n_on_Wb {n : B.Mat k r} (hn : n ∈ Nset k r) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) :
    n *ᵥ u - u ∈ lowS k r r := by
  intro i hi
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  have hterm : ∀ l : Fin (2 * r + k + 1), n i l * u l = if i = l then u l else 0 := by
    intro l
    by_cases hl : l.val < r ∨ r + k < l.val
    · rw [hu l hl]
      simp
    · push Not at hl
      rw [hn.2.2 i l hl.1 hl.2 hi]
      by_cases hil : i = l <;> simp [hil]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  simp

theorem conj_n {z : Fin (2 * r + k + 1) → ℂ} {h n : B.Mat k r} (hh : h ∈ UWset k r z) (hn : n ∈ Nset k r) :
    h⁻¹ * n * h ∈ Nset k r := by
  have hu := uh_inv hh.1
  have hhi := uw_inv hh
  have hfixi : ∀ b : Fin r, h⁻¹ *ᵥ bvec (eI k r b) = bvec (eI k r b) := fun b => (hhi.2.1 b).1
  refine ⟨uh_mul (uh_mul hu.2.2 hn.1) hh.1, ?_, ?_⟩
  · intro a i hai
    have hcol : (h⁻¹ * n * h) *ᵥ bvec (eI k r a) = n *ᵥ bvec (eI k r a) := by
      rw [← Matrix.mulVec_mulVec, (hh.2.1 a).1, ← Matrix.mulVec_mulVec]
      apply fix_low hfixi le_rfl
      intro l hl
      rw [col_eq]
      simp only
      rw [hn.2.1 a l (by have := a.isLt; omega), if_neg]
      intro h'
      have h2 : l.val = a.val := congrArg Fin.val h'
      have := a.isLt
      omega
    have e := congrFun hcol i
    rw [col_eq, col_eq] at e
    simp only at e
    rw [e]
    exact hn.2.1 a i hai
  · intro i j hj1 hj2 hi
    have hbj : inWb k r (bvec j) := by
      intro l hl
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      intro h'
      rw [h'] at hl
      omega
    set u := h *ᵥ bvec j with hu_def
    have huW : inWb k r u := uw_inWb hh hbj
    have hd := n_on_Wb hn huW
    have hcol : (h⁻¹ * n * h) *ᵥ bvec j = bvec j + (n *ᵥ u - u) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu_def]
      have : n *ᵥ u = u + (n *ᵥ u - u) := by abel
      rw [this, Matrix.mulVec_add, fix_low hfixi le_rfl _ hd, hu_def, Matrix.mulVec_mulVec, hu.2.1,
        Matrix.one_mulVec]
      abel
    have e := congrFun hcol i
    rw [col_eq] at e
    simp only [Pi.add_apply] at e
    rw [e, hd i hi, add_zero]
    simp [bvec, Pi.single_apply]

theorem n_mul {n m : B.Mat k r} (hn : n ∈ Nset k r) (hm : m ∈ Nset k r) : n * m ∈ Nset k r := by
  refine ⟨uh_mul hn.1 hm.1, ?_, ?_⟩
  · intro a i hai
    have hy : m *ᵥ bvec (eI k r a) - bvec (eI k r a) ∈ lowS k r a.val := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hm.2.1 a l hl]
      simp [bvec, Pi.single_apply]
    have hmaps := maps_low hn.2.1 (a := a.val) a.isLt.le
    have hcol : (n * m) *ᵥ bvec (eI k r a) =
        n *ᵥ bvec (eI k r a) + n *ᵥ (m *ᵥ bvec (eI k r a) - bvec (eI k r a)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
      congr 1
      abel
    have e := congrFun hcol i
    rw [col_eq] at e
    simp only [Pi.add_apply] at e
    rw [e, hmaps _ hy i hai, add_zero, col_eq]
    exact hn.2.1 a i hai
  · intro i j hj1 hj2 hi
    have hy : m *ᵥ bvec j - bvec j ∈ lowS k r r := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hm.2.2 l j hj1 hj2 hl]
      simp [bvec, Pi.single_apply]
    have hmaps := maps_low hn.2.1 (a := r) le_rfl
    have hcol : (n * m) *ᵥ bvec j = n *ᵥ bvec j + n *ᵥ (m *ᵥ bvec j - bvec j) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
      congr 1
      abel
    have e := congrFun hcol i
    rw [col_eq] at e
    simp only [Pi.add_apply] at e
    rw [e, hmaps _ hy i hi, add_zero, col_eq]
    exact hn.2.2 i j hj1 hj2 hi

end Grp

end PI.MirrorSection₂
