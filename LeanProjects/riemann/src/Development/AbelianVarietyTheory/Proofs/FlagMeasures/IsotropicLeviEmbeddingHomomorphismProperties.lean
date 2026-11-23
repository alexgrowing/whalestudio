import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.UEmb

def mI (k r : ℕ) (m : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + m.val, by omega⟩

theorem idx_cases {k r : ℕ} (i : Fin (2 * r + k + 1)) :
    (∃ a, i = eI k r a) ∨ (∃ m, i = mI k r m) ∨ ∃ a, i = esI k r a := by
  obtain ⟨i, hi⟩ := i
  by_cases h1 : i < r
  · exact Or.inl ⟨⟨i, h1⟩, rfl⟩
  by_cases h2 : i ≤ r + k
  · exact Or.inr (Or.inl ⟨⟨i - r, by omega⟩, Fin.ext (show i = r + (i - r) by omega)⟩)
  · exact Or.inr (Or.inr ⟨⟨2 * r + k - i, by omega⟩, Fin.ext (show i = 2 * r + k - (2 * r + k - i) by omega)⟩)

theorem sum_idx {k r : ℕ} (f : Fin (2 * r + k + 1) → ℂ) :
    ∑ i, f i = ∑ a, f (eI k r a) + (∑ m, f (mI k r m) + ∑ a, f (esI k r a)) := by
  have ve : ∀ z : Fin r, (eI k r z).val = z.val := fun _ => rfl
  have vm : ∀ z : Fin (k + 1), (mI k r z).val = r + z.val := fun _ => rfl
  have vs : ∀ z : Fin r, (esI k r z).val = 2 * r + k - z.val := fun _ => rfl
  have hb : Function.Bijective (Sum.elim (eI k r) (Sum.elim (mI k r) (esI k r))) := by
    constructor
    · intro x y h
      have h' := congrArg Fin.val h
      rcases x with x | x | x <;> rcases y with y | y | y <;> have hx := x.2 <;> have hy := y.2 <;>
        simp only [Sum.elim_inl, Sum.elim_inr, ve, vm, vs, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
          Fin.ext_iff] at h' ⊢ <;> omega
    · intro i
      rcases idx_cases i with ⟨a, rfl⟩ | ⟨m, rfl⟩ | ⟨a, rfl⟩
      · exact ⟨Sum.inl a, rfl⟩
      · exact ⟨Sum.inr (Sum.inl m), rfl⟩
      · exact ⟨Sum.inr (Sum.inr a), rfl⟩
  rw [← Fintype.sum_bijective _ hb (fun x => f (Sum.elim (eI k r) (Sum.elim (mI k r) (esI k r)) x)) f
    (fun _ => rfl)]
  simp [Fintype.sum_sum_type]

variable {k r : ℕ} (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) (m n : Fin (k + 1))

theorem u_ee : uEmb k r u (eI k r a) (eI k r b) = u a b := by
  have h : (eI k r a).val < r ∧ (eI k r b).val < r := ⟨a.2, b.2⟩
  simp only [uEmb, dif_pos h]
  rfl
theorem u_em : uEmb k r u (eI k r a) (mI k r n) = 0 := by
  have ha := a.2
  have va : (eI k r a).val = a.val := rfl
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  have hn := n.2
  have vn : (mI k r n).val = r + n.val := rfl
  simp only [uEmb]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega
theorem u_es : uEmb k r u (eI k r a) (esI k r b) = 0 := by
  have ha := a.2
  have va : (eI k r a).val = a.val := rfl
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  have hb := b.2
  have vb : (eI k r b).val = b.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  simp only [uEmb]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega
theorem u_me : uEmb k r u (mI k r m) (eI k r b) = 0 := by
  have hm := m.2
  have vm : (mI k r m).val = r + m.val := rfl
  have hb := b.2
  have vb : (eI k r b).val = b.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  simp only [uEmb]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega
theorem u_mm : uEmb k r u (mI k r m) (mI k r n) = if m = n then 1 else 0 := by
  have hm := m.2
  have vm : (mI k r m).val = r + m.val := rfl
  have hn := n.2
  have vn : (mI k r n).val = r + n.val := rfl
  simp only [uEmb]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega
theorem u_ms : uEmb k r u (mI k r m) (esI k r b) = 0 := by
  have hm := m.2
  have vm : (mI k r m).val = r + m.val := rfl
  have hb := b.2
  have vb : (eI k r b).val = b.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  simp only [uEmb]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega
theorem u_se : uEmb k r u (esI k r a) (eI k r b) = 0 := by
  have ha := a.2
  have va : (eI k r a).val = a.val := rfl
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  have hb := b.2
  have vb : (eI k r b).val = b.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  simp only [uEmb]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega
theorem u_sm : uEmb k r u (esI k r a) (mI k r n) = 0 := by
  have ha := a.2
  have va : (eI k r a).val = a.val := rfl
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  have hn := n.2
  have vn : (mI k r n).val = r + n.val := rfl
  simp only [uEmb]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega
theorem u_ss : uEmb k r u (esI k r a) (esI k r b) = star (u⁻¹ b a) := by
  have ha := a.2
  have va : (eI k r a).val = a.val := rfl
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  have hb := b.2
  have vb : (eI k r b).val = b.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  have h1 : ¬ ((esI k r a).val < r ∧ (esI k r b).val < r) := by rw [vsa, vsb]; omega
  have h2 : r + k < (esI k r a).val ∧ r + k < (esI k r b).val := by rw [vsa, vsb]; omega
  have e1 : 2 * r + k - (esI k r b).val = b.val := by rw [vsb]; omega
  have e2 : 2 * r + k - (esI k r a).val = a.val := by rw [vsa]; omega
  simp only [uEmb, dif_neg h1, dif_pos h2]
  congr 1
  exact congrArg₂ (fun x y => u⁻¹ x y) (Fin.ext e1) (Fin.ext e2)

theorem h_ee : Hpk k r (eI k r a) (eI k r b) = 0 := by
  have ha := a.2
  have hb := b.2
  have va : (eI k r a).val = a.val := rfl
  have vb : (eI k r b).val = b.val := rfl
  simp only [Hpk, Fin.ext_iff, va, vb]
  split_ifs <;> first | rfl | omega
theorem h_em : Hpk k r (eI k r a) (mI k r n) = 0 := by
  have ha := a.2
  have hn := n.2
  have va : (eI k r a).val = a.val := rfl
  have vn : (mI k r n).val = r + n.val := rfl
  simp only [Hpk, Fin.ext_iff, va, vn]
  split_ifs <;> first | rfl | omega
theorem h_es : Hpk k r (eI k r a) (esI k r b) = if a = b then 1 else 0 := by
  have ha := a.2
  have hb := b.2
  have va : (eI k r a).val = a.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  simp only [Hpk, Fin.ext_iff, va, vsb]
  split_ifs <;> first | rfl | omega
theorem h_me : Hpk k r (mI k r m) (eI k r b) = 0 := by
  have hm := m.2
  have hb := b.2
  have vm : (mI k r m).val = r + m.val := rfl
  have vb : (eI k r b).val = b.val := rfl
  simp only [Hpk, Fin.ext_iff, vm, vb]
  split_ifs <;> first | rfl | omega
theorem h_ms : Hpk k r (mI k r m) (esI k r b) = 0 := by
  have hm := m.2
  have hb := b.2
  have vm : (mI k r m).val = r + m.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  simp only [Hpk, Fin.ext_iff, vm, vsb]
  split_ifs <;> first | rfl | omega
theorem h_se : Hpk k r (esI k r a) (eI k r b) = if a = b then 1 else 0 := by
  have ha := a.2
  have hb := b.2
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  have vb : (eI k r b).val = b.val := rfl
  simp only [Hpk, Fin.ext_iff, vsa, vb]
  split_ifs <;> first | rfl | omega
theorem h_sm : Hpk k r (esI k r a) (mI k r n) = 0 := by
  have ha := a.2
  have hn := n.2
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  have vn : (mI k r n).val = r + n.val := rfl
  simp only [Hpk, Fin.ext_iff, vsa, vn]
  split_ifs <;> first | rfl | omega
theorem h_ss : Hpk k r (esI k r a) (esI k r b) = 0 := by
  have ha := a.2
  have hb := b.2
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  simp only [Hpk, Fin.ext_iff, vsa, vsb]
  split_ifs <;> first | rfl | omega

theorem eI_inj : eI k r a = eI k r b ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    exact Fin.ext h'
  · intro h
    rw [h]
theorem mI_inj : mI k r m = mI k r n ↔ m = n := by
  constructor
  · intro h
    have h' : r + m.val = r + n.val := congrArg Fin.val h
    exact Fin.ext (by omega)
  · intro h
    rw [h]
theorem esI_inj : esI k r a = esI k r b ↔ a = b := by
  have ha := a.2
  have va : (eI k r a).val = a.val := rfl
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  have hb := b.2
  have vb : (eI k r b).val = b.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  constructor
  · intro h
    have h' := congrArg Fin.val h
    rw [vsa, vsb] at h'
    exact Fin.ext (by omega)
  · intro h
    rw [h]
theorem eI_ne_mI : eI k r a ≠ mI k r m := by
  have ha := a.2
  have va : (eI k r a).val = a.val := rfl
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  have hm := m.2
  have vm : (mI k r m).val = r + m.val := rfl
  intro h
  have h' := congrArg Fin.val h
  rw [va, vm] at h'
  omega
theorem eI_ne_esI : eI k r a ≠ esI k r b := by
  have ha := a.2
  have va : (eI k r a).val = a.val := rfl
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  have hb := b.2
  have vb : (eI k r b).val = b.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  intro h
  have h' := congrArg Fin.val h
  rw [va, vsb] at h'
  omega
theorem mI_ne_esI : mI k r m ≠ esI k r b := by
  have hm := m.2
  have vm : (mI k r m).val = r + m.val := rfl
  have hb := b.2
  have vb : (eI k r b).val = b.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  intro h
  have h' := congrArg Fin.val h
  rw [vm, vsb] at h'
  omega
theorem mI_ne_eI : mI k r m ≠ eI k r a := by
  have hm := m.2
  have vm : (mI k r m).val = r + m.val := rfl
  have ha := a.2
  have va : (eI k r a).val = a.val := rfl
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  intro h
  have h' := congrArg Fin.val h
  rw [vm, va] at h'
  omega
theorem esI_ne_eI : esI k r b ≠ eI k r a := by
  have hb := b.2
  have vb : (eI k r b).val = b.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  have ha := a.2
  have va : (eI k r a).val = a.val := rfl
  have vsa : (esI k r a).val = 2 * r + k - a.val := rfl
  intro h
  have h' := congrArg Fin.val h
  rw [vsb, va] at h'
  omega
theorem esI_ne_mI : esI k r b ≠ mI k r m := by
  have hb := b.2
  have vb : (eI k r b).val = b.val := rfl
  have vsb : (esI k r b).val = 2 * r + k - b.val := rfl
  have hm := m.2
  have vm : (mI k r m).val = r + m.val := rfl
  intro h
  have h' := congrArg Fin.val h
  rw [vsb, vm] at h'
  omega

theorem uEmb_mul (u u' : Matrix (Fin r) (Fin r) ℂ) : uEmb k r (u * u') = uEmb k r u * uEmb k r u' := by
  ext i j
  rw [Matrix.mul_apply, sum_idx]
  rcases idx_cases i with ⟨a, rfl⟩ | ⟨m, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases idx_cases j with ⟨b, rfl⟩ | ⟨n, rfl⟩ | ⟨b, rfl⟩ <;>
    simp [u_ee, u_em, u_es, u_me, u_mm, u_ms, u_se, u_sm, u_ss, Matrix.mul_apply, Matrix.mul_inv_rev, star_sum] <;>
    simp [mul_comm]

theorem uEmb_one : uEmb k r 1 = 1 := by
  ext i j
  rcases idx_cases i with ⟨a, rfl⟩ | ⟨m, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases idx_cases j with ⟨b, rfl⟩ | ⟨n, rfl⟩ | ⟨b, rfl⟩ <;>
    simp [u_ee, u_em, u_es, u_me, u_mm, u_ms, u_se, u_sm, u_ss, eI_inj, mI_inj, esI_inj, eI_ne_mI, eI_ne_esI, esI_ne_mI, Matrix.one_apply,
      apply_ite (star : ℂ → ℂ), eq_comm]

theorem uEmb_mem (hu : IsUnit u.det) : uEmb k r u ∈ GG k r := by
  have hc : ∀ a b : Fin r, ∑ c, u⁻¹ b c * u c a = if b = a then 1 else 0 := fun a b => by
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul u hu, Matrix.one_apply]
  have hc' : ∀ a b : Fin r, ∑ c, (starRingEnd ℂ) (u c a) * (starRingEnd ℂ) (u⁻¹ b c) =
      if a = b then 1 else 0 := fun a b => by
    have h : ∑ c, (starRingEnd ℂ) (u c a) * (starRingEnd ℂ) (u⁻¹ b c) =
        (starRingEnd ℂ) (∑ c, u⁻¹ b c * u c a) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [map_mul, mul_comm]
    rw [h, hc]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, Ne.symm hab]
  show (uEmb k r u)ᴴ * Hpk k r * uEmb k r u = Hpk k r
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, sum_idx]
  rcases idx_cases i with ⟨a, rfl⟩ | ⟨m, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases idx_cases j with ⟨b, rfl⟩ | ⟨n, rfl⟩ | ⟨b, rfl⟩ <;>
    simp [u_ee, u_em, u_es, u_me, u_mm, u_ms, u_se, u_sm, u_ss, h_ee, h_em, h_es, h_me, h_ms, h_se, h_sm, h_ss, hc, hc',
      apply_ite (star : ℂ → ℂ)]

theorem uEmb_inv (hu : IsUnit u.det) : (uEmb k r u)⁻¹ = uEmb k r u⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [← uEmb_mul, Matrix.nonsing_inv_mul u hu, uEmb_one]

theorem uEmb_eI : uEmb k r u *ᵥ bvec (eI k r b) = ∑ a, u a b • bvec (eI k r a) := by
  ext i
  rcases idx_cases i with ⟨c, rfl⟩ | ⟨p, rfl⟩ | ⟨c, rfl⟩ <;>
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply, u_ee, u_em, u_es, u_me, u_mm, u_ms, u_se, u_sm, u_ss, eI_inj, mI_inj, esI_inj, eI_ne_mI, eI_ne_esI, mI_ne_esI, mI_ne_eI, esI_ne_eI, esI_ne_mI]

theorem uEmb_esI : uEmb k r u *ᵥ bvec (esI k r b) = ∑ a, star (u⁻¹ b a) • bvec (esI k r a) := by
  ext i
  rcases idx_cases i with ⟨c, rfl⟩ | ⟨p, rfl⟩ | ⟨c, rfl⟩ <;>
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply, u_ee, u_em, u_es, u_me, u_mm, u_ms, u_se, u_sm, u_ss, eI_inj, mI_inj, esI_inj, eI_ne_mI, eI_ne_esI, mI_ne_esI, mI_ne_eI, esI_ne_eI, esI_ne_mI]

theorem uEmb_mid (w : Fin (2 * r + k + 1) → ℂ) (hw : inWb k r w) : uEmb k r u *ᵥ w = w := by
  have he : ∀ c, w (eI k r c) = 0 := fun c => hw _ (Or.inl (by simp [eI]))
  have hs : ∀ c, w (esI k r c) = 0 := fun c => hw _ (Or.inr (by have := c.2; simp [esI]; omega))
  ext i
  show ∑ j, uEmb k r u i j * w j = w i
  rw [sum_idx]
  rcases idx_cases i with ⟨c, rfl⟩ | ⟨p, rfl⟩ | ⟨c, rfl⟩ <;>
    simp [he, hs, u_ee, u_em, u_es, u_me, u_mm, u_ms, u_se, u_sm, u_ss]

theorem det_upper (x : UT r → ℂ) : (upper x).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [upper]
  · intro a b hab
    have h' : b < a := hab
    simp [upper, not_lt.mpr h'.le, h'.ne']

theorem upper_mem (x : UT r → ℂ) : uEmb k r (upper x) ∈ Nset k r := by
  refine ⟨uEmb_mem (upper x) (by rw [det_upper]; exact isUnit_one), ?_, ?_⟩
  · intro a i hai
    rcases idx_cases i with ⟨c, rfl⟩ | ⟨p, rfl⟩ | ⟨c, rfl⟩
    · have hai' : a.val ≤ c.val := hai
      have hac : ¬ c < a := fun h => by rw [Fin.lt_iff_val_lt_val] at h; omega
      simp [u_ee, upper, hac, eI_inj]
    · simp [u_me, mI_ne_eI]
    · simp [u_se, esI_ne_eI]
  · intro i j hj1 hj2 hi
    rcases idx_cases j with ⟨b, rfl⟩ | ⟨n, rfl⟩ | ⟨b, rfl⟩
    · have hb := b.2
      have h' : r ≤ b.val := hj1
      omega
    · rcases idx_cases i with ⟨a, rfl⟩ | ⟨m, rfl⟩ | ⟨a, rfl⟩
      · have ha := a.2
        have h' : r ≤ a.val := hi
        omega
      · simp [u_mm, mI_inj]
      · simp [u_sm, esI_ne_mI]
    · have hb := b.2
      have h' : 2 * r + k - b.val ≤ r + k := hj2
      omega

theorem uEmb_hom : ∀ k r : ℕ, (∀ u u' : Matrix (Fin r) (Fin r) ℂ, IsUnit u.det → IsUnit u'.det → uEmb k r (u * u') = uEmb k r u * uEmb k r u') ∧ uEmb k r 1 = 1 ∧ (∀ u : Matrix (Fin r) (Fin r) ℂ, IsUnit u.det → uEmb k r u ∈ GG k r ∧ (uEmb k r u)⁻¹ = uEmb k r u⁻¹ ∧ (∀ b : Fin r, uEmb k r u *ᵥ bvec (eI k r b) = ∑ a, u a b • bvec (eI k r a)) ∧ (∀ b : Fin r, uEmb k r u *ᵥ bvec (esI k r b) = ∑ a, star (u⁻¹ b a) • bvec (esI k r a)) ∧ ∀ w, inWb k r w → uEmb k r u *ᵥ w = w) ∧ (∀ x : UT r → ℂ, (upper x).det = 1 ∧ uEmb k r (upper x) ∈ Nset k r) := by
  intro k r
  refine ⟨fun u u' _ _ => uEmb_mul u u', uEmb_one, fun u hu => ⟨uEmb_mem u hu, uEmb_inv u hu,
    fun b => uEmb_eI u b, fun b => uEmb_esI u b, fun w hw => uEmb_mid u w hw⟩,
    fun x => ⟨det_upper x, upper_mem x⟩⟩

end GlobalTheory.Amp.UEmb
