import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter

open Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.Forms (blkOf entN InJ blkMat)

theorem glm_blkIdx {t : ℕ} (ht : 0 < t) (j x : ℕ) : blkIdx (List.replicate j t) x = min (x / t) j := by
  induction j generalizing x with
  | zero => simp [blkIdx]
  | succ j ih =>
    simp only [List.replicate_succ, blkIdx]
    split_ifs with h
    · rw [Nat.div_eq_of_lt h]; omega
    · have hx : x / t = (x - t) / t + 1 := Nat.div_eq_sub_div ht (by omega)
      rw [ih, hx]; omega

theorem glm_fine {a t j x : ℕ} (ht : 0 < t) (hx : x ≤ a + j * t) : fine a (List.replicate j t) x = blkOf a t x := by
  simp only [fine, blkOf]
  split_ifs with h
  · rfl
  · rw [glm_blkIdx ht, min_eq_left]
    exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; omega)

section Grp

variable {κ k' : Type} [CommRing κ] [Field k'] {n : ℕ}

theorem glm_mem_uniUT {a t j : ℕ} (ht : 0 < t) (hn : n ≤ a + j * t + 1) (M : GL (Fin n) κ) :
    M ∈ uniUT n κ a (List.replicate j t) ↔
      (∀ x y : Fin n, blkOf a t y < blkOf a t x → (M : Matrix (Fin n) (Fin n) κ) x y = 0) ∧
      ∀ x : Fin n, (x : ℕ) < a → (M : Matrix (Fin n) (Fin n) κ) x x = 1 := by
  have hf : ∀ x : Fin n, fine a (List.replicate j t) x = blkOf a t x :=
    fun x => glm_fine ht (by have := x.isLt; omega)
  show (M ∈ btG n κ (fine a (List.replicate j t)) ∧
      ∀ i : Fin n, i.val < a → (M : Matrix (Fin n) (Fin n) κ) i i = 1) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x y hxy => h1 (by simp only [hf]; exact hxy), h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    intro x y hxy
    exact h1 x y (by simpa only [hf] using hxy)

theorem glm_mem_fixCol (c : ℕ) (M : GL (Fin n) κ) :
    M ∈ fixCol n κ c ↔ ∀ x y : Fin n, (y : ℕ) = c → (M : Matrix (Fin n) (Fin n) κ) x y = if x = y then 1 else 0 := by
  constructor
  · intro h x y hy
    rw [← Matrix.one_apply]
    exact h x y hy
  · intro h x y hy
    rw [Matrix.one_apply]
    exact h x y hy

def glmInJ (a t fc : ℕ) (zl : Bool) (M : Matrix (Fin n) (Fin n) κ) : Prop :=
  (∀ x y : Fin n, blkOf a t y < blkOf a t x → M x y = 0) ∧ (∀ x : Fin n, (x : ℕ) < a → M x x = 1) ∧
  (∀ x y : Fin n, (y : ℕ) = fc → M x y = if x = y then 1 else 0) ∧
  (zl = true → ∀ x y : Fin n, (y : ℕ) + 1 = n →
    M x y = (if x = y then 1 else 0) ∧ M y x = (if x = y then 1 else 0))

theorem glm_InJ_map (e : κ ≃+* k') (a t fc : ℕ) (zl : Bool) (M : Matrix (Fin n) (Fin n) κ) :
    InJ a t fc zl (M.map e) ↔ glmInJ a t fc zl M := by
  unfold InJ glmInJ
  simp only [Matrix.map_apply]
  have h0 : ∀ z : κ, e z = 0 ↔ z = 0 := fun z => map_eq_zero_iff e e.injective
  have h1 : ∀ z : κ, e z = 1 ↔ z = 1 := fun z => by rw [← map_one e, e.injective.eq_iff]
  have hd : ∀ (x y : Fin n) (z : κ), e z = (if x = y then 1 else 0) ↔ z = (if x = y then 1 else 0) := by
    intro x y z
    split_ifs
    exacts [h1 z, h0 z]
  simp only [h0, h1, hd]

theorem glm_InJ_false {a t j : ℕ} (ht : 0 < t) (hn : n ≤ a + j * t + 1) (fc : ℕ) (M : GL (Fin n) κ) :
    glmInJ a t fc false (M : Matrix (Fin n) (Fin n) κ) ↔ M ∈ uniUT n κ a (List.replicate j t) ⊓ fixCol n κ fc := by
  rw [Subgroup.mem_inf, glm_mem_uniUT ht hn, glm_mem_fixCol]
  unfold glmInJ
  constructor
  · rintro ⟨h1, h2, h3, -⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3, fun h => by cases h⟩

theorem glm_fixCol_top {c : ℕ} (hc : n ≤ c) : fixCol n κ c = ⊤ := by
  rw [eq_top_iff]
  intro M _
  rw [glm_mem_fixCol]
  intro x y hy
  exfalso
  have := y.isLt
  omega

theorem glm_InJ_true {a t j : ℕ} (ht : 0 < t) (hn : n = a + j * t + 1) (fc : ℕ) (M : GL (Fin n) κ) :
    glmInJ a t fc true (M : Matrix (Fin n) (Fin n) κ) ↔
      M ∈ (uniUT n κ a (List.replicate j t) ⊓ fixCol n κ (a + j * t)) ⊓ fixCol n κ fc := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, glm_mem_uniUT ht (le_of_eq hn), glm_mem_fixCol, glm_mem_fixCol]
  unfold glmInJ
  have hblk : ∀ x y : Fin n, (y : ℕ) = a + j * t → x ≠ y → blkOf a t x < blkOf a t y := by
    intro x y hy hxy
    have hxl := x.isLt
    have hne : (x : ℕ) ≠ y := fun h => hxy (Fin.ext h)
    have hx : (x : ℕ) < a + j * t := by omega
    have hyb : blkOf a t y = a + j := by
      unfold blkOf
      rw [if_neg (show ¬ (y : ℕ) < a by omega), show (y : ℕ) - a = j * t by omega, Nat.mul_div_cancel _ ht]
    rw [hyb]
    unfold blkOf
    split_ifs with h
    · omega
    · have h2 : ((x : ℕ) - a) / t < j := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      omega
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, fun x y hy => (h4 rfl x y (by omega)).1⟩, h3⟩
  · rintro ⟨⟨⟨h1, h2⟩, h5⟩, h3⟩
    refine ⟨h1, h2, h3, fun _ x y hy => ⟨h5 x y (by omega), ?_⟩⟩
    by_cases hxy : x = y
    · subst hxy
      exact h5 x x (by omega)
    · rw [if_neg hxy]
      exact h1 y x (hblk x y (by omega) hxy)

end Grp

section Chr

variable {κ k' K : Type} [CommRing κ] [Field k'] [Field K] {n : ℕ}

def glmPsi (e : κ ≃+* k') (σ₀ : K →+* ℂ) (ψ : AddChar κ K) : AddChar k' ℂ where
  toFun x := σ₀ (ψ (e.symm x))
  map_zero_eq_one' := by rw [map_zero, AddChar.map_zero_eq_one, map_one]
  map_add_eq_mul' x y := by rw [map_add, AddChar.map_add_eq_mul, map_mul]

theorem glmPsi_apply (e : κ ≃+* k') (σ₀ : K →+* ℂ) (ψ : AddChar κ K) (x : κ) : glmPsi e σ₀ ψ (e x) = σ₀ (ψ x) := by
  show σ₀ (ψ (e.symm (e x))) = σ₀ (ψ x)
  rw [e.symm_apply_apply]

open Classical in

def glmChi (e : κ ≃+* k') (σ₀ : K →+* ℂ) (χ : κˣ →* Kˣ) : MulChar k' ℂ :=
  MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp (χ.comp (Units.map e.symm.toRingHom.toMonoidHom)))

theorem glmChi_apply (e : κ ≃+* k') (σ₀ : K →+* ℂ) (χ : κˣ →* Kˣ) (x : κˣ) :
    glmChi e σ₀ χ (e (x : κ)) = σ₀ ((χ x : Kˣ) : K) := by
  have h : e (x : κ) = ((Units.map e.toRingHom.toMonoidHom x : k'ˣ) : k') := rfl
  rw [h]
  unfold glmChi
  rw [MulChar.ofUnitHom_coe]
  have h2 : (Units.map e.symm.toRingHom.toMonoidHom) (Units.map e.toRingHom.toMonoidHom x) = x := by
    ext
    simp
  simp only [MonoidHom.comp_apply, h2]
  rfl

def equalBlockPositionsEquiv {a t j s : ℕ} (ht : 0 < t) (hs : s < j) (hn : a + j * t ≤ n) :
    Fin t ≃ {i : Fin n // coarse a (List.replicate j t) i.val = s + 1} where
  toFun c := ⟨⟨a + s * t + c, by
      have h1 : (s + 1) * t ≤ j * t := Nat.mul_le_mul_right t hs
      have := c.2
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega⟩, by
    show coarse a (List.replicate j t) (a + s * t + c) = s + 1
    rw [coarse_of_le (by omega), glm_blkIdx ht]
    have h2 : (a + s * t + c - a) / t = s := by
      rw [show a + s * t + c - a = c + t * s by rw [Nat.mul_comm t s]; omega, Nat.add_mul_div_left _ _ ht,
        Nat.div_eq_of_lt c.2, Nat.zero_add]
    rw [h2]; omega⟩
  invFun i := ⟨i.1.val - (a + s * t), by
    have h := i.2
    have ha : a ≤ i.1.val := by
      by_contra hlt
      rw [coarse_of_lt (Nat.not_le.1 hlt)] at h
      omega
    rw [coarse_of_le ha, glm_blkIdx ht] at h
    have h3 : (i.1.val - a) / t = s := by omega
    have h4 := Nat.div_add_mod (i.1.val - a) t
    have h5 := Nat.mod_lt (i.1.val - a) ht
    rw [h3, Nat.mul_comm] at h4
    omega⟩
  left_inv c := by
    apply Fin.ext
    show a + s * t + c - (a + s * t) = c
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    show a + s * t + (i.1.val - (a + s * t)) = i.1.val
    have h := i.2
    have ha : a ≤ i.1.val := by
      by_contra hlt
      rw [coarse_of_lt (Nat.not_le.1 hlt)] at h
      omega
    rw [coarse_of_le ha, glm_blkIdx ht] at h
    have h3 : (i.1.val - a) / t = s := by omega
    have h4 := Nat.div_add_mod (i.1.val - a) t
    rw [h3, Nat.mul_comm] at h4
    omega

theorem glm_blkDet (e : κ ≃+* k') {a t j s : ℕ} (ht : 0 < t) (hs : s < j) (hn : a + j * t ≤ n)
    (M : ↥(blockUT n κ a (List.replicate j t))) :
    e ((blkDet n κ (coarse a (List.replicate j t)) (s + 1) M : κˣ) : κ) =
      (blkMat a t s ((M.1 : Matrix (Fin n) (Fin n) κ).map e)).det := by
  have hA : ((blkDet n κ (coarse a (List.replicate j t)) (s + 1) M : κˣ) : κ) =
      ((M.1 : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => coarse a (List.replicate j t) i.val) (s + 1)).det := rfl
  rw [hA, RingEquiv.map_det, RingEquiv.mapMatrix_apply]
  refine (Matrix.det_submatrix_equiv_self (equalBlockPositionsEquiv ht hs hn) _).symm.trans (congrArg Matrix.det ?_)
  ext c d
  have hc : a + s * t + (c : ℕ) < n := ((equalBlockPositionsEquiv ht hs hn) c).1.isLt
  have hd : a + s * t + (d : ℕ) < n := ((equalBlockPositionsEquiv ht hs hn) d).1.isLt
  simp only [blkMat, entN, dif_pos (And.intro hc hd)]
  rfl

theorem glm_lamGen (e : κ ≃+* k') (σ₀ : K →+* ℂ) (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {a t j skip : ℕ} (S : Finset ℕ)
    (ht : 0 < t) (hn : a + j * t ≤ n) (hS : ∀ x, x + 1 < a → (x ∈ S ↔ x + 1 ≠ skip))
    (M : ↥(uniUT n κ a (List.replicate j t))) :
    σ₀ ((lamGen ψ χ n a (List.replicate j t) S M : Kˣ) : K) =
      Formalism.L2.Forms.lamJ (glmPsi e σ₀ ψ) (fun s => glmChi e σ₀ (χ s)) a t j skip ((M.1 : Matrix (Fin n) (Fin n) κ).map e) := by
  have hsum : e (supSum a S (M.1 : Matrix (Fin n) (Fin n) κ)) =
      ∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ skip then
        ((M.1 : Matrix (Fin n) (Fin n) κ).map e) x y else 0 := by
    unfold supSum
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hc : ((x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (x : ℕ) ∈ S) ↔ ((x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ skip) := by
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, by rw [← h1]; exact (hS x (by omega)).1 h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, (hS x (by omega)).2 (by rw [h1]; exact h3)⟩
    rw [apply_ite e, map_zero, Matrix.map_apply]
    exact if_congr hc rfl rfl
  have hM : ∀ i ∈ Finset.range j, σ₀ (((χ i) (blkDet n κ (coarse a (List.replicate j t)) (i + 1)
      (Subgroup.inclusion (uniUT_le_blockUT n κ a (List.replicate j t)) M)) : Kˣ) : K) =
      glmChi e σ₀ (χ i) (Formalism.L2.Forms.blkMat a t i ((M.1 : Matrix (Fin n) (Fin n) κ).map e)).det := by
    intro i hi
    have h1 := glm_blkDet e ht (Finset.mem_range.1 hi) hn
      (Subgroup.inclusion (uniUT_le_blockUT n κ a (List.replicate j t)) M)
    have h2 := glmChi_apply e σ₀ (χ i) (blkDet n κ (coarse a (List.replicate j t)) (i + 1)
      (Subgroup.inclusion (uniUT_le_blockUT n κ a (List.replicate j t)) M))
    rw [h1] at h2
    exact h2.symm
  have hsup : ((supChar ψ n a (List.replicate j t) S M : Kˣ) : K) = ψ (supSum a S (M.1 : Matrix (Fin n) (Fin n) κ)) := rfl
  have hdet : ((detChar χ n a (List.replicate j t)
      (Subgroup.inclusion (uniUT_le_blockUT n κ a (List.replicate j t)) M) : Kˣ) : K) =
      ∏ i ∈ Finset.range j, (((χ i) (blkDet n κ (coarse a (List.replicate j t)) (i + 1)
        (Subgroup.inclusion (uniUT_le_blockUT n κ a (List.replicate j t)) M)) : Kˣ) : K) := by
    unfold detChar
    rw [MonoidHom.finset_prod_apply, Units.coe_prod, List.length_replicate]
    rfl
  have hL : ((lamGen ψ χ n a (List.replicate j t) S M : Kˣ) : K) =
      ((supChar ψ n a (List.replicate j t) S M : Kˣ) : K) *
        ((detChar χ n a (List.replicate j t)
          (Subgroup.inclusion (uniUT_le_blockUT n κ a (List.replicate j t)) M) : Kˣ) : K) := rfl
  rw [hL, hsup, hdet, map_mul, map_prod]
  unfold Formalism.L2.Forms.lamJ
  congr 1
  · rw [← glmPsi_apply e σ₀ ψ, hsum]
  · exact Finset.prod_congr rfl hM

end Chr

end Formalism.L2.Col
