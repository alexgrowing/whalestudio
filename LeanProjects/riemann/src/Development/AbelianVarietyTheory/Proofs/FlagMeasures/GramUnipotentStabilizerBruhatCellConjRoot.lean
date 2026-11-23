import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical

namespace GlobalTheory.LoopV.Cell

variable {K : Type} [Field K] {N : ℕ}

theorem ptEntry_inv (bs : List (K × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) :
    ∃ f : ℕ → ℕ, ∀ i, i < (bs.map Prod.snd).sum → f i < (bs.map Prod.snd).sum ∧ f (f i) = i ∧
      ptEntry bs i (f i) ≠ 0 ∧ ∀ j, j ≠ f i → ptEntry bs i j = 0 := by
  induction bs with
  | nil => exact ⟨id, fun i hi => by simp at hi⟩
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    have hb : t ≠ 0 ∧ 1 ≤ s := h (t, s) (by simp)
    obtain ⟨g, hg⟩ := ih (fun b hb' => h b (List.mem_cons_of_mem _ hb'))
    refine ⟨fun i => if i < s then s - 1 - i else s + g (i - s), fun i hi => ?_⟩
    simp only [List.map_cons, List.sum_cons] at hi ⊢
    by_cases his : i < s
    · have e1 : (if i < s then s - 1 - i else s + g (i - s)) = s - 1 - i := if_pos his
      have e2 : (if s - 1 - i < s then s - 1 - (s - 1 - i) else s + g (s - 1 - i - s)) = i := by
        rw [if_pos (show s - 1 - i < s by omega)]; omega
      rw [e1, e2]
      refine ⟨by omega, rfl, ?_, fun j hj => ?_⟩
      · simp only [ptEntry]
        rw [if_pos (show i < s ∧ s - 1 - i < s by omega), if_pos (show i + (s - 1 - i) + 1 = s by omega)]
        exact hb.1
      · simp only [ptEntry]
        by_cases hjs : j < s
        · rw [if_pos (show i < s ∧ j < s from ⟨his, hjs⟩), if_neg (show ¬ (i + j + 1 = s) by omega)]
        · rw [if_neg (show ¬ (i < s ∧ j < s) by omega), if_neg (show ¬ (s ≤ i ∧ s ≤ j) by omega)]
    · have hi' : i - s < (bs.map Prod.snd).sum := by omega
      obtain ⟨h1, h2, h3, h4⟩ := hg (i - s) hi'
      have e1 : (if i < s then s - 1 - i else s + g (i - s)) = s + g (i - s) := if_neg his
      have e2 : (if s + g (i - s) < s then s - 1 - (s + g (i - s)) else s + g (s + g (i - s) - s)) = i := by
        rw [if_neg (show ¬ (s + g (i - s) < s) by omega), Nat.add_sub_cancel_left, h2]; omega
      rw [e1, e2]
      refine ⟨by omega, rfl, ?_, fun j hj => ?_⟩
      · simp only [ptEntry]
        rw [if_neg (show ¬ (i < s ∧ s + g (i - s) < s) by omega),
          if_pos (show s ≤ i ∧ s ≤ s + g (i - s) by omega), Nat.add_sub_cancel_left]
        exact h3
      · simp only [ptEntry]
        by_cases hjs : j < s
        · rw [if_neg (show ¬ (i < s ∧ j < s) by omega), if_neg (show ¬ (s ≤ i ∧ s ≤ j) by omega)]
        · rw [if_neg (show ¬ (i < s ∧ j < s) by omega), if_pos (show s ≤ i ∧ s ≤ j by omega)]
          exact h4 (j - s) (by omega)

theorem ptMat_monomial (p : Point K N) :
    ∃ (σ : Equiv.Perm (Fin N)) (d : Fin N → K), (∀ i, d i ≠ 0) ∧
      ∀ i j, ptMat p i j = if j = σ i then d i else 0 := by
  obtain ⟨f, hf⟩ := ptEntry_inv p.1 p.2.1
  have hf' : ∀ i : Fin N, f i < N ∧ f (f i) = i ∧ ptEntry p.1 i (f i) ≠ 0 ∧
      ∀ j, j ≠ f i → ptEntry p.1 i j = 0 := by
    intro i
    have := hf i (by rw [p.2.2]; exact i.2)
    rw [p.2.2] at this
    exact this
  let σ : Equiv.Perm (Fin N) :=
    { toFun := fun i => ⟨f i, (hf' i).1⟩
      invFun := fun i => ⟨f i, (hf' i).1⟩
      left_inv := fun i => Fin.ext (hf' i).2.1
      right_inv := fun i => Fin.ext (hf' i).2.1 }
  refine ⟨σ, fun i => ptEntry p.1 i (f i), fun i => (hf' i).2.2.1, fun i j => ?_⟩
  show ptEntry p.1 i j = _
  split_ifs with hj
  · subst hj; rfl
  · exact (hf' i).2.2.2 j (fun h' => hj (Fin.ext h'))

section mono
variable {w : Matrix (Fin N) (Fin N) K} {σ : Equiv.Perm (Fin N)} {d : Fin N → K}

theorem mono_mul_inv (hd : ∀ i, d i ≠ 0) (hw : ∀ i j, w i j = if j = σ i then d i else 0) :
    w * (Matrix.of fun k j => if k = σ j then (d j)⁻¹ else 0) = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ i)]
  · rw [hw, if_pos rfl, Matrix.of_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl, mul_inv_cancel₀ (hd i)]
    · rw [if_neg (fun h => hij (σ.injective h)), if_neg hij, mul_zero]
  · intro k _ hk; rw [hw, if_neg hk, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mono_conj (hd : ∀ i, d i ≠ 0) (hw : ∀ i j, w i j = if j = σ i then d i else 0)
    (x : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    (w * x * w⁻¹) i j = d i * x (σ i) (σ j) * (d j)⁻¹ := by
  rw [Matrix.inv_eq_right_inv (mono_mul_inv hd hw), Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (σ i)]
    · rw [hw, if_pos rfl, Matrix.of_apply, if_pos rfl]
    · intro k _ hk; rw [hw, if_neg hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro k _ hk; rw [Matrix.of_apply, if_neg hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mono_roots (hd : ∀ i, d i ≠ 0) (hw : ∀ i j, w i j = if j = σ i then d i else 0)
    (i j : Fin N) : (i, j) ∈ roots w ↔ i < j ∧ σ.symm j < σ.symm i := by
  have key : ∀ a k, w a k ≠ 0 ↔ a = σ.symm k := by
    intro a k
    rw [hw]
    constructor
    · intro h
      split_ifs at h with hk
      · rw [hk, Equiv.symm_apply_apply]
      · exact absurd rfl h
    · rintro rfl
      rw [if_pos (Equiv.apply_symm_apply σ k).symm]
      exact hd _
  simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, a, b, hb, ha, hb'⟩
    rw [key] at ha hb'
    subst ha; subst hb'
    exact ⟨h1, hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, σ.symm i, σ.symm j, h2, (key _ _).2 rfl, (key _ _).2 rfl⟩
end mono

theorem mem_lieU_iff_inv {Z : Matrix (Fin N) (Fin N) K} (hZ : IsUnit Z.det)
    (x : Matrix (Fin N) (Fin N) K) : x ∈ lieU Z ↔ StrUp x ∧ StrLo (Z * x * Z⁻¹) := by
  have hc : Ring.inverse Z.det ≠ 0 := by
    rw [Ring.inverse_eq_inv]; exact inv_ne_zero hZ.ne_zero
  have e : Z * x * Z⁻¹ = Ring.inverse Z.det • (Z * x * Z.adjugate) := by
    rw [Matrix.inv_def, Matrix.mul_smul]
  simp only [lieU, Set.mem_ofPred_eq, e, StrLo, Matrix.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or]

theorem isUpUni_iff_sub (a : Matrix (Fin N) (Fin N) K) : IsUpUni a ↔ StrUp (a - 1) := by
  simp only [IsUpUni, StrUp, Matrix.sub_apply, Matrix.one_apply]
  constructor
  · intro h i j hji
    rcases hji.lt_or_eq with hlt | heq
    · rw [(h i j).1 hlt, if_neg hlt.ne', sub_zero]
    · subst heq; rw [(h j j).2 rfl, if_pos rfl, sub_self]
  · intro h i j
    refine ⟨fun hlt => ?_, fun hij => ?_⟩
    · have := h i j hlt.le
      rwa [if_neg hlt.ne', sub_zero] at this
    · subst hij
      have := h i i le_rfl
      rwa [if_pos rfl, sub_eq_zero] at this

theorem isLoUni_iff_sub (a : Matrix (Fin N) (Fin N) K) : IsLoUni a ↔ StrLo (a - 1) := by
  simp only [IsLoUni, StrLo, Matrix.sub_apply, Matrix.one_apply]
  constructor
  · intro h i j hij
    rcases hij.lt_or_eq with hlt | heq
    · rw [(h i j).1 hlt, if_neg hlt.ne, sub_zero]
    · subst heq; rw [(h i i).2 rfl, if_pos rfl, sub_self]
  · intro h i j
    refine ⟨fun hlt => ?_, fun hij => ?_⟩
    · have := h i j hlt.le
      rwa [if_neg hlt.ne, sub_zero] at this
    · subst hij
      have := h i i le_rfl
      rwa [if_pos rfl, sub_eq_zero] at this

theorem conj_sub_one {Z : Matrix (Fin N) (Fin N) K} (hZ : IsUnit Z.det)
    (a : Matrix (Fin N) (Fin N) K) : Z * (a - 1) * Z⁻¹ = Z * a * Z⁻¹ - 1 := by
  rw [mul_sub, mul_one, sub_mul, Matrix.mul_nonsing_inv _ hZ]

theorem mem_stabU_iff_sub {Z : Matrix (Fin N) (Fin N) K} (hZ : IsUnit Z.det)
    (a : Matrix (Fin N) (Fin N) K) : a ∈ stabU Z ↔ a - 1 ∈ lieU Z := by
  simp only [stabU, Set.mem_ofPred_eq]
  rw [mem_lieU_iff_inv hZ, conj_sub_one hZ, ← isUpUni_iff_sub, ← isLoUni_iff_sub]

private theorem strUp_mul_of_blockTriangular {A x : Matrix (Fin N) (Fin N) K} (hA : A.BlockTriangular id)
    (hx : StrUp x) : StrUp (A * x) := by
  intro i j hji
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l i with h | h
  · rw [hA h, zero_mul]
  · rw [hx l j (hji.trans h), mul_zero]

private theorem strUp_mul_blockTriangular {B x : Matrix (Fin N) (Fin N) K} (hB : B.BlockTriangular id)
    (hx : StrUp x) : StrUp (x * B) := by
  intro i j hji
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge j k with h | h
  · rw [hB h, mul_zero]
  · rw [hx i k (h.trans hji), zero_mul]

theorem strUp_mul {A B x : Matrix (Fin N) (Fin N) K} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (hx : StrUp x) : StrUp (A * x * B) := strUp_mul_blockTriangular hB (strUp_mul_of_blockTriangular hA hx)

private theorem strLo_mul_of_blockTriangular_toDual {A x : Matrix (Fin N) (Fin N) K}
    (hA : A.BlockTriangular OrderDual.toDual) (hx : StrLo x) : StrLo (A * x) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge i l with h | h
  · rw [hA (OrderDual.toDual_lt_toDual.mpr h), zero_mul]
  · rw [hx l j (h.trans hij), mul_zero]

private theorem strLo_mul_blockTriangular_toDual {B x : Matrix (Fin N) (Fin N) K}
    (hB : B.BlockTriangular OrderDual.toDual) (hx : StrLo x) : StrLo (x * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k j with h | h
  · rw [hB (OrderDual.toDual_lt_toDual.mpr h), mul_zero]
  · rw [hx i k (hij.trans h), zero_mul]

theorem strLo_mul {A B x : Matrix (Fin N) (Fin N) K} (hA : A.BlockTriangular OrderDual.toDual)
    (hB : B.BlockTriangular OrderDual.toDual) (hx : StrLo x) : StrLo (A * x * B) := strLo_mul_blockTriangular_toDual hB (strLo_mul_of_blockTriangular_toDual hA hx)

theorem up_tri {U : Matrix (Fin N) (Fin N) K} (h : IsUpUni U) : U.BlockTriangular id := by
  intro i j hij
  exact (h i j).1 hij

theorem lo_tri {L : Matrix (Fin N) (Fin N) K} (h : IsLoUni L) :
    L.BlockTriangular OrderDual.toDual := by
  intro i j hij
  exact (h i j).1 (OrderDual.toDual_lt_toDual.mp hij)

theorem up_det {U : Matrix (Fin N) (Fin N) K} (h : IsUpUni U) : IsUnit U.det := by
  rw [Matrix.det_of_isUpperTriangular (up_tri h), Finset.prod_eq_one (fun i _ => (h i i).2 rfl)]
  exact isUnit_one

theorem lo_det {L : Matrix (Fin N) (Fin N) K} (h : IsLoUni L) : IsUnit L.det := by
  rw [Matrix.det_of_isLowerTriangular _ (lo_tri h), Finset.prod_eq_one (fun i _ => (h i i).2 rfl)]
  exact isUnit_one

theorem conj_cancel {Z : Matrix (Fin N) (Fin N) K} (hZ : IsUnit Z.det)
    (x : Matrix (Fin N) (Fin N) K) : Z⁻¹ * (Z * x * Z⁻¹) * Z = x := by
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZ, Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ hZ]

theorem strUp_conj {U : Matrix (Fin N) (Fin N) K} (h : IsUpUni U) (x : Matrix (Fin N) (Fin N) K) :
    StrUp (U * x * U⁻¹) ↔ StrUp x := by
  have hU := up_tri h
  have hd := up_det h
  have := Matrix.invertibleOfIsUnitDet U hd
  have hUi : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hU
  constructor
  · intro hx
    have := strUp_mul hUi hU hx
    rwa [conj_cancel hd] at this
  · intro hx
    exact strUp_mul hU hUi hx

theorem strLo_conj {L : Matrix (Fin N) (Fin N) K} (h : IsLoUni L) (x : Matrix (Fin N) (Fin N) K) :
    StrLo (L * x * L⁻¹) ↔ StrLo x := by
  have hL := lo_tri h
  have hd := lo_det h
  have := Matrix.invertibleOfIsUnitDet L hd
  have hLi : L⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular hL
  constructor
  · intro hx
    have := strLo_mul hLi hL hx
    rwa [conj_cancel hd] at this
  · intro hx
    exact strLo_mul hL hLi hx

theorem ptMat_det (p : Point K N) : IsUnit (ptMat p).det := by
  obtain ⟨σ, d, hd, hw⟩ := ptMat_monomial p
  exact Matrix.isUnit_det_of_right_inverse (mono_mul_inv hd hw)

theorem mem_lieU_cell {L U w : Matrix (Fin N) (Fin N) K} (hL : IsLoUni L) (hU : IsUpUni U)
    (hw : IsUnit w.det) (x : Matrix (Fin N) (Fin N) K) :
    x ∈ lieU (L * w * U) ↔ U * x * U⁻¹ ∈ lieU w := by
  have hZ : IsUnit (L * w * U).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact ((lo_det hL).mul hw).mul (up_det hU)
  have e : L * w * U * x * (L * w * U)⁻¹ = L * (w * (U * x * U⁻¹) * w⁻¹) * L⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  rw [mem_lieU_iff_inv hZ, mem_lieU_iff_inv hw, e, strLo_conj hL, strUp_conj hU]

theorem mem_lieU_ptMat (p : Point K N) (x : Matrix (Fin N) (Fin N) K) :
    x ∈ lieU (ptMat p) ↔ ∀ i j, (i, j) ∉ roots (ptMat p) → x i j = 0 := by
  obtain ⟨σ, d, hd, hw⟩ := ptMat_monomial p
  rw [mem_lieU_iff_inv (ptMat_det p)]
  have hc : ∀ i j, (ptMat p * x * (ptMat p)⁻¹) i j = 0 ↔ x (σ i) (σ j) = 0 := by
    intro i j
    rw [mono_conj hd hw]
    simp [hd i, hd j]
  constructor
  · rintro ⟨hu, hl⟩ a b hab
    rw [mono_roots hd hw, not_and_or, not_lt, not_lt] at hab
    rcases hab with h | h
    · exact hu a b h
    · have := (hc (σ.symm a) (σ.symm b)).1 (hl _ _ h)
      simpa using this
  · intro h
    refine ⟨fun a b hab => h a b ?_, fun i j hij => (hc i j).2 (h _ _ ?_)⟩
    · rw [mono_roots hd hw]
      exact fun hr => absurd hr.1 (not_lt.2 hab)
    · rw [mono_roots hd hw]
      intro hr
      have h2 := hr.2
      simp only [Equiv.symm_apply_apply] at h2
      exact absurd h2 (not_lt.2 hij)

theorem stab_cell : ∀ (K : Type) [Field K] (N : ℕ) (L U : Matrix (Fin N) (Fin N) K) (p : Point K N), IsLoUni L → IsUpUni U → (∀ a, a ∈ stabU (L * ptMat p * U) ↔ U * a * U⁻¹ ∈ stabU (ptMat p)) ∧ (∀ x, x ∈ lieU (L * ptMat p * U) ↔ U * x * U⁻¹ ∈ lieU (ptMat p)) ∧ (∀ a, a ∈ stabU (ptMat p) ↔ IsUpUni a ∧ ∀ i j, i < j → (i, j) ∉ roots (ptMat p) → a i j = 0) ∧ (∀ x, x ∈ lieU (ptMat p) ↔ ∀ i j, (i, j) ∉ roots (ptMat p) → x i j = 0) := by
  intro K _ N L U p hL hU
  have hw := ptMat_det p
  have dU := up_det hU
  have hZ : IsUnit (L * ptMat p * U).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact ((lo_det hL).mul hw).mul dU
  obtain ⟨σ, d, hd, hm⟩ := ptMat_monomial p
  have hroot : ∀ i j, (i, j) ∈ roots (ptMat p) → i < j := fun i j hr => ((mono_roots hd hm i j).1 hr).1
  refine ⟨fun a => ?_, fun x => mem_lieU_cell hL hU hw x, fun a => ?_, fun x => mem_lieU_ptMat p x⟩
  · rw [mem_stabU_iff_sub hZ, mem_lieU_cell hL hU hw, mem_stabU_iff_sub hw, conj_sub_one dU]
  · rw [mem_stabU_iff_sub hw, mem_lieU_ptMat, isUpUni_iff_sub]
    constructor
    · intro h
      refine ⟨fun i j hji => h i j fun hr => absurd (hroot i j hr) (not_lt.2 hji), fun i j hij hr => ?_⟩
      have := h i j hr
      rwa [Matrix.sub_apply, Matrix.one_apply, if_neg hij.ne, sub_zero] at this
    · rintro ⟨hu, hr⟩ i j hn
      rcases lt_or_ge i j with hij | hji
      · rw [Matrix.sub_apply, Matrix.one_apply, if_neg hij.ne, sub_zero]
        exact hr i j hij hn
      · exact hu i j hji

end GlobalTheory.LoopV.Cell
