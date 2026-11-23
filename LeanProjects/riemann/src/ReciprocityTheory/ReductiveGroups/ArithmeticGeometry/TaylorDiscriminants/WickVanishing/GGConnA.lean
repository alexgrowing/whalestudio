import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC

section Line

open Polynomial

theorem isPreconnected_det_ne {ι : Type*} [Fintype ι] {n : ℕ} (V : Set (ι → Matrix (Fin n) (Fin n) ℂ))
    (hV : ∀ a ∈ V, ∀ b ∈ V, ∀ z : ℂ, (1 - z) • a + z • b ∈ V) :
    IsPreconnected {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0} := by
  refine isPreconnected_of_forall_pair ?_
  rintro a ⟨haV, ha⟩ b ⟨hbV, hb⟩
  let L : ℂ → ι → Matrix (Fin n) (Fin n) ℂ := fun z => (1 - z) • a + z • b
  let p : ι → ℂ[X] := fun i =>
    (Matrix.of fun k l => C (a i k l) + X * C (b i k l - a i k l)).det
  have hev : ∀ i z, (p i).eval z = (L z i).det := by
    intro i z
    simp only [p, L]
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext k l
    simp [Matrix.of_apply]
    ring
  have hp : ∀ i, p i ≠ 0 := by
    intro i h0
    have := hev i 0
    rw [h0, eval_zero] at this
    exact ha i (by simpa [L] using this.symm)
  let Z : Set ℂ := ⋃ i, {z | (p i).IsRoot z}
  have hZ : Z.Countable := (Set.finite_iUnion fun i => Polynomial.finite_setOfPred_isRoot (hp i)).countable
  have hc : IsPreconnected Zᶜ :=
    (hZ.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected
  have hLc : Continuous L := by
    simp only [L]
    fun_prop
  have hmem : ∀ z ∈ Zᶜ, L z ∈ {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0} := by
    intro z hz
    refine ⟨hV a haV b hbV z, fun i h0 => hz ?_⟩
    exact Set.mem_iUnion.2 ⟨i, by show (p i).eval z = 0; rw [hev]; exact h0⟩
  have hnot : ∀ z, (∀ i, (L z i).det ≠ 0) → z ∈ Zᶜ := by
    intro z hz hZz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hZz
    exact hz i (by rw [← hev]; exact hi)
  have hL0 : L 0 = a := by simp [L]
  have hL1 : L 1 = b := by simp [L]
  refine ⟨L '' Zᶜ, ?_, ⟨0, hnot 0 (by rw [hL0]; exact ha), hL0⟩,
    ⟨1, hnot 1 (by rw [hL1]; exact hb), hL1⟩, hc.image L hLc.continuousOn⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hmem z hz

end Line

open Matrix
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {r : ℕ} (p0 : ℕ)

def sv (a : Fin r) : ℂ := if (a : ℕ) < p0 then 1 else -1

def Gy (y : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  yᵀ * diagonal (sv p0) * y.map (starRingEnd ℂ)

def Ok (y : Matrix (Fin r) (Fin r) ℂ) : Prop := (diagonal (sv p0) * Gy p0 y).PosDef

def mask (t : ℝ) (y : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun k a => (if ((k : ℕ) < p0 ↔ (a : ℕ) < p0) then 1 else (t : ℂ)) * y k a

def Wm (s : ℂ) (y : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun k b => if ((k : ℕ) < p0 ↔ (b : ℕ) < p0) then 0 else s * conj (y k b)

variable {p0}

lemma sv_star (a : Fin r) : star (sv p0 a) = sv p0 a := by
  unfold sv
  split_ifs <;> simp

lemma Gy_apply (y : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    Gy p0 y a b = ∑ k, y k a * sv p0 k * conj (y k b) := by
  rw [Gy, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]

lemma det_ne_of_ok {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) : y.det ≠ 0 := by
  intro h0
  have hpos := h.det_pos
  rw [Gy, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0] at hpos
  simp at hpos

lemma lead_pos {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) (i : ℕ) (hi : i ≤ r) :
    0 < (∏ a ∈ Finset.range i, (if a < p0 then (1 : ℝ) else -1)) *
      ((Gy p0 y).submatrix (Fin.castLE hi) (Fin.castLE hi)).det.re := by
  have hpd := h.submatrix (Fin.castLE_injective hi)
  have hsub : (diagonal (sv p0) * Gy p0 y).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      diagonal (fun j : Fin i => sv p0 (Fin.castLE hi j)) * (Gy p0 y).submatrix (Fin.castLE hi) (Fin.castLE hi) := by
    ext a b
    simp [Matrix.diagonal_mul]
  rw [hsub] at hpd
  have hd := hpd.det_pos
  rw [Matrix.det_mul, Matrix.det_diagonal] at hd
  have hprod : ∏ j : Fin i, sv p0 (Fin.castLE hi j) =
      ((∏ a ∈ Finset.range i, (if a < p0 then (1 : ℝ) else -1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [sv, Fin.val_castLE]
    split_ifs <;> simp
  rw [hprod] at hd
  have h2 := (Complex.lt_def.1 hd).1
  rw [Complex.re_ofReal_mul, Complex.zero_re] at h2
  exact h2

lemma sv_ne {a b : Fin r} (hab : ¬((a : ℕ) < p0 ↔ (b : ℕ) < p0)) : sv p0 b ≠ sv p0 a := by
  unfold sv
  split_ifs with h1 h2
  · exact absurd (iff_of_true h2 h1) hab
  · norm_num
  · norm_num
  · exact absurd (iff_of_false ‹_› h1) hab

lemma cross_zero {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) {a b : Fin r}
    (hab : ¬((a : ℕ) < p0 ↔ (b : ℕ) < p0)) : Gy p0 y a b = 0 := by
  have hH := h.isHermitian
  have hG : star (Gy p0 y b a) = Gy p0 y a b := by
    rw [Gy_apply, Gy_apply, star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [star_mul', sv_star, Complex.star_def, Complex.conj_conj]
    ring
  have h1 := (hH.apply a b).symm
  simp only [Matrix.diagonal_mul] at h1
  rw [star_mul', sv_star, hG] at h1
  have h2 : (sv p0 a - sv p0 b) * Gy p0 y a b = 0 := by rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3).symm (sv_ne hab)
  · exact h3

lemma mask_eq {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) (t : ℝ) (s : ℂ) (hs : conj s * s = 1 - (t : ℂ) ^ 2) :
    diagonal (sv p0) * Gy p0 (mask p0 t y) = diagonal (sv p0) * Gy p0 y + (Wm p0 s y)ᴴ * Wm p0 s y := by
  ext a b
  rw [Matrix.add_apply, Matrix.diagonal_mul, Matrix.diagonal_mul, Gy_apply, Gy_apply, Matrix.mul_apply]
  by_cases hab : ((a : ℕ) < p0 ↔ (b : ℕ) < p0)
  · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [mask, Wm, Matrix.of_apply, Matrix.conjTranspose_apply]
    by_cases hk : (k : ℕ) < p0 <;> by_cases ha : (a : ℕ) < p0 <;> by_cases hb : (b : ℕ) < p0 <;>
      simp [hk, ha, hb, sv] at hab ⊢ <;>
      first | ring1 | linear_combination (-(y k a * (starRingEnd ℂ) (y k b))) * hs
  · have hz := cross_zero h hab
    rw [Gy_apply] at hz
    rw [hz, mul_zero, zero_add]
    have hw : ∀ k : Fin r, star (Wm p0 s y k a) * Wm p0 s y k b = 0 := by
      intro k
      simp only [Wm, Matrix.of_apply]
      by_cases hk : (k : ℕ) < p0 <;> by_cases ha : (a : ℕ) < p0 <;> by_cases hb : (b : ℕ) < p0 <;>
        simp [hk, ha, hb] at hab ⊢
    simp only [Matrix.conjTranspose_apply, hw, Finset.sum_const_zero]
    have h4 : sv p0 a * ∑ k, mask p0 t y k a * sv p0 k * conj (mask p0 t y k b) =
        (t : ℂ) * (sv p0 a * ∑ k, y k a * sv p0 k * conj (y k b)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mask, Matrix.of_apply]
      by_cases hk : (k : ℕ) < p0 <;> by_cases ha : (a : ℕ) < p0 <;> by_cases hb : (b : ℕ) < p0 <;>
        simp [hk, ha, hb] at hab ⊢ <;> ring
    rw [h4, hz, mul_zero, mul_zero]

variable {p0 : ℕ}

lemma ok_mask {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ok p0 (mask p0 t y) := by
  have hs : conj ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) = 1 - (t : ℂ) ^ 2 := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by nlinarith)]
    push_cast
    ring
  unfold Ok
  rw [mask_eq h t _ hs]
  exact h.add_posSemidef (posSemidef_conjTranspose_mul_self _)

lemma ok_of_blk {y : Matrix (Fin r) (Fin r) ℂ}
    (hy : ∀ k a : Fin r, ¬((k : ℕ) < p0 ↔ (a : ℕ) < p0) → y k a = 0) (hd : y.det ≠ 0) : Ok p0 y := by
  have key : diagonal (sv p0) * Gy p0 y = (y.map (starRingEnd ℂ))ᴴ * y.map (starRingEnd ℂ) := by
    ext a b
    rw [Matrix.diagonal_mul, Gy_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def, Complex.conj_conj]
    by_cases hka : ((k : ℕ) < p0 ↔ (a : ℕ) < p0)
    · have hs : sv p0 a * sv p0 k = 1 := by
        unfold sv
        by_cases hk : (k : ℕ) < p0 <;> by_cases ha : (a : ℕ) < p0
        · rw [if_pos ha, if_pos hk]; norm_num
        · exact absurd (hka.1 hk) ha
        · exact absurd (hka.2 ha) hk
        · rw [if_neg ha, if_neg hk]; norm_num
      calc sv p0 a * (y k a * sv p0 k * (starRingEnd ℂ) (y k b))
          = (sv p0 a * sv p0 k) * (y k a * (starRingEnd ℂ) (y k b)) := by ring
        _ = y k a * (starRingEnd ℂ) (y k b) := by rw [hs, one_mul]
    · rw [hy k a hka]
      ring
  unfold Ok
  rw [key]
  apply Matrix.PosDef.conjTranspose_mul_self
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hdet : (y.map (starRingEnd ℂ)).det = starRingEnd ℂ y.det := (RingHom.map_det _ _).symm
  rw [hdet]
  exact (map_ne_zero _).2 hd

lemma mask_one (y : Matrix (Fin r) (Fin r) ℂ) : mask p0 1 y = y := by
  ext k a
  simp [mask]

lemma mask_zero_blk (y : Matrix (Fin r) (Fin r) ℂ) {k a : Fin r} (h : ¬((k : ℕ) < p0 ↔ (a : ℕ) < p0)) :
    mask p0 0 y k a = 0 := by
  simp [mask, h]

lemma continuous_mask (y : Matrix (Fin r) (Fin r) ℂ) : Continuous fun t : ℝ => mask p0 t y := by
  refine continuous_pi fun k => continuous_pi fun a => ?_
  simp only [mask, Matrix.of_apply]
  split_ifs <;> fun_prop

theorem isPreconnected_ok {ι : Type*} [Fintype ι] :
    IsPreconnected {y : ι → Matrix (Fin r) (Fin r) ℂ | ∀ i, Ok p0 (y i)} := by
  let V : Set (ι → Matrix (Fin r) (Fin r) ℂ) :=
    {x | ∀ i (k a : Fin r), ¬((k : ℕ) < p0 ↔ (a : ℕ) < p0) → x i k a = 0}
  have hV : ∀ a ∈ V, ∀ b ∈ V, ∀ z : ℂ, (1 - z) • a + z • b ∈ V := by
    intro a ha b hb z i k l hkl
    simp [ha i k l hkl, hb i k l hkl]
  have hBD := isPreconnected_det_ne V hV
  have hsub : {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0} ⊆ {y : ι → Matrix (Fin r) (Fin r) ℂ | ∀ i, Ok p0 (y i)} :=
    fun x hx i => ok_of_blk (hx.1 i) (hx.2 i)
  have h1 : (1 : ι → Matrix (Fin r) (Fin r) ℂ) ∈ {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0} := by
    refine ⟨fun i k a hka => ?_, fun i => by simp⟩
    have hne : k ≠ a := by
      rintro rfl
      exact hka Iff.rfl
    simp [Matrix.one_apply_ne hne]
  refine isPreconnected_of_forall 1 fun y hy => ?_
  let γ : ℝ → ι → Matrix (Fin r) (Fin r) ℂ := fun t i => mask p0 t (y i)
  have hγc : Continuous γ := continuous_pi fun i => continuous_mask (y i)
  have hγ0 : γ 0 ∈ {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0} :=
    ⟨fun i k a hka => mask_zero_blk (y i) hka, fun i => det_ne_of_ok (ok_mask (hy i) le_rfl zero_le_one)⟩
  refine ⟨γ '' Set.Icc 0 1 ∪ {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0}, ?_, Or.inr (hsub h1 |> fun _ => h1),
    Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, funext fun i => mask_one (y i)⟩, ?_⟩
  · rintro x (⟨t, ⟨ht0, ht1⟩, rfl⟩ | hx)
    · exact fun i => ok_mask (hy i) ht0 ht1
    · exact hsub hx
  · exact IsPreconnected.union (γ 0) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ hγ0
      (isPreconnected_Icc.image γ hγc.continuousOn) hBD

theorem isPreconnected_upper {ι : Type*} [Fintype ι] :
    IsPreconnected {b : ι → Matrix (Fin r) (Fin r) ℂ |
      ∀ i, (b i).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b i a c = 0} := by
  have h := isPreconnected_det_ne {x : ι → Matrix (Fin r) (Fin r) ℂ | ∀ i (a c : Fin r), c < a → x i a c = 0}
    (by
      intro a ha b hb z i k l hkl
      simp [ha i k l hkl, hb i k l hkl])
  convert h using 1
  ext b
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨fun i => (h i).2, fun i => (h i).1⟩, fun h i => ⟨h.2 i, h.1 i⟩⟩

end

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
