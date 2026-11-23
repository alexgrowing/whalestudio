import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockUnitriangularFlagStatement
import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

theorem antidiag_unique {ι : Type} [Fintype ι] [DecidableEq ι] (l : ι → ℕ) (N : ℕ) (u u' A B : Matrix ι ι ℂ)
    (hu : ∀ i j, l j ≤ l i → u i j = (1 : Matrix ι ι ℂ) i j)
    (hu' : ∀ i j, l j ≤ l i → u' i j = (1 : Matrix ι ι ℂ) i j)
    (hA : ∀ i j, l i + l j ≠ N → A i j = 0) (hB : ∀ i j, l i + l j ≠ N → B i j = 0)
    (h : u * A = B * u') : A = B ∧ u * A = A := by
  have one_ap : ∀ i j : ι, (1 : Matrix ι ι ℂ) i j = if i = j then 1 else 0 := fun i j => Matrix.one_apply
  have ha : ∀ i j, N < l i + l j → (u * A) i j = 0 := by
    intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : l m + l j = N
    · rw [hu i m (by omega), one_ap]
      split_ifs with him
      · exfalso; subst him; omega
      · simp
    · rw [hA m j hm, mul_zero]
  have hb : ∀ i j, l i + l j = N → (u * A) i j = A i j := by
    intro i j hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hu i i le_rfl, one_ap, if_pos rfl, one_mul]
    · intro m _ hmi
      by_cases hm : l m + l j = N
      · rw [hu i m (by omega), one_ap, if_neg (Ne.symm hmi), zero_mul]
      · rw [hA m j hm, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hc : ∀ i j, l i + l j < N → (B * u') i j = 0 := by
    intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : l i + l m = N
    · rw [hu' m j (by omega), one_ap]
      split_ifs with hmj
      · exfalso; subst hmj; omega
      · simp
    · rw [hB i m hm, zero_mul]
  have hd : ∀ i j, l i + l j = N → (B * u') i j = B i j := by
    intro i j hij
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hu' j j le_rfl, one_ap, if_pos rfl, mul_one]
    · intro m _ hmj
      by_cases hm : l i + l m = N
      · rw [hu' m j (by omega), one_ap, if_neg hmj, mul_zero]
      · rw [hB i m hm, zero_mul]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hAB : A = B := by
    ext i j
    by_cases hij : l i + l j = N
    · rw [← hb i j hij, ← hd i j hij, h]
    · rw [hA i j hij, hB i j hij]
  refine ⟨hAB, ?_⟩
  ext i j
  rcases lt_trichotomy (l i + l j) N with hlt | heq | hgt
  · rw [h, hc i j hlt, hA i j (by omega)]
  · exact hb i j heq
  · rw [ha i j hgt, hA i j (by omega)]

theorem bigCell_support (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) (h : lev k r i + lev k r j ≠ 2 * r) : bigCell k r c μ i j = 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [bigCell]
  by_cases h1 : j.val < r
  · rw [dif_pos h1]
    split_ifs with h3
    · exfalso
      have hv : i.val = 2 * r + k - j.val := by subst h3; rfl
      unfold lev at h
      split_ifs at h <;> omega
    · rfl
  · rw [dif_neg h1]
    by_cases h2 : j.val ≤ r + k
    · rw [dif_pos h2]
      split_ifs with h3
      · exfalso
        unfold lev at h
        split_ifs at h <;> omega
      · rfl
    · rw [dif_neg h2]
      split_ifs with h3
      · exfalso
        unfold lev at h
        split_ifs at h <;> omega
      · rfl

theorem bigCell_entry (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (a : Fin r) :
    bigCell k r c μ (esI k r a) (eI k r a) = c a := by
  have h1 : (eI k r a).val < r := a.isLt
  simp only [bigCell]
  rw [dif_pos h1]
  exact if_pos rfl

private theorem lev_mono' (k r : ℕ) (i j : Fin (2 * r + k + 1)) (h : j.val ≤ i.val) :
    lev k r j ≤ lev k r i := by
  unfold lev
  split_ifs <;> omega

private theorem mul_apply_eq_one_apply_of_unitriangular_lev {k r : ℕ} {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : ∀ i j, lev k r j ≤ lev k r i → g i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) (hh : ∀ i j, lev k r j ≤ lev k r i → h i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) : ∀ i j, lev k r j ≤ lev k r i → (g * h) i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := by
  intro i j hij
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hg i i le_rfl, hh i j hij, Matrix.one_apply_eq, one_mul]
  · intro m _ hmi
    by_cases hm : lev k r m ≤ lev k r i
    · rw [hg i m hm, Matrix.one_apply_ne (Ne.symm hmi), zero_mul]
    · have hmj : m ≠ j := by
        intro hmj'
        subst hmj'
        exact hm hij
      rw [hh m j (by omega), Matrix.one_apply_ne hmj, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem isUnit_det_of_unitriangular_lev {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : ∀ i j, lev k r j ≤ lev k r i → g i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) : IsUnit g.det := by
  have hbt : Matrix.BlockTriangular g id := by
    intro i j hij
    rw [hg i j (lev_mono' k r i j (le_of_lt hij)), Matrix.one_apply_ne (ne_of_gt hij : i ≠ j)]
  rw [Matrix.det_of_isUpperTriangular hbt]
  have hd : ∀ i, g i i = 1 := fun i => by rw [hg i i le_rfl, Matrix.one_apply_eq]
  simp [hd]

private theorem inv_apply_eq_one_apply_of_unitriangular_lev {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : ∀ i j, lev k r j ≤ lev k r i → g i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) : ∀ i j, lev k r j ≤ lev k r i → g⁻¹ i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := by
  have hbt : Matrix.BlockTriangular g (lev k r) := by
    intro i j hij
    rw [hg i j hij.le, Matrix.one_apply_ne]
    intro hij'
    subst hij'
    exact lt_irrefl _ hij
  have : Invertible g := Matrix.invertibleOfIsUnitDet g (isUnit_det_of_unitriangular_lev hg)
  have hbi := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have hone : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g (isUnit_det_of_unitriangular_lev hg)
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | heq
  · rw [hbi hlt, Matrix.one_apply_ne]
    intro hij'
    subst hij'
    exact lt_irrefl _ hlt
  · rw [← hone, Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hg j j le_rfl, Matrix.one_apply_eq, mul_one]
    · intro m _ hmj
      by_cases hm : lev k r m < lev k r i
      · rw [hbi hm, zero_mul]
      · rw [hg m j (by omega), Matrix.one_apply_ne hmj, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj

private theorem bigCell_mid_apply (k r : ℕ) (c : Fin r → ℂ) (m j : Fin (2 * r + k + 1)) (h1 : r ≤ j.val)
    (h2 : j.val ≤ r + k) : bigCell k r c 1 m j = if m = j then 1 else 0 := by
  by_cases hm : Formalism.FourierDecayAlt.P.TwoByOneBlock.mid k r m
  · exact Formalism.FourierDecayAlt.P.TwoByOneBlock.bc_one_mid c m j hm ⟨h1, h2⟩
  · rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.bc_mid_col c 1 m j ⟨h1, h2⟩, dif_neg hm, if_neg]
    intro hmj
    subst hmj
    exact hm ⟨h1, h2⟩

private theorem bigCell_mul_bigCell_star (k r : ℕ) (x : Fin r → ℂ) (hx : ∀ a, x a ≠ 0) :
    bigCell k r x 1 * bigCell k r (fun a => star (x a)) 1 = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hj := j.isLt
  have hi := i.isLt
  by_cases h1 : j.val < r
  · obtain ⟨a, ha⟩ : ∃ a : Fin r, a.val = j.val := ⟨⟨j.val, h1⟩, rfl⟩
    obtain ⟨p, hp⟩ : ∃ p : Fin (2 * r + k + 1), p.val = 2 * r + k - j.val := ⟨⟨2 * r + k - j.val, by omega⟩, rfl⟩
    rw [Finset.sum_eq_single p]
    · rw [Formalism.QuantumDeterminants.BruhatBigCell.col_lo (fun a => star (x a)) 1 p j a ha.symm,
        Formalism.QuantumDeterminants.BruhatBigCell.col_hi x 1 i p a (by omega),
        if_pos (show p.val = 2 * r + k - a.val by omega)]
      by_cases hia : i.val = a.val
      · have hij : i = j := Fin.ext (by omega)
        rw [if_pos hia, hij, Matrix.one_apply_eq]
        show (star (x a))⁻¹ * star (x a) = 1
        exact inv_mul_cancel₀ (star_ne_zero.mpr (hx a))
      · rw [if_neg hia, zero_mul, Matrix.one_apply_ne (show i ≠ j from fun h => hia (by rw [h]; omega))]
    · intro m _ hm
      rw [Formalism.QuantumDeterminants.BruhatBigCell.col_lo (fun a => star (x a)) 1 m j a ha.symm,
        if_neg (show ¬ m.val = 2 * r + k - a.val from fun h' => hm (Fin.ext (by omega))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · by_cases h2 : j.val ≤ r + k
    · rw [Finset.sum_eq_single j]
      · rw [bigCell_mid_apply k r (fun a => star (x a)) j j (by omega) h2, bigCell_mid_apply k r x i j (by omega) h2,
          if_pos (rfl : j = j), mul_one, Matrix.one_apply]
      · intro m _ hm
        rw [bigCell_mid_apply k r (fun a => star (x a)) m j (by omega) h2, if_neg hm, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · obtain ⟨a, ha⟩ : ∃ a : Fin r, a.val = 2 * r + k - j.val := ⟨⟨2 * r + k - j.val, by omega⟩, rfl⟩
      obtain ⟨p, hp⟩ : ∃ p : Fin (2 * r + k + 1), p.val = a.val := ⟨⟨a.val, by omega⟩, rfl⟩
      rw [Finset.sum_eq_single p]
      · rw [Formalism.QuantumDeterminants.BruhatBigCell.col_hi (fun a => star (x a)) 1 p j a (by omega),
          Formalism.QuantumDeterminants.BruhatBigCell.col_lo x 1 i p a hp, if_pos hp]
        by_cases hia : i.val = 2 * r + k - a.val
        · have hij : i = j := Fin.ext (by omega)
          rw [if_pos hia, hij, Matrix.one_apply_eq]
          show x a * (star (star (x a)))⁻¹ = 1
          rw [star_star]
          exact mul_inv_cancel₀ (hx a)
        · rw [if_neg hia, zero_mul, Matrix.one_apply_ne (show i ≠ j from fun h => hia (by rw [h]; omega))]
      · intro m _ hm
        rw [Formalism.QuantumDeterminants.BruhatBigCell.col_hi (fun a => star (x a)) 1 m j a (by omega),
          if_neg (show ¬ m.val = a.val from fun h' => hm (Fin.ext (by omega))), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h

theorem bigCell_coords_unique : ∀ (k r : ℕ) (x y : Fin r → ℂ), (∀ a, x a ≠ 0) → (∀ a, y a ≠ 0) →
    ∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, ∀ n₁' ∈ Nset k r, ∀ n₂' ∈ Nset k r,
    ∀ m₁ ∈ Formalism.FourierDecayAlt.B2.UWb k r, ∀ m₂ ∈ Formalism.FourierDecayAlt.B2.UWb k r,
    n₁⁻¹ * bigCell k r x 1 * m₁ * n₁' = n₂⁻¹ * bigCell k r y 1 * m₂ * n₂' →
    n₁ = n₂ ∧ x = y ∧ m₁ = m₂ ∧ n₁' = n₂' := by
  intro k r x y hx hy n₁ hn₁ n₂ hn₂ n₁' hn₁' n₂' hn₂' m₁ hm₁ m₂ hm₂ h
  have hP : ∀ g ∈ Nset k r, ∀ i j, lev k r j ≤ lev k r i → g i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := fun g hg => GlobalTheory.T.unipotentRadical_block_unitriangular_flag k r g hg
  obtain ⟨μ₁, hμ₁, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff m₁).1 hm₁
  obtain ⟨μ₂, hμ₂, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff m₂).1 hm₂
  rw [Matrix.mul_assoc n₁⁻¹, Matrix.mul_assoc n₂⁻¹, ← (Formalism.FourierDecayAlt.P.TwoByOneBlock.bigCellFactor k r x μ₁).1,
    ← (Formalism.FourierDecayAlt.P.TwoByOneBlock.bigCellFactor k r y μ₂).1] at h
  have hdet : ∀ g ∈ Nset k r, IsUnit g.det := fun g hg => isUnit_det_of_unitriangular_lev (hP g hg)
  have hA : IsUnit (bigCell k r x μ₁).det := by
    rw [(Formalism.FourierDecayAlt.P.TwoByOneBlock.bigCellFactor k r x μ₁).1, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_right_inverse (bigCell_mul_bigCell_star k r x hx)).mul
      (Matrix.isUnit_det_of_right_inverse (B := Formalism.FourierDecayAlt.B2.embWb k r μ₁⁻¹) (by
        rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mul, Matrix.mul_nonsing_inv μ₁ (Formalism.FourierDecayAlt.P.TwoByOneBlock.UHb_inv hμ₁).1,
          Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_one]))
  have key : (n₂ * n₁⁻¹) * bigCell k r x μ₁ = bigCell k r y μ₂ * (n₂' * n₁'⁻¹) := by
    calc (n₂ * n₁⁻¹) * bigCell k r x μ₁
        = n₂ * (n₁⁻¹ * bigCell k r x μ₁ * n₁') * n₁'⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv n₁' (hdet n₁' hn₁'), Matrix.mul_one]
      _ = n₂ * (n₂⁻¹ * bigCell k r y μ₂ * n₂') * n₁'⁻¹ := by rw [h]
      _ = bigCell k r y μ₂ * (n₂' * n₁'⁻¹) := by
          simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv n₂ (hdet n₂ hn₂), Matrix.one_mul]
  obtain ⟨hAB, hUA⟩ := antidiag_unique (lev k r) (2 * r) (n₂ * n₁⁻¹) (n₂' * n₁'⁻¹)
    (bigCell k r x μ₁) (bigCell k r y μ₂)
    (mul_apply_eq_one_apply_of_unitriangular_lev (hP n₂ hn₂) (inv_apply_eq_one_apply_of_unitriangular_lev (hP n₁ hn₁)))
    (mul_apply_eq_one_apply_of_unitriangular_lev (hP n₂' hn₂') (inv_apply_eq_one_apply_of_unitriangular_lev (hP n₁' hn₁')))
    (fun i j hij => bigCell_support k r x μ₁ i j hij) (fun i j hij => bigCell_support k r y μ₂ i j hij) key
  have hxy : x = y := by
    funext a
    have e := congrFun (congrFun hAB (esI k r a)) (eI k r a)
    rwa [bigCell_entry, bigCell_entry] at e
  have hμ : μ₁ = μ₂ := by
    ext p q
    have e := congrFun (congrFun hAB (Formalism.QuantumDeterminants.wI k r p)) (Formalism.QuantumDeterminants.wI k r q)
    rwa [Formalism.QuantumDeterminants.BruhatBigCell.mid_mid, Formalism.QuantumDeterminants.BruhatBigCell.mid_mid] at e
  have hinvA := Matrix.mul_nonsing_inv (bigCell k r x μ₁) hA
  have hinvA' := Matrix.nonsing_inv_mul (bigCell k r x μ₁) hA
  have hu1 : n₂ * n₁⁻¹ = 1 := by
    calc n₂ * n₁⁻¹ = (n₂ * n₁⁻¹) * bigCell k r x μ₁ * (bigCell k r x μ₁)⁻¹ := by
          rw [Matrix.mul_assoc (n₂ * n₁⁻¹), hinvA, Matrix.mul_one]
      _ = 1 := by rw [hUA, hinvA]
  have hn : n₁ = n₂ := by
    calc n₁ = (n₂ * n₁⁻¹) * n₁ := by rw [hu1, Matrix.one_mul]
      _ = n₂ := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul n₁ (hdet n₁ hn₁), Matrix.mul_one]
  have hAu' : bigCell k r x μ₁ * (n₂' * n₁'⁻¹) = bigCell k r x μ₁ := by
    calc bigCell k r x μ₁ * (n₂' * n₁'⁻¹) = bigCell k r y μ₂ * (n₂' * n₁'⁻¹) := by rw [hAB]
      _ = bigCell k r x μ₁ := by rw [← key, hUA]
  have hu1' : n₂' * n₁'⁻¹ = 1 := by
    calc n₂' * n₁'⁻¹ = (bigCell k r x μ₁)⁻¹ * (bigCell k r x μ₁ * (n₂' * n₁'⁻¹)) := by
          rw [← Matrix.mul_assoc, hinvA', Matrix.one_mul]
      _ = 1 := by rw [hAu', hinvA']
  have hn' : n₁' = n₂' := by
    calc n₁' = (n₂' * n₁'⁻¹) * n₁' := by rw [hu1', Matrix.one_mul]
      _ = n₂' := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul n₁' (hdet n₁' hn₁'), Matrix.mul_one]
  exact ⟨hn, hxy, by rw [hμ], hn'⟩

end GlobalTheory.CellDens
