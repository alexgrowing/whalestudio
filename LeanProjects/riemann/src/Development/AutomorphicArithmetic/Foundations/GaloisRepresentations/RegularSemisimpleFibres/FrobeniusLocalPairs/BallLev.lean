import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.SmallRadAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractB

noncomputable section

open ValuativeRel Matrix GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

section Mat

variable {k : Type} [Field k] {n : ℕ}

private def colM (p : Fin n) (a : Fin n → k) : Matrix (Fin n) (Fin n) k := fun i j => if j = p then a i else 0

private def rowM (p : Fin n) (b : Fin n → k) : Matrix (Fin n) (Fin n) k := fun i j => if i = p then b j else 0

private theorem colM_mul (p : Fin n) (a : Fin n → k) (M : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    (colM p a * M) i j = a i * M p j := by
  simp [Matrix.mul_apply, colM, ite_mul]

private theorem mul_rowM (p : Fin n) (b : Fin n → k) (M : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    (M * rowM p b) i j = M i p * b j := by
  simp [Matrix.mul_apply, rowM, mul_ite]

private theorem colM_sq {p : Fin n} {a : Fin n → k} (h : a p = 0) : colM p a * colM p a = 0 := by
  ext i j
  rw [colM_mul]
  simp [colM, h]

private theorem rowM_sq {p : Fin n} {b : Fin n → k} (h : b p = 0) : rowM p b * rowM p b = 0 := by
  ext i j
  rw [mul_rowM]
  simp [rowM, h]

private def nilU (A : Matrix (Fin n) (Fin n) k) (h : A * A = 0) : GL (Fin n) k where
  val := 1 + A
  inv := 1 - A
  val_inv := by simp [add_mul, mul_sub, h]
  inv_val := by simp [sub_mul, mul_add, h]

private theorem mem_low {g : GL (Fin n) k} :
    g ∈ unipBLower k (Fin n) ↔ (∀ i j, i < j → (g : Matrix (Fin n) (Fin n) k) i j = 0) ∧
      ∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1 := by
  refine (mem_unipRad (e := opp (points (Fin n)))).trans (and_congr Iff.rfl ⟨fun h i => ?_, fun h i _ _ => ?_⟩)
  · exact (h i () ()).trans (by simp)
  · exact (h i).trans (by simp)

private theorem conj_entry (t : Fin n → kˣ) (u : GL (Fin n) k) (i j : Fin n) :
    ((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (t i : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t j : k)⁻¹ := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

private theorem conj_entry' (t : Fin n → kˣ) (u : GL (Fin n) k) (i j : Fin n) :
    (((diagT k (Fin n) t)⁻¹ * u * diagT k (Fin n) t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (t j : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t i : k)⁻¹ := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp
  ring

end Mat

section Val

variable {k : Type} [Field k] [ValuativeRel k]

private theorem val_one_of {r : ValueGroupWithZero k} (hr : r < 1) {x : k} (h : valuation k (x - 1) ≤ r) :
    valuation k x = 1 := by
  have h1 : valuation k (x - 1) < valuation k (1 : k) := by simpa using h.trans_lt hr
  have e := Valuation.map_add_eq_of_lt_left (valuation k) h1
  simpa using e

private theorem val_le {x z : kˣ} (h : valuation k (x : k) ≤ valuation k (z : k)) (y : k) :
    valuation k ((x : k) * y * (z : k)⁻¹) ≤ valuation k y := by
  have hz : 0 < valuation k (z : k) := zero_lt_iff.2 (by simp)
  rw [map_mul, map_mul, map_inv₀, mul_comm (valuation k (x : k)), mul_assoc]
  refine mul_le_of_le_one_right' ?_
  rw [← div_eq_mul_inv]
  exact (div_le_one₀ hz).2 h

end Val

section Fact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem nat_mul_factorial_bound {r : ValueGroupWithZero k} (hr : r < 1) (K : Subgroup (GL (Fin n) k))
    (hK : (K : Set (GL (Fin n) k)) = ball n r) :
    ∀ m, m ≤ n → ∀ g ∈ K,
      (∀ i j : Fin n, i ≠ j → (m ≤ i.1 ∨ m ≤ j.1) → (g : Matrix (Fin n) (Fin n) k) i j = 0) →
      ∃ u ∈ K ⊓ unipB k (Fin n), ∃ d, diagT k (Fin n) d ∈ K ∧ ∃ c ∈ K ⊓ unipBLower k (Fin n),
        g = u * diagT k (Fin n) d * c := by
  have hmem : ∀ g, g ∈ K ↔ g ∈ ball n r := fun g => by rw [← SetLike.mem_coe, hK]
  have hd1 : ∀ g ∈ K, ∀ i, valuation k ((g : Matrix (Fin n) (Fin n) k) i i) = 1 := fun g hg i =>
    val_one_of hr (by simpa using (hmem g).1 hg i i)
  intro m
  induction m with
  | zero =>
    intro _ g hg hc
    have h0 : ∀ i, (g : Matrix (Fin n) (Fin n) k) i i ≠ 0 := fun i h => by
      have := hd1 g hg i
      simp [h] at this
    let d : Fin n → kˣ := fun i => Units.mk0 _ (h0 i)
    have e : g = diagT k (Fin n) d := by
      ext i j
      rw [val_diagT]
      by_cases h : i = j
      · subst h
        simp [d]
      · rw [diagonal_apply_ne _ h]
        exact hc i j h (Or.inl (Nat.zero_le _))
    exact ⟨1, one_mem _, d, e ▸ hg, 1, one_mem _, by simpa using e⟩
  | succ m ih =>
    intro hm g hg hc
    let p : Fin n := ⟨m, hm⟩
    have hgr : ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r :=
      (hmem g).1 hg
    have hpp : valuation k ((g : Matrix (Fin n) (Fin n) k) p p) = 1 := hd1 g hg p
    have hp0 : (g : Matrix (Fin n) (Fin n) k) p p ≠ 0 := fun h => by simp [h] at hpp
    let a : Fin n → k := fun i => if i < p then (g : Matrix (Fin n) (Fin n) k) i p / (g : Matrix (Fin n) (Fin n) k) p p else 0
    let b : Fin n → k := fun j => if j < p then (g : Matrix (Fin n) (Fin n) k) p j / (g : Matrix (Fin n) (Fin n) k) p p else 0
    have ap : a p = 0 := by simp [a]
    have bp : b p = 0 := by simp [b]
    have ha : ∀ i, valuation k (a i) ≤ r := fun i => by
      simp only [a]
      split_ifs with h
      · have := hgr i p
        rw [one_apply_ne h.ne, sub_zero] at this
        rwa [map_div₀, hpp, div_one]
      · simp
    have hb : ∀ j, valuation k (b j) ≤ r := fun j => by
      simp only [b]
      split_ifs with h
      · have := hgr p j
        rw [one_apply_ne h.ne', sub_zero] at this
        rwa [map_div₀, hpp, div_one]
      · simp
    let U : GL (Fin n) k := nilU (colM p a) (colM_sq ap)
    let L : GL (Fin n) k := nilU (rowM p b) (rowM_sq bp)
    have hUv : (U : Matrix (Fin n) (Fin n) k) = 1 + colM p a := rfl
    have hLv : (L : Matrix (Fin n) (Fin n) k) = 1 + rowM p b := rfl
    have hUi : ((U⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 - colM p a := rfl
    have hLi : ((L⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 - rowM p b := rfl
    have hU : U ∈ K ⊓ unipB k (Fin n) := by
      refine ⟨(hmem U).2 fun i j => ?_, (mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩⟩
      · rw [hUv, Matrix.add_apply, add_sub_cancel_left]
        simp only [colM]
        split_ifs
        · exact ha i
        · simp
      · rw [hUv, Matrix.add_apply, one_apply_ne hji.ne', zero_add]
        simp only [colM]
        split_ifs with h
        · subst h
          simp [a, hji.not_gt]
        · rfl
      · rw [hUv, Matrix.add_apply, one_apply_eq]
        simp only [colM]
        split_ifs with h
        · subst h
          simp [ap]
        · simp
    have hL : L ∈ K ⊓ unipBLower k (Fin n) := by
      refine ⟨(hmem L).2 fun i j => ?_, mem_low.2 ⟨fun i j hij => ?_, fun i => ?_⟩⟩
      · rw [hLv, Matrix.add_apply, add_sub_cancel_left]
        simp only [rowM]
        split_ifs
        · exact hb j
        · simp
      · rw [hLv, Matrix.add_apply, one_apply_ne hij.ne, zero_add]
        simp only [rowM]
        split_ifs with h
        · subst h
          simp [b, hij.not_gt]
        · rfl
      · rw [hLv, Matrix.add_apply, one_apply_eq]
        simp only [rowM]
        split_ifs with h
        · subst h
          simp [bp]
        · simp
    have hH : ∀ i j, (((U⁻¹ * g : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j =
        (g : Matrix (Fin n) (Fin n) k) i j - a i * (g : Matrix (Fin n) (Fin n) k) p j := fun i j => by
      rw [Units.val_mul, hUi, sub_mul, one_mul, Matrix.sub_apply, colM_mul]
    have hE : ∀ i j, (((U⁻¹ * g * L⁻¹ : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j =
        (((U⁻¹ * g : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j -
          (((U⁻¹ * g : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i p * b j := fun i j => by
      rw [Units.val_mul _ (L⁻¹), hLi, mul_sub, mul_one, Matrix.sub_apply, mul_rowM]
    have hclean : ∀ i j : Fin n, i ≠ j → (m ≤ i.1 ∨ m ≤ j.1) →
        (((U⁻¹ * g * L⁻¹ : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j = 0 := by
      intro i j hij hor
      rw [hE, hH, hH]
      by_cases hi : m + 1 ≤ i.1
      · have hip : ¬ i < p := fun h => by
          have : i.1 < m := h
          omega
        have hne : i ≠ p := fun h => by
          have : i.1 = m := congrArg Fin.val h
          omega
        have e1 := hc i j hij (Or.inl hi)
        have e2 := hc i p hne (Or.inl hi)
        simp [a, hip, e1, e2]
      by_cases hj : m + 1 ≤ j.1
      · have hjp : ¬ j < p := fun h => by
          have : j.1 < m := h
          omega
        have hne : p ≠ j := fun h => by
          have : m = j.1 := congrArg Fin.val h
          omega
        have e1 := hc i j hij (Or.inr hj)
        have e2 := hc p j hne (Or.inr hj)
        simp [b, hjp, e1, e2]
      rcases hor with h | h
      · have hi' : i = p := Fin.ext (by simp only [p]; omega)
        subst hi'
        have hjp : j < p := lt_of_le_of_ne (Fin.le_def.2 (by simp only [p]; omega)) (Ne.symm hij)
        have e : (g : Matrix (Fin n) (Fin n) k) p p * ((g : Matrix (Fin n) (Fin n) k) p j / (g : Matrix (Fin n) (Fin n) k) p p) =
            (g : Matrix (Fin n) (Fin n) k) p j := by field_simp
        simp only [ap, zero_mul, sub_zero, b, if_pos hjp, e, sub_self]
      · have hj' : j = p := Fin.ext (by simp only [p]; omega)
        subst hj'
        have hip : i < p := lt_of_le_of_ne (Fin.le_def.2 (by simp only [p]; omega)) hij
        have e : (g : Matrix (Fin n) (Fin n) k) i p / (g : Matrix (Fin n) (Fin n) k) p p * (g : Matrix (Fin n) (Fin n) k) p p =
            (g : Matrix (Fin n) (Fin n) k) i p := by field_simp
        simp only [bp, mul_zero, sub_zero, a, if_pos hip, e, sub_self]
    obtain ⟨u, hu, d, hd, c, hc', e⟩ := ih (by omega) (U⁻¹ * g * L⁻¹)
      (K.mul_mem (K.mul_mem (K.inv_mem hU.1) hg) (K.inv_mem hL.1)) hclean
    refine ⟨U * u, (K ⊓ unipB k (Fin n)).mul_mem hU hu, d, hd, c * L,
      (K ⊓ unipBLower k (Fin n)).mul_mem hc' hL, ?_⟩
    calc g = U * (U⁻¹ * g * L⁻¹) * L := by group
      _ = U * u * diagT k (Fin n) d * (c * L) := by rw [e]; group

end Fact

end UpperTheory.Gal.InertialTypesAlt.L

theorem UpperTheory.Gal.InertialTypesAlt.L.ballLev :
    UpperTheory.Gal.InertialTypesAlt.L.BallLev := by
  intro k _ _ _ _ n r h0 h1 K hK
  have hmem : ∀ g, g ∈ K ↔ g ∈ ball n r := fun g => by rw [← SetLike.mem_coe, hK]
  obtain ⟨K₀, e₀, ho, hc⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub k n r h0 h1
  have eK : (K : Set (GL (Fin n) k)) = K₀ := hK.trans e₀.symm
  refine ⟨⟨⟨eK ▸ hc, eK ▸ ho⟩, ?_, ?_, ?_⟩, fun t => ?_⟩
  · intro g hg
    exact UpperTheory.Gal.InertialTypesAlt.L.nat_mul_factorial_bound h1 K hK n le_rfl g hg fun i j _ h => by
      have := i.2
      have := j.2
      omega
  · intro t ht u hu
    obtain ⟨hu1, hu2⟩ := (mem_unipB k).1 hu.2
    have hur := (hmem u).1 hu.1
    refine (hmem _).2 fun i j => ?_
    rw [UpperTheory.Gal.InertialTypesAlt.L.conj_entry]
    rcases lt_trichotomy i j with h | h | h
    · rw [one_apply_ne h.ne, sub_zero]
      have := hur i j
      rw [one_apply_ne h.ne, sub_zero] at this
      exact (UpperTheory.Gal.InertialTypesAlt.L.val_le (ht i j h) _).trans this
    · subst h
      rw [hu2 i, mul_one, mul_inv_cancel₀ (t i).ne_zero, one_apply_eq, sub_self, map_zero]
      exact zero_le
    · rw [hu1 i j h, one_apply_ne h.ne']
      simp
  · intro t ht c hc'
    obtain ⟨hc1, hc2⟩ := UpperTheory.Gal.InertialTypesAlt.L.mem_low.1 hc'.2
    have hcr := (hmem c).1 hc'.1
    refine (hmem _).2 fun i j => ?_
    rw [UpperTheory.Gal.InertialTypesAlt.L.conj_entry']
    rcases lt_trichotomy i j with h | h | h
    · rw [hc1 i j h, one_apply_ne h.ne]
      simp
    · subst h
      rw [hc2 i, mul_one, mul_inv_cancel₀ (t i).ne_zero, one_apply_eq, sub_self, map_zero]
      exact zero_le
    · rw [one_apply_ne h.ne', sub_zero]
      have := hcr i j
      rw [one_apply_ne h.ne', sub_zero] at this
      exact (UpperTheory.Gal.InertialTypesAlt.L.val_le (ht j i h) _).trans this
  · ext g
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, (hmem a).1 ha, b, (hmem b).1 hb, t, rfl, e⟩
    · rintro ⟨a, ha, b, hb, s, hs, e⟩
      obtain rfl : s = t := hs
      exact ⟨a, (hmem a).2 ha, b, (hmem b).2 hb, e⟩
