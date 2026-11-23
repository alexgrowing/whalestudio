import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.UnitaryCorrection

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_of_eq {x : L} {u : Multiplicative ℤ}
    (h : Valued.v x = (u : WithZero (Multiplicative ℤ))) :
    ordL x = -Multiplicative.toAdd u := by
  have h0 : Valued.v x ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  unfold ordL
  rw [dif_neg h0]
  congr 2
  apply WithZero.coe_injective
  rw [WithZero.coe_unzero, h]

theorem ordL_mul_of_ne {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordL (a * b) = ordL a + ordL b := by
  have ha' : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hb' : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 ha'
  obtain ⟨w, hw⟩ := WithZero.ne_zero_iff_exists.1 hb'
  have hab : Valued.v (a * b) = ((u * w : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_mul, ← hu, ← hw, WithZero.coe_mul]
  rw [ordL_of_eq hab, ordL_of_eq hu.symm, ordL_of_eq hw.symm, toAdd_mul]
  ring

theorem ordL_congr {a b : L} (h : Valued.v a = Valued.v b) : ordL a = ordL b := by
  unfold ordL
  simp only [h]

theorem ordL_one : ordL (1 : L) = 0 := by
  have h : Valued.v (1 : L) = ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_one, WithZero.coe_one]
  rw [ordL_of_eq h]
  simp

theorem val_mul_entry_le {ι : Type} [Fintype ι] {A B : Matrix ι ι L}
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hB : ∀ i j, Valued.v (B i j) ≤ 1) (i j : ι) :
    Valued.v ((A * B) i j) ≤ 1 := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_one' (hA i k) (hB k j)

end Val

section Anti

variable {L : Type} [Field L]

theorem antiJ_apply {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if j = Fin.rev i then 1 else 0 := by
  have : (i.val + j.val + 1 = n) ↔ j = Fin.rev i := by
    rw [Fin.ext_iff, Fin.val_rev]
    have := i.isLt
    have := j.isLt
    omega
  simp only [antiJ, this]

theorem antiJ_mul_self (n : ℕ) : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · rw [antiJ_apply, antiJ_apply, if_pos rfl, one_mul, Matrix.one_apply, Fin.rev_rev]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  · intro k _ hk
    rw [antiJ_apply, if_neg hk, zero_mul]
  · simp

theorem cT_antiJ (σ : L →+* L) (n : ℕ) : cT σ (antiJ L n) = antiJ L n := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, antiJ_apply]
  by_cases h : j = Fin.rev i
  · subst h
    simp
  · have h' : ¬ i = Fin.rev j := fun e => h (by rw [e, Fin.rev_rev])
    simp [h, h']

theorem cT_diag_conj {ι : Type} [Fintype ι] [DecidableEq ι] (σ : L →+* L) (s : ι → L)
    (H : Matrix ι ι L) (i j : ι) :
    (cT σ (diagonal s) * H * diagonal s) i j = σ (s i) * H i j * s j := by
  have : cT σ (diagonal s) = diagonal fun i => σ (s i) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [this, Matrix.mul_diagonal, Matrix.diagonal_mul]

end Anti

section Core

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_diag_unit (σ : L →+* L) (hσσ : ∀ x, σ (σ x) = x)
    (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (hyp : ∀ c : L, σ c = c → Valued.v c = 1 → ∃ s : L, Valued.v s = 1 ∧ σ s * s = c)
    {n : ℕ} (H H' : Matrix (Fin n) (Fin n) L) (hHH : H * H' = 1)
    (hI : ∀ i j, Valued.v (H i j) ≤ 1) (hI' : ∀ i j, Valued.v (H' i j) ≤ 1)
    (hsupp : ∀ i j, H i j ≠ 0 → j = Fin.rev i)
    (hherm : ∀ i j, σ (H j i) = H i j) :
    ∃ s : Fin n → L, (∀ i, Valued.v (s i) = 1) ∧
      ∀ i, σ (s i) * H i (Fin.rev i) * s (Fin.rev i) = 1 := by
  have hprod : ∀ i, H i (Fin.rev i) * H' (Fin.rev i) i = 1 := by
    intro i
    have h1 : (H * H') i i = 1 := by rw [hHH, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)] at h1
    · exact h1
    · intro k _ hk
      have : H i k = 0 := by
        by_contra h
        exact hk (hsupp i k h)
      rw [this, zero_mul]
    · simp
  have hv : ∀ i, Valued.v (H i (Fin.rev i)) = 1 := by
    intro i
    refine le_antisymm (hI _ _) ?_
    have h2 : Valued.v (H i (Fin.rev i)) * Valued.v (H' (Fin.rev i) i) = 1 := by
      rw [← map_mul, hprod, map_one]
    calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (H i (Fin.rev i)) * Valued.v (H' (Fin.rev i) i) := h2.symm
      _ ≤ Valued.v (H i (Fin.rev i)) * 1 := mul_le_mul_right (hI' _ _) _
      _ = Valued.v (H i (Fin.rev i)) := mul_one _
  have hne : ∀ i, H i (Fin.rev i) ≠ 0 := by
    intro i h
    have := hv i
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hs : ∀ i, σ (H i (Fin.rev i)) = H (Fin.rev i) i := fun i => hherm (Fin.rev i) i
  have hmid : ∀ i, i = Fin.rev i →
      ∃ s : L, Valued.v s = 1 ∧ σ s * s = (H i (Fin.rev i))⁻¹ := by
    intro i hi
    refine hyp _ ?_ ?_
    · rw [map_inv₀, hs i]
      have e : H (Fin.rev i) i = H i (Fin.rev i) := by
        rw [← hi]
      rw [e]
    · rw [map_inv₀, hv i, inv_one]
  choose! r hr1 hr2 using hmid
  refine ⟨fun i => if i < Fin.rev i then 1 else
    if Fin.rev i < i then (H (Fin.rev i) i)⁻¹ else r i, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with h1 h2
    · exact map_one _
    · have := hv (Fin.rev i)
      rw [Fin.rev_rev] at this
      rw [map_inv₀, this, inv_one]
    · exact hr1 i (le_antisymm (not_lt.1 h2) (not_lt.1 h1))
  · intro i
    rcases lt_trichotomy i (Fin.rev i) with h | h | h
    · have h1 : ¬ Fin.rev i < Fin.rev (Fin.rev i) := by
        rw [Fin.rev_rev]; exact not_lt.2 h.le
      have h2 : Fin.rev (Fin.rev i) < Fin.rev i := by rw [Fin.rev_rev]; exact h
      dsimp only
      rw [if_pos h, if_neg h1, if_pos h2, Fin.rev_rev, map_one, one_mul]
      exact mul_inv_cancel₀ (hne i)
    · have h1 : ¬ i < Fin.rev i := not_lt.2 h.ge
      have h2 : ¬ Fin.rev i < i := not_lt.2 h.le
      have a1 : ¬ Fin.rev i < Fin.rev (Fin.rev i) := by rw [Fin.rev_rev]; exact h2
      have a2 : ¬ Fin.rev (Fin.rev i) < Fin.rev i := by rw [Fin.rev_rev]; exact h1
      have a3 : r (Fin.rev i) = r i := congrArg r h.symm
      dsimp only
      rw [if_neg h1, if_neg h2, if_neg a1, if_neg a2, a3]
      have := hr2 i h
      calc σ (r i) * H i (Fin.rev i) * r i = (σ (r i) * r i) * H i (Fin.rev i) := by ring
        _ = 1 := by rw [this]; exact inv_mul_cancel₀ (hne i)
    · have h1 : ¬ i < Fin.rev i := not_lt.2 h.le
      have h2 : Fin.rev i < Fin.rev (Fin.rev i) := by rw [Fin.rev_rev]; exact h
      dsimp only
      rw [if_neg h1, if_pos h, if_pos h2, mul_one, map_inv₀, hherm i (Fin.rev i)]
      exact inv_mul_cancel₀ (hne i)

end Core

theorem main : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → (∀ c : L, σ c = c → Valued.v c = 1 → ∃ s : L, Valued.v s = 1 ∧ σ s * s = c) → ∀ (n : ℕ) (y : Fin n → ℤ), Function.Injective y → (∀ i, y (Fin.rev i) = -y i) → ∀ (d : Fin n → Lˣ), (∀ i, ordL (d i : L) = y i) → ∀ m : GL (Fin n) L, (∀ i j, Valued.v (m.val i j) ≤ 1) → (∀ i j, Valued.v ((m⁻¹).val i j) ≤ 1) → m * GlobalTheory.SmGL.diagT L (Fin n) d * m⁻¹ ∈ UJ σ (antiJ L n) → ∃ s : Fin n → Lˣ, (∀ i, Valued.v (s i : L) = 1) ∧ m * GlobalTheory.SmGL.diagT L (Fin n) s ∈ UJ σ (antiJ L n) := by
  intro L _ _ σ hσσ hσv hyp n y hy hrev d hd m hm hm' hU
  set M : Matrix (Fin n) (Fin n) L := m.val with hMdef
  set M' : Matrix (Fin n) (Fin n) L := (m⁻¹).val with hM'def
  set J := antiJ L n with hJdef
  have hMM' : M * M' = 1 := by rw [hMdef, hM'def, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hM'M : M' * M = 1 := by rw [hMdef, hM'def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcc : cT σ M * cT σ M' = 1 := by rw [← cT_mul, hM'M, cT_one]
  have hcc' : cT σ M' * cT σ M = 1 := by rw [← cT_mul, hMM', cT_one]
  have hJJ : J * J = 1 := antiJ_mul_self n
  have hJc : cT σ J = J := cT_antiJ σ n
  have hJI : ∀ i j, Valued.v (J i j) ≤ 1 := by
    intro i j
    rw [hJdef, antiJ_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le_one
  have hcI : ∀ (A : Matrix (Fin n) (Fin n) L), (∀ i j, Valued.v (A i j) ≤ 1) →
      ∀ i j, Valued.v (cT σ A i j) ≤ 1 := by
    intro A hA i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [hσv]
    exact hA j i
  set D : Matrix (Fin n) (Fin n) L := diagonal fun i => (d i : L) with hDdef
  have hUm : cT σ (M * D * M') * J * (M * D * M') = J := by
    have h := hU
    change cT σ ((m * GlobalTheory.SmGL.diagT L (Fin n) d * m⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * J *
      ((m * GlobalTheory.SmGL.diagT L (Fin n) d * m⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = J at h
    rwa [Units.val_mul, Units.val_mul, GlobalTheory.SmGL.val_diagT] at h
  set H : Matrix (Fin n) (Fin n) L := cT σ M * J * M with hHdef
  have hDH : cT σ D * H * D = H := by
    calc cT σ D * H * D
        = (cT σ M * cT σ M') * (cT σ D * cT σ M * J * M * D) * (M' * M) := by
          rw [hcc, hM'M, hHdef]; simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = cT σ M * (cT σ (M * D * M') * J * (M * D * M')) * M := by
          simp only [cT_mul, Matrix.mul_assoc]
      _ = H := by rw [hUm]
  have hentry : ∀ i j, σ (d i : L) * H i j * (d j : L) = H i j := by
    intro i j
    rw [← cT_diag_conj σ (fun i => (d i : L)) H i j, ← hDdef, hDH]
  have hsupp : ∀ i j, H i j ≠ 0 → j = Fin.rev i := by
    intro i j hij
    have h1 : σ (d i : L) * (d j : L) = 1 := by
      have h2 := hentry i j
      have h3 : H i j * (σ (d i : L) * (d j : L)) = H i j * 1 := by
        rw [mul_one]
        calc H i j * (σ (d i : L) * (d j : L)) = σ (d i : L) * H i j * (d j : L) := by ring
          _ = H i j := h2
      exact mul_left_cancel₀ hij h3
    have hσd : σ (d i : L) ≠ 0 := by
      intro h
      have := hσv (d i : L)
      rw [h, map_zero] at this
      exact (d i).ne_zero ((Valuation.zero_iff _).1 this.symm)
    have h4 := ordL_mul_of_ne hσd (d j).ne_zero
    rw [h1, ordL_one, ordL_congr (hσv _), hd, hd] at h4
    apply hy
    rw [hrev]
    omega
  have hherm : ∀ i j, σ (H j i) = H i j := by
    have hcH : cT σ H = H := by
      have hcc2 : cT σ (cT σ M) = M := by
        ext a b
        simp [cT, hσσ]
      rw [hHdef, cT_mul, cT_mul, hcc2, hJc, Matrix.mul_assoc]
    intro i j
    have := congrFun (congrFun hcH i) j
    simpa [cT] using this
  have hHH : H * (M' * J * cT σ M') = 1 := by
    calc H * (M' * J * cT σ M')
        = cT σ M * J * (M * M') * J * cT σ M' := by
          rw [hHdef]; simp only [Matrix.mul_assoc]
      _ = cT σ M * (J * J) * cT σ M' := by
          rw [hMM']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hJJ, Matrix.mul_one, hcc]
  have hI : ∀ i j, Valued.v (H i j) ≤ 1 :=
    val_mul_entry_le (val_mul_entry_le (hcI M hm) hJI) hm
  have hI' : ∀ i j, Valued.v ((M' * J * cT σ M') i j) ≤ 1 :=
    val_mul_entry_le (val_mul_entry_le hm' hJI) (hcI M' hm')
  obtain ⟨s, hs1, hs2⟩ := exists_diag_unit σ hσσ hσv hyp H _ hHH hI hI' hsupp hherm
  have hs0 : ∀ i, s i ≠ 0 := by
    intro i h
    have := hs1 i
    rw [h, map_zero] at this
    exact zero_ne_one this
  refine ⟨fun i => Units.mk0 (s i) (hs0 i), fun i => hs1 i, ?_⟩
  change cT σ ((m * GlobalTheory.SmGL.diagT L (Fin n) _ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * J *
    ((m * GlobalTheory.SmGL.diagT L (Fin n) _ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = J
  rw [Units.val_mul, GlobalTheory.SmGL.val_diagT]
  have hval : (fun i => ((Units.mk0 (s i) (hs0 i) : Lˣ) : L)) = s := by
    ext i
    rfl
  rw [hval, cT_mul]
  have hre : cT σ (diagonal s) * cT σ M * J * (M * diagonal s) = cT σ (diagonal s) * H * diagonal s := by
    rw [hHdef]; simp only [Matrix.mul_assoc]
  rw [hre]
  ext i j
  rw [cT_diag_conj, hJdef, antiJ_apply]
  by_cases hj : j = Fin.rev i
  · subst hj
    rw [if_pos rfl]
    exact hs2 i
  · rw [if_neg hj]
    have : H i j = 0 := by
      by_contra h
      exact hj (hsupp i j h)
    rw [this, mul_zero, zero_mul]

end GlobalTheory.CompanionTheory.UnitaryCorrection
