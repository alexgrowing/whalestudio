import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit

theorem UpperTheory.ConvolutionTheory.T.goodEx :
    UpperTheory.ConvolutionTheory.T.GoodEx := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set S : ℤ := ∑ k : Fin m, ((m : ℤ) + 1 - (k : ℕ)) with hS
  have hS0 : 0 ≤ S := by
    refine Finset.sum_nonneg fun k _ => ?_
    have := k.isLt
    omega
  let ν : Fin (m + 1) → ℤ := fun i => if i = Fin.last m then -S else (m : ℤ) + 1 - (i : ℕ)
  have hlast : ν (Fin.last m) = -S := by simp [ν]
  have hcast : ∀ k : Fin m, ν k.castSucc = (m : ℤ) + 1 - (k : ℕ) := by
    intro k
    have : k.castSucc ≠ Fin.last m := (Fin.castSucc_lt_last k).ne
    simp [ν, this]
  have hne : ∀ i : Fin (m + 1), i ≠ Fin.last m → ν i = (m : ℤ) + 1 - (i : ℕ) := by
    intro i hi
    simp [ν, hi]
  have hpos : ∀ i : Fin (m + 1), i ≠ Fin.last m → 0 < ν i := by
    intro i hi
    rw [hne i hi]
    have := i.isLt
    omega
  have hsum : ∑ i, ν i = 0 := by
    rw [Fin.sum_univ_castSucc, hlast]
    simp only [hcast]
    rw [← hS]
    ring
  have hJ : ∀ J : Finset (Fin (m + 1)), J.Nonempty → Fin.last m ∉ J → 0 < ∑ i ∈ J, ν i := by
    intro J hJ hl
    refine Finset.sum_pos (fun i hi => hpos i ?_) hJ
    rintro rfl
    exact hl hi
  refine ⟨ν, ?_, hsum, ?_⟩
  · intro i j hij
    by_cases hj : j = Fin.last m
    · have hi : i ≠ Fin.last m := by
        rintro rfl
        subst hj
        exact lt_irrefl _ hij
      have h1 := hpos i hi
      have h2 : ν j = -S := by rw [hj, hlast]
      show ν j < ν i
      omega
    · have hi : i ≠ Fin.last m := by
        rintro rfl
        exact absurd (Fin.le_last j) (not_le.mpr hij)
      show ν j < ν i
      rw [hne i hi, hne j hj]
      have : (i : ℕ) < (j : ℕ) := hij
      omega
  · intro J hJne hJu
    by_cases hl : Fin.last m ∈ J
    · have hc : Jᶜ.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact hJu (by simpa using h)
      have h1 := hJ Jᶜ hc (by simpa using hl)
      have h2 : ∑ i ∈ J, ν i + ∑ i ∈ Jᶜ, ν i = 0 := by
        rw [Finset.sum_add_sum_compl, hsum]
      omega
    · exact (hJ J hJne hl).ne'
