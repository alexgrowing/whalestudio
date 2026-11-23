import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Artin

private theorem artin {P : Type} [Mul P] (T : Finset (P → ℂ)) : ∀ c : (P → ℂ) → ℂ,
    (∀ χ ∈ T, χ ≠ 0 ∧ ∀ p q, χ (p * q) = χ p * χ q) → (∀ p, ∑ χ ∈ T, c χ * χ p = 0) → ∀ χ ∈ T, c χ = 0 :=
  _root_.UpperTheory.Reformulated.B.Qh30.artin T

private theorem grp {P I : Type} [DecidableEq (P → ℂ)] (S : Finset I) (a : I → ℂ) (α : I → P → ℂ) (T : Finset (P → ℂ))
    (h : ∀ i ∈ S, α i ≠ 0 → α i ∈ T) (p : P) :
    ∑ χ ∈ T, (∑ i ∈ S.filter (fun i => α i = χ), a i) * χ p = ∑ i ∈ S, a i * α i p := by
  simp only [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases h0 : α i = 0
  · rw [h0]; simp only [Pi.zero_apply, mul_zero]
    refine Finset.sum_eq_zero fun χ _ => ?_
    split_ifs with e
    · subst e; simp
    · simp
  · rw [Finset.sum_eq_single (α i) (fun χ _ e => by simp [e.symm]) fun e => absurd (h i hi h0) e]; simp

theorem UpperTheory.V.Z.Sym.Tf.extract :
    UpperTheory.V.Z.Sym.Tf.Extract := by
  classical
  intro P I J _ S S' a b α β hα hβ h χ hχ hb
  by_contra hn
  push Not at hn
  set T := (S.image α ∪ S'.image β).filter (· ≠ 0) with hT
  have key := artin T (fun χ => ∑ i ∈ S.filter (fun i => α i = χ), a i - ∑ j ∈ S'.filter (fun j => β j = χ), b j)
    (fun ψ hψ => by
      simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image] at hψ
      refine ⟨hψ.2, ?_⟩
      rcases hψ.1 with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      exacts [hα i hi, hβ i hi])
    (fun p => by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [grp S a α T (fun i hi h0 => by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inl ⟨i, hi, rfl⟩, h0⟩),
        grp S' b β T (fun i hi h0 => by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inr ⟨i, hi, rfl⟩, h0⟩),
        h, sub_self])
  obtain ⟨j, hj, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hj' := Finset.mem_filter.1 hj
  have := key χ (by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inr ⟨j, hj'.1, hj'.2⟩, hχ⟩)
  rw [Finset.sum_eq_zero (s := S.filter _) fun i hi => by
    by_contra e; exact hn i (Finset.mem_filter.1 hi).1 e (Finset.mem_filter.1 hi).2, zero_sub, neg_eq_zero] at this
  exact hb (by convert this)
