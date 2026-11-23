import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private lemma corG_sum_log (n : ℤ) (hn : n ≠ 0) (Ls : Finset Nat.Primes) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ) ≤ Real.log |(n : ℝ)| := by
  classical
  have hdvd : ∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ (padicValInt l n) ∣ n := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      simp only [Function.onFun]
      apply IsCoprime.pow
      rw [Nat.isCoprime_iff_coprime]
      exact (Nat.coprime_primes a.2 b.2).mpr (fun h => hab (Subtype.ext h))
    · intro l _
      haveI : Fact (Nat.Prime l) := ⟨l.2⟩
      exact padicValInt_dvd n
  have hP : (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ (padicValInt l n)) ≤ |(n : ℝ)| := by
    have h1 := Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs _ _).mpr hdvd)
    have h2 : ((∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ (padicValInt l n) : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    exact h2
  have hpos : ∀ l ∈ Ls, (0 : ℝ) < ((l : ℕ) : ℝ) ^ (padicValInt l n) :=
    fun l _ => pow_pos (by exact_mod_cast l.2.pos) _
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ)
      = ∑ l ∈ Ls, Real.log (((l : ℕ) : ℝ) ^ (padicValInt l n)) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [Real.log_pow]
        ring
    _ = Real.log (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ (padicValInt l n)) :=
        (Real.log_prod (fun l hl => (hpos l hl).ne')).symm
    _ ≤ Real.log |(n : ℝ)| := Real.log_le_log (Finset.prod_pos hpos) hP

theorem UpperTheory.V.U3.corGK :
    PropGK → CorGK := by
  intro hP K _ _
  obtain ⟨c₅, A, hK⟩ := hP K
  refine ⟨c₅, A, ?_⟩
  intro Ω _ _ _ _ e N _ H p p' hp hp' hne hd hd' c Ls hL
  rcases Ls.eq_empty_or_nonempty with rfl | ⟨l₀, hl₀⟩
  · refine ⟨by simp, ?_⟩
    rw [Finset.sum_empty]
    have h1 := Real.log_natCast_nonneg p
    have h2 := Real.log_natCast_nonneg p'
    positivity
  have he : 1 ≤ e := by
    obtain ⟨ψ, _, h⟩ := hL l₀ hl₀
    exact h.e_pos
  obtain ⟨n, hn, hb, h⟩ := hK e N H p he hp hd
  obtain ⟨n', hn', hb', h'⟩ := hK e N H p' he hp' hd'
  have key : ∀ l ∈ Ls, (∀ ψ ∈ orb (c l) H, Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ ψ ∈ orb (c l) H, Vn Ω (c l) e ψ ≤ 2 * (padicValInt l n : ℝ) + 2 * (padicValInt l n' : ℝ) := by
    intro l hl
    have a1 : (0 : ℝ) ≤ (padicValInt l n : ℝ) := Nat.cast_nonneg _
    have a2 : (0 : ℝ) ≤ (padicValInt l n' : ℝ) := Nat.cast_nonneg _
    by_cases hlp : (l : ℕ) = p
    · have hlp' : (l : ℕ) ≠ p' := fun x => hne (hlp.symm.trans x)
      obtain ⟨b1, b2⟩ := h' Ω l hlp' (c l) (hL l hl)
      exact ⟨b1, by linarith⟩
    · obtain ⟨b1, b2⟩ := h Ω l hlp (c l) (hL l hl)
      exact ⟨b1, by linarith⟩
  refine ⟨fun l hl => (key l hl).1, ?_⟩
  have s1 := corG_sum_log n hn Ls
  have s2 := corG_sum_log n' hn' Ls
  calc _ ≤ ∑ l ∈ Ls, Real.log (l : ℕ) * (2 * (padicValInt l n : ℝ) + 2 * (padicValInt l n' : ℝ)) :=
        Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (key l hl).2 (Real.log_natCast_nonneg _)
    _ = 2 * ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ) + 2 * ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n' : ℝ) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ _ := by nlinarith
