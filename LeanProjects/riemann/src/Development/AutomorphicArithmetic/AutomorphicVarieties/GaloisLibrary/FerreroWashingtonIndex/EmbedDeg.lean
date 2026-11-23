import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EmbCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwHom

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem totient_prime_pow_add_le_pow_mul_totient (l : ℕ) (hl : l.Prime) (n k : ℕ) :
    (l ^ (n + k)).totient ≤ l ^ k * (l ^ n).totient := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using Nat.totient_le (l ^ k)
  · rw [Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl hn]
    have : n + k - 1 = k + (n - 1) := by omega
    rw [this, pow_add, mul_assoc]

theorem UpperTheory.V.FW.embed :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K], ∃ f D : ℕ, f.Coprime l ∧ 1 < f ∧ ∀ (n n₀ : ℕ) (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [IsCyclotomicExtension {l ^ n} K K'], ∃ (m : ℕ) (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K' L) (_ : IsCyclotomicExtension {f * l ^ m} ℚ L), n₀ ≤ m ∧ Module.finrank K' L ≤ D * l ^ n₀ := by
  intro l hl K _ _ _
  have hp : l.Prime := hl.out
  obtain ⟨N, hN, ⟨φ⟩⟩ := CF.kwHom K
  obtain ⟨e, f₀, hf₀, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hp.one_lt.ne'
  have hf₀c : f₀.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).2 hf₀).symm
  have hf₀pos : 0 < f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · simp [h] at hN
    · exact h
  have hlc : (l + 1).Coprime l := by
    simp
  refine ⟨f₀ * (l + 1), f₀ * (l + 1) * l ^ e, Nat.Coprime.mul hf₀c hlc, ?_, ?_⟩
  · have : 1 < l + 1 := by have := hp.one_lt; omega
    calc 1 < l + 1 := this
      _ ≤ f₀ * (l + 1) := Nat.le_mul_of_pos_left _ hf₀pos
  intro n n₀ K' _ _ _ _
  set m := n + (e + n₀) with hm
  set M := f₀ * (l + 1) * l ^ m with hM
  have hMpos : 0 < M := by
    have := hp.pos
    positivity
  haveI : NeZero M := ⟨hMpos.ne'⟩
  let L := CyclotomicField M K'
  haveI : Module.Finite K' L := IsCyclotomicExtension.finite {M} K' L
  haveI : NumberField L := NumberField.of_module_finite K' L
  have hdvdN : l ^ e * f₀ ∣ M := by
    refine ⟨(l + 1) * l ^ (n + n₀), ?_⟩
    rw [hM, hm]
    ring
  have hdvdm : l ^ n ∣ M := by
    refine ⟨f₀ * (l + 1) * l ^ (e + n₀), ?_⟩
    rw [hM, hm]
    ring
  have hcyc : IsCyclotomicExtension {M} ℚ L :=
    embCyc (l ^ e * f₀) (l ^ n) M K K' L hdvdN hdvdm ⟨φ⟩
  refine ⟨m, L, inferInstance, inferInstance, inferInstance, hcyc, by omega, ?_⟩
  have hL : Module.finrank ℚ L = M.totient := IsCyclotomicExtension.Rat.finrank M L
  have hlnpos : 0 < l ^ n := pow_pos hp.pos n
  have hK' : (l ^ n).totient ≤ Module.finrank ℚ K' := by
    have hz := IsCyclotomicExtension.zeta_spec (l ^ n) K K'
    have h1 := Polynomial.cyclotomic_eq_minpoly_rat hz hlnpos
    have h2 := minpoly.natDegree_le (A := ℚ) (IsCyclotomicExtension.zeta (l ^ n) K K')
    rw [← h1, Polynomial.natDegree_cyclotomic] at h2
    exact h2
  have htow := Module.finrank_mul_finrank ℚ K' L
  have htot : M.totient ≤ f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := by
    have hco : (f₀ * (l + 1)).Coprime (l ^ m) := (Nat.Coprime.mul hf₀c hlc).pow_right m
    rw [hM, Nat.totient_mul hco]
    calc (f₀ * (l + 1)).totient * (l ^ m).totient ≤ f₀ * (l + 1) * (l ^ m).totient :=
          Nat.mul_le_mul_right _ (Nat.totient_le _)
      _ ≤ f₀ * (l + 1) * (l ^ (e + n₀) * (l ^ n).totient) :=
          Nat.mul_le_mul_left _ (totient_prime_pow_add_le_pow_mul_totient l hp n (e + n₀))
      _ = f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := by
          rw [pow_add]
          ring
  have htpos : 0 < (l ^ n).totient := Nat.totient_pos.2 hlnpos
  refine Nat.le_of_mul_le_mul_right ?_ htpos
  calc Module.finrank K' L * (l ^ n).totient ≤ Module.finrank K' L * Module.finrank ℚ K' :=
        Nat.mul_le_mul_left _ hK'
    _ = M.totient := by rw [mul_comm, htow, hL]
    _ ≤ f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := htot
