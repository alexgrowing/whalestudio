import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denint

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem primorial_dvd_fact (n : ℕ) : primorial n ∣ n.factorial := by
  rw [primorial, ← Finset.prod_Ico_id_eq_factorial]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  simp only [Finset.mem_Ico]
  exact ⟨hp.2.one_lt.le, hp.1⟩

private theorem denY_Ek (N k : ℕ) (hN : 0 < N) (hk : 1 ≤ k) (b : ZMod N) :
    ∃ z : ℤ, (z : ℚ) = (denY N k : ℚ) * Ek N k b := by
  obtain ⟨z, hz⟩ := b_denint N k b.val hN
  obtain ⟨c, hc⟩ := primorial_dvd_fact (k + 1)
  refine ⟨c * z, ?_⟩
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  simp only [denY, Ek, den] at hz ⊢
  push_cast [hc] at hz ⊢
  rw [← hz]
  field_simp

theorem UpperTheory.V.B5.exists_int_higherStickelbergerDenom_smul :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 1 ≤ k → ∃ z : MonoidAlgebra ℤ Γ, coefMap ℚ Γ z = (denY N k : ℚ) • yEl k a ha π := by
  intro N _ Γ _ π a ha k hk
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  choose w hw using fun b : ZMod N => denY_Ek N k hN hk b
  refine ⟨(1 - MonoidAlgebra.single (π (ZMod.unitOfCoprime a ha))⁻¹ ((a : ℤ) ^ k)) *
    -∑ b : (ZMod N)ˣ, MonoidAlgebra.single (π b)⁻¹ (w b), ?_⟩
  simp only [yEl, thetaEl, sumEl, map_mul, map_sub, map_one, map_neg, map_sum, coefMap_single, hw]
  push_cast
  rw [← mul_smul_comm, smul_neg, Finset.smul_sum]
  simp only [MonoidAlgebra.smul_single']
