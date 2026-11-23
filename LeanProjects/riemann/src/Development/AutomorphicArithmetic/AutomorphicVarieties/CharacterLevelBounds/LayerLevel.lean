import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevChange

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem UpperTheory.V.Chr.layerLevel_emb (n : ℕ) [NeZero n] (K L C : Type) [Field K] [Field L] [Field C] [Algebra K L]
    [Algebra K C] [IsCyclotomicExtension {n} K L] (ζ : C) (hζ : IsPrimitiveRoot ζ n) : Nonempty (L →ₐ[K] C) := by
  haveI : Polynomial.IsSplittingField K L (Polynomial.X ^ n - 1) :=
    IsCyclotomicExtension.isSplittingField_X_pow_sub_one (n := n) (K := K) (L := L)
  have hs : Polynomial.Splits ((Polynomial.X ^ n - 1 : Polynomial K).map (algebraMap K C)) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
      ← Polynomial.C_1]
    exact Polynomial.X_pow_sub_one_splits hζ
  exact ⟨Polynomial.IsSplittingField.lift L _ hs⟩

theorem UpperTheory.V.Chr.layerLevel :
    ∀ (A : AbF) (l j : ℕ), l.Prime → ∀ (L₀ : Type) [Field L₀] [NumberField L₀] (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁],
          IsAbField A L₀ → IsLayer l j L₀ L₁ → ∃ (N : ℕ) (_ : NeZero N) (H : Subgroup (ZMod N)ˣ), HasLevel L₁ N H := by
  intro A l j hl L₀ _ _ L₁ _ _ _ hA hL
  obtain ⟨N, hN, jj, ζ, -, hζ, -⟩ := hA
  obtain ⟨⟨k, hk⟩, -⟩ := hL
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI hN' : NeZero (N * l ^ k) := ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (((N * l ^ k : ℕ)) : ℚ) := ⟨by exact_mod_cast NeZero.ne (N * l ^ k)⟩
  obtain ⟨r, hr⟩ := @IsCyclotomicExtension.exists_isPrimitiveRoot {N * l ^ k} ℚ
    (CyclotomicField (N * l ^ k) ℚ) _ _ _ (CyclotomicField.isCyclotomicExtension (N * l ^ k) ℚ)
    (N * l ^ k) rfl (NeZero.ne _)
  have hrN : IsPrimitiveRoot (r ^ (l ^ k)) N := by
    have h0 := hr.pow_of_dvd (pow_ne_zero k hl.ne_zero) (dvd_mul_left _ N)
    rwa [Nat.mul_div_cancel _ (pow_pos hl.pos k)] at h0
  have hrl : IsPrimitiveRoot (r ^ N) (l ^ k) := by
    have h0 := hr.pow_of_dvd (NeZero.ne N) (dvd_mul_right N _)
    rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N))] at h0
  obtain ⟨g⟩ := @layerLevel_emb N _ ℚ (CyclotomicField N ℚ) (CyclotomicField (N * l ^ k) ℚ)
    _ _ _ _ _ (CyclotomicField.isCyclotomicExtension N ℚ) _ hrN
  letI : Algebra L₀ (CyclotomicField (N * l ^ k) ℚ) :=
    ((g : CyclotomicField N ℚ →+* CyclotomicField (N * l ^ k) ℚ).comp
      (jj : L₀ →+* CyclotomicField N ℚ)).toAlgebra
  obtain ⟨h1⟩ := layerLevel_emb (l ^ k) L₀ L₁ (CyclotomicField (N * l ^ k) ℚ) (r ^ N) hrl
  obtain ⟨H, hH⟩ := (levChange L₁ (N * l ^ k)).1
    ⟨(h1 : L₁ →+* CyclotomicField (N * l ^ k) ℚ).toRatAlgHom⟩
  exact ⟨N * l ^ k, hN', H, hH⟩
