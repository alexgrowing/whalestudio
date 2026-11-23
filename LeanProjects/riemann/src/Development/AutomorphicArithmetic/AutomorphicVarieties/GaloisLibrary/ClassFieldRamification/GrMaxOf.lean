import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.grMaxOf :
    ∀ (p : ℕ) [Fact p.Prime] (R G : Type) [CommRing R] [IsLocalRing R] [CommGroup G] [Finite G], (p : R) ∈ IsLocalRing.maximalIdeal R → IsPGroup p G → ∀ M : Ideal (MonoidAlgebra R G), M.IsMaximal → M = (IsLocalRing.maximalIdeal R).comap (aug R G) := by
  intro p _ R G _ _ _ _ hpm hG M hM
  classical
  have hcomap : M.comap (algebraMap R (MonoidAlgebra R G)) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  letI : Field (MonoidAlgebra R G ⧸ M) := Ideal.Quotient.field M
  have hpQ : ((p : ℕ) : MonoidAlgebra R G ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]
    have h0 : (p : R) ∈ M.comap (algebraMap R (MonoidAlgebra R G)) := by
      rw [hcomap]; exact hpm
    simpa using h0
  haveI : CharP (MonoidAlgebra R G ⧸ M) p := by
    have h := CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hpQ
    exact h ▸ ringChar.charP _
  have hg : ∀ g : G, Ideal.Quotient.mk M (MonoidAlgebra.single g 1) = 1 := by
    intro g
    obtain ⟨k, hk⟩ := hG g
    have h1 : (Ideal.Quotient.mk M (MonoidAlgebra.single g (1 : R)) - 1) ^ p ^ k = 0 := by
      rw [sub_pow_char_pow, one_pow, ← map_pow, MonoidAlgebra.single_pow, one_pow, hk,
        ← MonoidAlgebra.one_def, map_one, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mp h1)
  have hext : Ideal.Quotient.mkₐ R M = (Algebra.ofId R _).comp (aug R G) := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp [hg, aug_single]
    · exact Subsingleton.elim _ _
  have hle : (IsLocalRing.maximalIdeal R).comap (aug R G) ≤ M := by
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h3 := congrArg (fun f => f x) hext
    simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, Algebra.ofId_apply] at h3
    rw [h3, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
    have h2 : aug R G x ∈ M.comap (algebraMap R (MonoidAlgebra R G)) := by
      rw [hcomap]; exact hx
    exact h2
  haveI : ((IsLocalRing.maximalIdeal R).comap (aug R G)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (aug R G) (fun r => ⟨MonoidAlgebra.single 1 r, aug_single R G 1 r⟩)
  exact (Ideal.IsMaximal.eq_of_le this hM.ne_top hle).symm
