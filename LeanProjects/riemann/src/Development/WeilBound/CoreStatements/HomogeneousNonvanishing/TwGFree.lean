import Mathlib
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem free_semilocal (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R] [Module.Finite A R] :
    Finite (MaximalSpectrum R) := by
  haveI := (Algebra.QuasiFinite.finite_primesOver (R := A) (S := R)
    (IsLocalRing.maximalIdeal A)).to_subtype
  have hover : ∀ P : MaximalSpectrum R, IsLocalRing.maximalIdeal A = Ideal.under A P.asIdeal :=
    fun P =>
      haveI := P.isMaximal
      (IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) P.asIdeal)).symm
  exact Finite.of_injective (β := ↥((IsLocalRing.maximalIdeal A).primesOver R))
    (fun P => ⟨P.asIdeal, P.isMaximal.isPrime, Ideal.LiesOver.mk (hover P)⟩)
    (fun P Q h => MaximalSpectrum.ext (congrArg Subtype.val h))

theorem free_rank (B K L : Type) [CommRing B] [IsDomain B] [Field K] [Algebra B K] [AddCommGroup L] [Module B L]
    [Module.Finite B L] [Module.Projective B L] : Module.finrank K (K ⊗[B] L) = Module.finrank B L := by
  haveI : Module.Flat B L := Module.Flat.of_projective
  haveI : Module.Free K (K ⊗[B] L) := Module.Free.of_divisionRing K _
  have hstalk : ∀ q : PrimeSpectrum B, Module.rankAtStalk L q = Module.finrank B L := by
    intro q
    have hle := Ideal.primeCompl_le_nonZeroDivisors q.asIdeal
    show Module.finrank (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl L) = _
    rw [IsLocalization.finrank_eq (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl hle,
      IsLocalizedModule.finrank_eq q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl L) hle]
  have hK := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := K ⊗[B] L))
    (IsLocalRing.closedPoint K)
  rw [Module.rankAtStalk_baseChange, hstalk] at hK
  simp only [Pi.natCast_apply, Nat.cast_id] at hK
  exact hK.symm

theorem tw_g_free : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (L : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L], ∃ φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (Fin (Module.finrank (𝓞 E) L) → ℤ_[p] ⊗[ℤ] 𝓞 E), ∀ (z : ℤ_[p]) (a : 𝓞 E) (x : L), φ (z ⊗ₜ (a • x)) = ((1 : ℤ_[p]) ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] 𝓞 E) • φ (z ⊗ₜ x) := by
  intro E _ _ p _ L _ _ _ _
  haveI : Module.Flat (𝓞 E) L := Module.Flat.of_projective
  haveI : Module.Finite ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) := Module.Finite.base_change ℤ ℤ_[p] (𝓞 E)
  haveI : Finite (MaximalSpectrum (ℤ_[p] ⊗[ℤ] 𝓞 E)) :=
    PositivityTheory.UnitarySelfGeneration.free_semilocal ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)
  haveI : Module.Flat (ℤ_[p] ⊗[ℤ] 𝓞 E) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L) :=
    Module.Flat.baseChange (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) L
  haveI : Module.Finite (ℤ_[p] ⊗[ℤ] 𝓞 E) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L) :=
    Module.Finite.base_change (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) L
  haveI : Algebra.IsPushout ℤ ℤ_[p] (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) := TensorProduct.isPushout
  have hrank : ∀ P : MaximalSpectrum (ℤ_[p] ⊗[ℤ] 𝓞 E),
      Module.finrank ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal)
        (((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) ⊗[ℤ_[p] ⊗[ℤ] 𝓞 E] ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L)) =
        Module.finrank (𝓞 E) L := by
    intro P
    haveI := P.isMaximal
    letI : Field ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E)
      ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) L).finrank_eq.trans
      (PositivityTheory.UnitarySelfGeneration.free_rank (𝓞 E) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) L)
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (ℤ_[p] ⊗[ℤ] 𝓞 E)
    ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L) _ hrank
  refine ⟨(Algebra.IsPushout.cancelBaseChange ℤ ℤ_[p] (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) L).symm.trans
    (b.equivFun.restrictScalars ℤ_[p]), ?_⟩
  intro z a x
  have key : (algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) z) ⊗ₜ[𝓞 E] (a • x) =
      ((1 : ℤ_[p]) ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] 𝓞 E) • ((algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) z) ⊗ₜ[𝓞 E] x) := by
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul,
      Algebra.TensorProduct.right_algebraMap_apply]
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, key, map_smul]

end PositivityTheory.UnitarySelfGeneration
