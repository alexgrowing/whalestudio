import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

namespace GlobalTheory.GroupBplus

theorem exists_algHom_comp_eq {A K C : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing C] [Algebra A C] [Algebra.IsIntegral A C] (f : C →ₐ[A] K) :
    ∃ g : C →ₐ[A] A, (Algebra.ofId A K).comp g = f := by
  have h : ∀ c, f c ∈ (⊥ : Subalgebra A K) := fun c => by
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp ((Algebra.IsIntegral.isIntegral (R := A) c).map f)
    exact Algebra.mem_bot.2 ⟨a, ha⟩
  let e := Algebra.botEquivOfInjective (IsFractionRing.injective A K)
  refine ⟨e.toAlgHom.comp (f.codRestrict ⊥ h), ?_⟩
  ext c
  have h1 := congrArg Subtype.val (e.symm.commutes (e (f.codRestrict ⊥ h c)))
  rw [Algebra.algebraMap_self, RingHom.id_apply, AlgEquiv.symm_apply_apply] at h1
  exact h1.symm

end GlobalTheory.GroupBplus
