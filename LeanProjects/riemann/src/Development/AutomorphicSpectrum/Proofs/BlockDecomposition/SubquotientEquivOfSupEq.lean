import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RepSecondIso

theorem subQuot_equiv_of_sup : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), E ≤ A → E ⊔ B = A →
    Nonempty ((subQuot E B).Equiv (subQuot A B)) := by
  intro G V _ _ _ ρ A B E hEA hsup
  have hEA' : E.toSubmodule ≤ A.toSubmodule := fun x hx => hEA hx
  let PE := Submodule.comap E.toSubmodule.subtype B.toSubmodule
  let PA := Submodule.comap A.toSubmodule.subtype B.toSubmodule
  let f : E.toSubmodule →ₗ[ℂ] A.toSubmodule ⧸ PA := PA.mkQ ∘ₗ Submodule.inclusion hEA'
  have hf : PE ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (p := PA) (Submodule.inclusion hEA' x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  let φ := PE.liftQ f hf
  have hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Submodule.inclusion hEA' x) :=
    fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective PE q
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hq
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective PA q
    have ha : (a : V) ∈ E.toSubmodule ⊔ B.toSubmodule := by
      rw [← Subrepresentation.toSubmodule_sup, hsup]
      exact a.2
    obtain ⟨e, he, b, hb, hab⟩ := Submodule.mem_sup.mp ha
    refine ⟨Submodule.Quotient.mk ⟨e, he⟩, ?_⟩
    rw [hφ, Submodule.Quotient.eq]
    show e - (a : V) ∈ B.toSubmodule
    have hdiff : e - (a : V) = -b := by
      rw [← hab]
      abel
    rw [hdiff]
    exact B.toSubmodule.neg_mem hb
  let ψ := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨Representation.Equiv.mk' ⟨φ, fun g => ?_⟩ ψ.symm (fun x => ψ.symm_apply_apply x)
    (fun y => ψ.apply_symm_apply y)⟩
  exact Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl)

end GlobalTheory.CompanionTheory.RepSecondIso
