import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G V) (π : Representation ℂ G W) (H : Subgroup G), IsSmooth π → IsSubquotient σ π → IsCompact (H : Set G) →
    fixed σ H ≠ ⊥ → fixed π H ≠ ⊥ := by
  intro G _ _ _ V W _ _ _ _ σ π H hπ hsq hH hne
  obtain ⟨S, f, hf⟩ := hsq
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g : G | S.toRepresentation g v = v} = {g : G | π g v = v} := by
      ext g; exact Subtype.ext_iff
    rw [this]; exact hπ v
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨u, rfl⟩ := hf x
  obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hS hH f.toLinearMap u fun h hh => by
    show f (S.toRepresentation h u) = f u
    rw [f.isIntertwining]
    simpa using hx ⟨h, hh⟩
  refine (Submodule.ne_bot_iff _).2 ⟨v.1, fun h => ?_, fun h0 => hx0 ?_⟩
  · exact congrArg Subtype.val (hv h)
  · have hv0 : v = 0 := Subtype.ext h0
    have e' : f.toLinearMap v = f u := e
    rw [← e', hv0, map_zero]
