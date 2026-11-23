import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleIffStable
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem irrIff_stable {H K : Type} [Group H] [Field K] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) K)
    (h : Submodule.span K (Set.range r) = ⊤) (W : Submodule K (Fin n → K))
    (hW : ∀ g, ∀ v ∈ W, (r g).mulVec v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  _root_.UpperTheory.Reformulated.B.StableSubmoduleBotOrTopOfSpanEqTop.irrIff_stable r h W hW

theorem UpperTheory.V.GradeZeroInterpolatingElement.irrIff :
    ∀ {H : Type} [Group H] (K : Type) [Field K] [IsAlgClosed K], (∀ r : H →* M4 K, Irr r ↔ Af.IsIrr r.toHomUnits) ∧ ∀ r r' : H →* M4 K, IsConj4 r r' ↔ Af.RepIso r.toHomUnits r'.toHomUnits := by
  intro H _ K _ _
  refine ⟨fun r => ⟨fun h => ?_, fun h => ?_⟩, fun r r' => ⟨?_, ?_⟩⟩
  · exact ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => irrIff_stable r h W hW⟩
  · exact KStar.Schema.span_eq_top_of_irreducible r fun N hN => h.2.2 N le_top hN
  · rintro ⟨u, hu⟩
    exact ⟨u, fun s => Units.ext (hu s)⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, fun s => congrArg Units.val (hu s)⟩
