import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PlacesExc

theorem finite_exceptional : ∀ (D : D7) (l : ℕ), l.Prime → ∃ F : Finset (PlE D.host), ∀ v, v ∉ F → v ∉ placesOver D.host.E l ∧ v ∉ placesS D l := by
  intro D l hl
  have h1 : (placesOver D.host.E l).Finite := Formalism.L2.Fam.NPC.placesOver_fin D.host l hl
  have h2 : (placesS D l).Finite := Formalism.L2.Fam.NPC.exceptional_places_finite D.host l
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset] at hv
  exact ⟨fun h => hv (Or.inl h), fun h => hv (Or.inr h)⟩

end GlobalTheory.PlacesExc
