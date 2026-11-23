import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem topologicalKrullDim_le_of_isClosed_ne_univ :
    ∀ (X : Scheme.{0}) [IsIntegral X] (d : ℕ), topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → topologicalKrullDim Z ≤ (d : ℕ) := by
  intro X _ d h Z hZ hne
  have h₁ := GlobalTheory.topologicalKrullDim_add_one_le hZ isClosed_univ fun x _ =>
    ⟨genericPoint X, Set.mem_univ _, fun hg => hne (Set.eq_univ_of_forall fun z =>
      (genericPoint_specializes z).mem_closed hZ hg), genericPoint_specializes x⟩
  rw [(Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq] at h₁
  exact ENat.WithBot.add_le_add_one_right_iff.1 (h₁.trans (h.trans_eq (Nat.cast_succ d)))

end GlobalTheory
