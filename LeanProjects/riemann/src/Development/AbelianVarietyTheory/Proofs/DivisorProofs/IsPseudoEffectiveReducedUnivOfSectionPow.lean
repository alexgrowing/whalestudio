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

set_option autoImplicit false

namespace GlobalTheory

theorem isPsEff_pull_redι_univ_of_hasNonzeroSec_pow :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (M : LB X), M.IsLB → ∀ r : ℕ, 1 ≤ r → HasNonzeroSec (lbPow M r) → ∀ Z : Closeds X, (Z : Set X) = Set.univ → IsPsEff (M.pull (redι Z)) := by
  intro k _ _ X _ _ hp M hM r hr hs Z hZ
  have hirr : IsIrreducible (Z : Set X) := hZ ▸ IrreducibleSpace.isIrreducible_univ X
  have := isIntegral_red hirr
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
  obtain ⟨x, hx⟩ := (range_redι Z).ge (hZ.ge (Set.mem_univ (genericPoint X)))
  rw [← hx] at hs
  have e := nonzeroLocus_secPull s (redι Z)
  have h1 : HasNonzeroSec ((lbPow M r).pull (redι Z)) :=
    ⟨secPull s (redι Z), sec_ne_zero_of_mem (x := x) (e.ge hs)⟩
  have hM' := LB.isLB_pull hM (redι Z)
  refine isPsEff_of_hasNonzeroSec_pow (hH.pull_of_isClosedImmersion (redι Z)) hM' hr
    (h1.of_cls_eq (isLB_lbPow hM' r) (LB.isLB_pull (isLB_lbPow hM r) _) ?_)
  rw [cls_lbPow hM', cls_pull hM, cls_pull (isLB_lbPow hM r), cls_lbPow hM, map_nsmul]

end GlobalTheory
