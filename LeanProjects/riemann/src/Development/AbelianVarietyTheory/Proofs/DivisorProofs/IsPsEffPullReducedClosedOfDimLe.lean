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

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsNef.isPsEff_pull_red_of_dim_le (k : Type) [Field k] [Infinite k] (d : ℕ)
    (H : ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) →
      topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N →
        IsAmpleLB (CechPic.tens A N))
    (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (hX : IsProjOver (strHom k X)) (M : LB X)
    (hM : IsNef k M) (Z : Closeds X) (hZ : IsIrreducible (Z : Set X))
    (hd : topologicalKrullDim (Z : Set X) ≤ (d : ℕ)) : IsPsEff (M.pull (redι Z)) := by
  letI := algebraΓAlong k (redι Z)
  have := isIntegral_red hZ
  obtain ⟨B, hB⟩ := exists_isAmpleLB_of_isProjOver hX
  have : IsProper (strHom k X) := by
    obtain ⟨N, i, hi, e⟩ := hX
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hA := hB.pull_of_isClosedImmersion (redι Z)
  have : IsProper (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    rw [← comp_strHom (appTop_algebraMap_along k (redι Z))]
    infer_instance
  have hN := hM.pull_of_isClosedImmersion (redι Z) (appTop_algebraMap_along k (redι Z))
  refine ⟨hN.isLB, _, hA, fun m _ => ?_⟩
  have hP := H _ (hA.isProjOver _) ((topologicalKrullDim_red Z).trans_le hd) _ _ hA (hN.pow hA m)
  obtain ⟨r, hr, hg⟩ := hP.exists_isGenerated_pow
  refine ⟨r, hr, hg.hasNonzeroSec.of_cls_eq
    (isLB_lbPow (isLB_tens (isLB_lbPow hN.isLB m) hA.isLB) r) hg.isLB ?_⟩
  rw [cls_lbPow (isLB_tens (isLB_lbPow hN.isLB m) hA.isLB), cls_lbPow hP.isLB,
    cls_tens (isLB_lbPow hN.isLB m) hA.isLB, cls_tens hA.isLB (isLB_lbPow hN.isLB m), add_comm]

end GlobalTheory
