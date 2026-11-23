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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfIsNef
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.AmplePlusNefDimensionStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPsEffPullReducedClosedOfDimLeStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem withBot_eq_succ_of_le_of_not_le {t : WithBot ℕ∞} {d : ℕ} (h1 : t ≤ ((d + 1 : ℕ) : WithBot ℕ∞))
    (h2 : ¬ t ≤ (d : WithBot ℕ∞)) : t = ((d + 1 : ℕ) : WithBot ℕ∞) := by
  induction t using WithBot.recBotCoe with
  | bot => exact absurd bot_le h2
  | coe t =>
    induction t using ENat.recTopCoe with
    | top =>
      have h1' : (⊤ : ℕ∞) ≤ ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
      exact absurd h1' (ENat.coe_lt_top (d + 1)).not_ge
    | coe n =>
      have h1' : n ≤ d + 1 := by exact_mod_cast h1
      have h2' : ¬ n ≤ d := fun h => h2 (by exact_mod_cast h)
      have : n = d + 1 := by omega
      subst this; rfl

theorem isAmpleLB_tens_of_isNef_succ : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d + 1 : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) := by
  intro k _ _ d ih Y _ hproj hdimY A N hA hN
  refine IsAmpleLB.tens_of_forall_isPsEff k Y (strHom k Y) hproj A N hA hN.isLB ?_
  intro Z hZ
  let Z' := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme
  letI : Algebra k Γ(Z', ⊤) := ((redι Z).appTop.hom.comp (algebraMap k Γ(Y, ⊤))).toAlgebra
  have compat : ∀ r : k, (redι Z).appTop.hom (algebraMap k Γ(Y, ⊤) r) = algebraMap k Γ(Z', ⊤) r :=
    fun r => rfl
  haveI hirr : IrreducibleSpace Z' := Subtype.irreducibleSpace (by simpa using hZ)
  haveI hred : IsReduced Z' := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  haveI hint : IsIntegral Z' := isIntegral_of_irreducibleSpace_of_isReduced Z'
  have hdim : topologicalKrullDim Z' ≤ topologicalKrullDim Y :=
    (redι Z).isClosedEmbedding.isInducing.topologicalKrullDim_le
  have hpZ : IsProjOver (strHom k Z') := by
    obtain ⟨n, i, hi, hcomp⟩ := hproj
    refine ⟨n, redι Z ≫ i, ?_, ?_⟩
    · exact IsClosedImmersion.comp _ _
    · rw [Category.assoc, hcomp, comp_strHom compat]
  haveI hne : Nonempty Z' := by
    obtain ⟨y, hy⟩ := hZ.nonempty
    rw [← range_redι Z] at hy
    obtain ⟨z, _⟩ := hy
    exact ⟨z⟩
  haveI hnoeth : IsNoetherian Z' := isNoetherian_of_isProjOver hpZ
  have hAZ : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
  have hNZ : IsNef k (N.pull (redι Z)) := hN.pull_of_isClosedImmersion (redι Z) compat
  refine ⟨hNZ.isLB, A.pull (redι Z), hAZ, fun m hm => ?_⟩
  have hNm : IsNef k (lbPow (N.pull (redι Z)) m) := hNZ.pow hAZ m
  have hamp : IsAmpleLB (tens (A.pull (redι Z)) (lbPow (N.pull (redι Z)) m)) := by
    by_cases hle : topologicalKrullDim Z' ≤ ((d : ℕ) : WithBot ℕ∞)
    · exact ih Z' hpZ hle _ _ hAZ hNm
    · have hle2 : topologicalKrullDim Z' ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := hdim.trans hdimY
      have heq := withBot_eq_succ_of_le_of_not_le hle2 hle
      exact isAmpleLB_tens_of_nef_descent k d ih Z' hpZ heq _ _ hAZ hNm
  have hL'LB : (tens (lbPow (N.pull (redι Z)) m) (A.pull (redι Z))).IsLB :=
    isLB_tens (isLB_lbPow hNZ.isLB m) hAZ.isLB
  have hL'amp : IsAmpleLB (tens (lbPow (N.pull (redι Z)) m) (A.pull (redι Z))) := by
    refine IsAmpleLB.of_lbIso hamp hL'LB ((cls_eq_iff hL'LB hamp.isLB).1 ?_)
    rw [cls_tens (isLB_lbPow hNZ.isLB m) hAZ.isLB, cls_tens hAZ.isLB (isLB_lbPow hNZ.isLB m), add_comm]
  obtain ⟨r, hr1, hsec⟩ := IsAmpleLB.exists_hasNonzeroSec hL'amp (isLB_lbPow hL'LB 0)
  exact ⟨r, hr1, hsec _ (isLB_lbPow hL'LB r) (by rw [cls_lbPow hL'LB, cls_lbPow hL'LB, zero_smul, zero_add])⟩

end GlobalTheory
