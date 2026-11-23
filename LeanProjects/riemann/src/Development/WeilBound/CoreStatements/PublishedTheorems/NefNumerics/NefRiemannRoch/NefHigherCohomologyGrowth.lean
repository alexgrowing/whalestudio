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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistBoundOfShortExactStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRestrictionIrreducible

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem nefTwist_hdim_bound_succ : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → ∀ N : LB Y, IsNef k N → ∀ (E : Y.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow N m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → ∀ N : LB Y, IsNef k N → ∀ (E : Y.Modules) [IsFiniteQC E], suppDim E ≤ (d + 1 : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow N m)) j ≤ C * ((d + 1) * (m + 1) ^ d))) := by
  intro k _ _ d hd Y _ hY N hN E _ hsupp j hj
  haveI hnoeth : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hY
  obtain ⟨hprop, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hY
  haveI := hprop
  have hfin : ∀ (F : Y.Modules) [IsFiniteQC F] (m : ℕ), FiniteCoh k (twist F (lbPow N m)) :=
    fun F _ m => IsAmpleLB.finiteCohTwists (algebraMap_eq_strHom k Y) F hA _ (isLB_lbPow hN.isLB m)
  let P : Y.Modules → Prop := fun F => suppDim F ≤ ((d + 1 : ℕ) : WithBot ℕ∞) →
    ∀ j, 0 < j → ∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow N m)) j ≤ C * ((d + 1) * (m + 1) ^ d)
  have key : ∀ F : Y.Modules, IsFiniteQC F → P F := by
    refine QCoh.devissage Y P ?_ ?_ ?_
    · intro F hF _ j _
      refine ⟨0, fun m => ?_⟩
      have hz : IsZero (twist F (lbPow N m)) := (isZero_twist_iff (isLB_lbPow hN.isLB m)).2 hF
      haveI : Subsingleton (coh (twist F (lbPow N m)) j) := by
        have := cohOn.subsingleton_of_isZero hz ⊤ j
        exact this
      rw [hdim_eq_zero_of_subsingleton]
      exact Nat.zero_le _
    · intro S hS h1 h3 hP1 hP3 hs2 j hj
      haveI := h1
      haveI := h3
      haveI := hS.mono_f
      haveI := hS.epi_g
      obtain ⟨C1, hC1⟩ := hP1 ((suppDim_le_of_mono S.f).trans hs2) j hj
      obtain ⟨C3, hC3⟩ := hP3 ((suppDim_le_of_epi S.g).trans hs2) j hj
      refine ⟨C1 + C3, fun m => ?_⟩
      have hL := isLB_lbPow hN.isLB m
      haveI := Twist.preservesFiniteLimits_twistFunctor hL
      haveI := Twist.preservesColimits_twistFunctor hL
      have hS' := hS.map_of_exact (twistFunctor (lbPow N m))
      have h := hdim₂_le k hS' j ((hfin S.X₁ m).finite j) ((hfin S.X₃ m).finite j)
      have e1 := hC1 m
      have e3 := hC3 m
      simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃, twistFunctor_obj] at h
      calc hdim k (twist S.X₂ (lbPow N m)) j ≤ hdim k (twist S.X₁ (lbPow N m)) j + hdim k (twist S.X₃ (lbPow N m)) j := h
        _ ≤ C1 * ((d + 1) * (m + 1) ^ d) + C3 * ((d + 1) * (m + 1) ^ d) := Nat.add_le_add e1 e3
        _ = (C1 + C3) * ((d + 1) * (m + 1) ^ d) := by ring
    · intro Z hirr IH G hG hs j hj
      haveI := hG
      have hsub : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊆ (Z : Set Y) := by
        refine (support_pushforward_subset_image_of_isClosedImmersion _ G).trans ?_
        rintro _ ⟨x, -, rfl⟩
        rw [← range_redι Z]
        exact ⟨x, rfl⟩
      haveI : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G) :=
        ProperFinite.isFiniteQC_pushforward (redι Z) (IsAmpleLB.pull_of_isClosedImmersion hA (redι Z)) G
      by_cases hstrict : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊂ (Z : Set Y)
      · exact IH _ inferInstance hstrict hs j hj
      · have heq : support ((Scheme.Modules.pushforward (redι Z)).obj G) = (Z : Set Y) := by
          by_contra hne
          exact hstrict (HasSubset.Subset.ssubset_of_ne hsub hne)
        have hgen := hirr.isGenericPoint_genericPoint_closure
        rw [Z.isClosed.closure_eq] at hgen
        obtain ⟨w, hcl⟩ : ∃ w : Y, closure ({w} : Set Y) = (Z : Set Y) := ⟨_, hgen⟩
        have hw : w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G) := by
          rw [heq, ← hcl]
          exact subset_closure (Set.mem_singleton _)
        have hdimZ : topologicalKrullDim (Z : Set Y) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
          have := SheafCycle.dim_closure_le_suppDim hw
          rw [hcl] at this
          exact this.trans hs
        exact RRPush.hdim_pushforward_le k d hd Y hY N hN Z hirr hdimZ G j hj
  exact key E inferInstance hsupp j hj

end GlobalTheory
