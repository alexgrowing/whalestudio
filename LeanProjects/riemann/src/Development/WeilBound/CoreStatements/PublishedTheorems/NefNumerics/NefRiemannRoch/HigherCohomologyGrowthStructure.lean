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
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegAllDimsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfRegularSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfTwoCutsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1GrowthNoSectionsNefStatement

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRR

theorem hdim_twist_structureModule_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), IsNef k L → topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ _ hproj d L hL hkd hind i hi
  haveI : IsLocallyNoetherian X := by
    obtain ⟨N, f, hf, -⟩ := hproj
    haveI := hf
    exact LocallyOfFiniteType.isLocallyNoetherian (f ≫ PSpace.str k N)
  have hsupp : suppDim (GlobalTheory.structureModule X) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
    (suppDim_structureModule (X := X)).trans_le hkd
  by_cases hsec : ∃ p, 1 ≤ p ∧ HasNonzeroSec (lbPow L p)
  · obtain ⟨p, hp, s, hs⟩ := hsec
    have hmono : Mono (cutHom (GlobalTheory.structureModule X) (isLB_lbPow hL.isLB p) s) :=
      (mono_cutHom_structureModule_iff _ s).mpr ((sec_ne_zero_iff s).mp hs)
    exact T.higherCohomology_twist_bound_of_regular_section k X hproj d L hL.isLB hind (GlobalTheory.structureModule X) hsupp p hp s hmono i hi
  · push_neg at hsec
    have h0 : ∀ m, 1 ≤ m → hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 = 0 := by
      intro m hm
      by_contra hne
      exact hsec m hm (lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) (Nat.pos_of_ne_zero hne))
    have hint := T.nef_intersection_nonneg_all_dims k X hproj (d + 1) (GlobalTheory.structureModule X) hsupp (fun _ => L) (fun _ => hL)
    have hi2 := T.higherCohomology_twist_bound_of_two_cuts k X hproj d L hL.isLB hind (GlobalTheory.structureModule X) hsupp
    rcases Nat.lt_or_ge i 2 with h | h
    · obtain rfl : i = 1 := by omega
      exact T.h1_dim_bound_of_no_sections_nonneg_interNum k X hproj d L hL.isLB (GlobalTheory.structureModule X) hsupp h0 hint hi2
    · exact hi2 i h

end GlobalTheory.NefRR
