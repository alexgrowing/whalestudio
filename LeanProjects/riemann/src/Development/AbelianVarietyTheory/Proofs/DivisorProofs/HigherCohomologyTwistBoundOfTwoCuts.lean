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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBoundOfStepDiff

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_lbPow_le_of_two_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hp d L hL ih F _ hF i hi
  obtain ⟨H, hH⟩ : ∃ H : LB X, IsAmpleLB H := (isProper_and_exists_isAmpleLB_of_isProjOver hp).2
  have : IsLocallyNoetherian X := (isNoetherian_of_isProjOver hp).toIsLocallyNoetherian
  obtain ⟨A, B, hA, hB, s, t, hs, ht, e⟩ := hH.exists_sub_of_mono_cutHom F (cls L hL)
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨C₁, h₁⟩ := ih (cut F hA s) (suppDim_cut_le F hA s hF) (j + 1) (by omega)
  obtain ⟨C₂, h₂⟩ := ih (cut F hB t) (suppDim_cut_le F hB t hF) j (by omega)
  refine sum_bound_of_step_diff (fun m => hdim k (twist F (lbPow L m)) (j + 1)) d 1 (C₁ + C₂)
    le_rfl fun m => ?_
  obtain ⟨M, hM, eM⟩ := cls_surj (m • cls L hL - cls B hB)
  have a₁ := (T.sheafCohomologyDim_twist_cut_inequalities k X hp F A (lbPow L (m + 1)) M hA (isLB_lbPow hL _) hM s hs (by
    rw [cls_lbPow hL, eM, succ_nsmul]
    nth_rewrite 2 [e]
    abel)).1 (j + 1)
  have a₂ := (T.sheafCohomologyDim_twist_cut_inequalities k X hp F B (lbPow L m) M hB (isLB_lbPow hL _) hM t ht (by
    rw [cls_lbPow hL, eM, sub_add_cancel])).2.1 j
  have a₃ := h₁ (m + 1)
  have a₄ : hdim k (twist (cut F hB t) (lbPow L m)) j ≤ C₂ * (d * (m + 1 + 1) ^ (d - 1)) :=
    (h₂ m).trans (by gcongr; omega)
  rw [add_mul]
  omega

end GlobalTheory
