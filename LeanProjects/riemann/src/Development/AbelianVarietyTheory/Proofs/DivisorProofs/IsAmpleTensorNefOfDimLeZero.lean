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

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem isAmpleLB_tens_of_isNef_of_dim_le_zero : ∀ (k : Type) [Field k] [Infinite k], (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (0 : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) := by
  intro k _ _ Y _ hp hd A N hA hN
  have : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hp
  have hAN : (tens A N).IsLB := (IsNef.tens_of_isProjOver (IsAmpleLB.isNef (k := k) hA) hN hp).isLB
  have hlt : topologicalKrullDim Y < ((1 : ℕ) : WithBot ℕ∞) :=
    lt_of_le_of_lt hd (by exact_mod_cast Nat.zero_lt_one)
  refine isAmpleLB_of_subsingleton_coh_one Y (tens A N) hAN fun F _ => ⟨1, le_rfl, ?_⟩
  have : IsFiniteQC (twist F (lbPow (tens A N) 1)) := isFiniteQC_twist (isLB_lbPow hAN 1)
  exact hA.subsingleton_coh_of_dim_lt _ hlt

end GlobalTheory
