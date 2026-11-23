import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDimLeAddMulSectionsDimCut
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsDim_le_add_mul_sectionsDim_cut : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M : LB X) (hB : B.IsLB) (hM : M.IsLB) (s t : B.Sec), Mono (cutHom F hB s) → Mono (cutHom (cut F hB s) hB t) → ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB → hdim k (twist F M) 0 ≤ hdim k (twist F M') 0 + j * hdim k (twist (cut F hB s) M) 0 := by
  first | exact @GlobalTheory.SiuChain.hdim_le_add_mul_hdim_cut | exact GlobalTheory.SiuChain.hdim_le_add_mul_hdim_cut | (intros; apply GlobalTheory.SiuChain.hdim_le_add_mul_hdim_cut <;> assumption)
