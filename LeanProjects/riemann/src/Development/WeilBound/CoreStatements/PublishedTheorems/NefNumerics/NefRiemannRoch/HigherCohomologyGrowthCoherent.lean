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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberEqGenericRankMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistBoundOfShortExactStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.HigherCohomologyGrowthStructureStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.HigherCohomologyGrowthTwist
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestFurther
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefBound

theorem le_natCast_of_lt_succ {a : WithBot ℕ∞} {d : ℕ} (h : a < ((d + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (d : WithBot ℕ∞) :=
  _root_.UpperTheory.Reformulated.B.Yhb2.main h

end GlobalTheory.NefBound

open GlobalTheory.VB in

theorem GlobalTheory.NefBound.hdim_twist_le_of_isIntegral : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), IsNef k L → topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (G : X.Modules) [IsFiniteQC G], ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist G (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ _ hp d L hL hd hE
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  suffices H : ∀ r : ℕ, ∀ (G : X.Modules) [IsFiniteQC G], genRank G = r → ∀ i, 0 < i →
      ∃ C : ℕ, ∀ m : ℕ, hdim k (twist G (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d) by
    intro G _
    exact H _ G rfl
  intro r
  induction r with
  | zero =>
    intro G _ h i hi
    have hs : suppDim G ≤ (d : WithBot ℕ∞) :=
      GlobalTheory.NefBound.le_natCast_of_lt_succ (suppDim_lt_of_genRank_eq_zero hd h)
    obtain ⟨C, hC⟩ := hE G hs i hi
    refine ⟨C, fun m => (hC m).trans (Nat.mul_le_mul_left _ ?_)⟩
    exact Nat.mul_le_mul (Nat.le_succ d) (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.sub_le d 1))
  | succ r ih =>
    intro G _ h i hi
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule X).genRank_eq, hr] at e₃
    let S := ShortComplex.mk (QCoh.sectionHom s) (cokernel.π _) (cokernel.condition _)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    have hQ : IsFiniteQC S.X₃ := inferInstanceAs (IsFiniteQC (cokernel (QCoh.sectionHom s)))
    have h1 : IsFiniteQC S.X₁ := inferInstanceAs (IsFiniteQC (structureModule X))
    have hbd : ∀ i, 0 < i → ∃ C : ℕ, ∀ m : ℕ,
        hdim k (twist (twist G (lbPow A n)) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d) :=
      fun i hi => GlobalTheory.T.sheafCohomologyDim_twist_bound_of_shortExact k X hp L hL.isLB S hS h1 hQ i _
        (GlobalTheory.T.higher_cohomology_growth_structure k X hp d L hL hd hE i hi) (ih (cokernel (QCoh.sectionHom s)) (by omega) i hi)
    obtain ⟨C, hC⟩ := GlobalTheory.T.higher_cohomology_growth_twist k X hp d L hL.isLB hE (twist G (lbPow A n))
      ((QCoh.suppDim_le _).trans hd) _ (isLB_lbZPow hM (-1)) hbd i hi
    refine ⟨C, fun m => ?_⟩
    exact (hdim_congr k i ((twistFunctor (lbPow L m)).mapIso (Twist.twistTwistZNegOneIso G hM))).symm.trans_le (hC m)
