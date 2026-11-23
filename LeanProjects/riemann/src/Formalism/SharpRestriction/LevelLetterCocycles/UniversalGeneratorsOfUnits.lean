import Formalism.SharpRestriction.LevelLetterCocycles.SingleMemSpan
import Formalism.SharpRestriction.LevelLetterCocycles.EvalZeroXEqUniformizer

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem univGenCore_of_lev [IsDomain O] [IsPrincipalIdealRing O] [NeZero n]
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W) (hS : PsStable W)
    (hRAT : CutU.RATCore W)
    (hInv : ∀ (A : ArcP n) (c : ZMod n), c ∈ A.cuts → ∀ s < A.len c, InvLevAt W s) :
    Formalism.MainNotions.UnusedSlot80.UnivC.UnivGenCore PD W :=
  univGenCore_of' W hinj hO2 hpu hR hKL hS hRAT hInv (finLev_of W hR (p_ne_zero_O' W) hpu)

theorem universal_generators_of_units [IsDomain O] [IsPrincipalIdealRing O] [NeZero n]
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) :
    Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W → KillerLevCore W → PsStable W → W.π₀ ∈ W.AΔ →
      CutU.RATCore W → CutU.InvLevCore W → Formalism.MainNotions.UnusedSlot80.UnivC.UnivGenCore PD W :=
  fun hR hKL hS _ hRAT hInv =>
    univGenCore_of_lev W hinj hO2 hpu hR hKL hS hRAT fun _ _ _ s _ => invLevAt_of W hInv s

end Formalism.MainNotions.UnusedSlot80.UGen
