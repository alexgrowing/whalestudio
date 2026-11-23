import Formalism.SharpRestriction.LevelLetterCocycles.ThmELiftAtOf
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingEveryOrdering
import Formalism.SharpRestriction.LevelLetterCocycles.ThmELiftAtBc
import Formalism.SharpRestriction.LevelLetterCocycles.BoundedNumeratorPowerSummability
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finiteDimensional_max_unramified (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have h : K0 K ≤ K.1 := inf_le_left
  exact FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion h).injective

theorem fd_Ks (K : FinExt l) (s : ℕ) : FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  classical
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos _
  have hfin : Set.Finite {x : Om l | x ^ (l ^ s) = 1} :=
    (Polynomial.nthRoots (l ^ s) (1 : Om l)).toFinset.finite_toSet.subset fun x hx => by
      simpa [Polynomial.mem_nthRoots hpos] using hx
  haveI : Finite {x : Om l | x ^ (l ^ s) = 1} := hfin.to_subtype
  haveI : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x hx =>
      IsIntegral.of_pow hpos (by rw [hx]; exact isIntegral_one)
  haveI := finiteDimensional_max_unramified K
  unfold Ks
  exact IntermediateField.finiteDimensional_sup _ _

def bigLL (K LL : FinExt l) : FinExt l :=
  ⟨LL.1 ⊔ IntermediateField.normalClosure ℚ_[l] ↥(Ks K 1) (Om l), by
    have := LL.2
    have := fd_Ks K 1
    exact IntermediateField.finiteDimensional_sup _ _⟩

theorem le_bigLL (K LL : FinExt l) : LL.1 ≤ (bigLL K LL).1 := le_sup_left

theorem unram_of_caseA {K LL : FinExt l} (hA : CaseA K LL) :
    Function.Bijective (algebraMap ↥(K0 K) ↥K.1) := by
  refine ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun y => ⟨⟨y, ⟨y.2, hA.1 y.2⟩⟩, ?_⟩⟩
  apply Subtype.ext
  rfl

def BrRest {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] (W : LocWach PD LL O v n)
    [Fintype (K →ₐ[Qp] LL)] : Prop :=
  ∃ e : W.DD W.one, UnitGen W e ∧ BKExt W e ∧ ∀ hR : Ring9 W, Realised2 hR e

theorem brHyp2_of_rec (P : LocPrime l) {K LL : FinExt l} (hA : CaseA K LL) (h5 : 5 ≤ l)
    [NeZero (finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)]
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (finrank ℚ_[l] ↥(K0 K))) (hs : W.s = 1) {Cc : ℝ}
    (h5W : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6W : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W) (h9W : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2a : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFirstProperty W) (hwx : Formalism.MainNotions.LiftingTheory.coreWX W) (hwr : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (htools : ToolsAlg W) (hf1 : F1 W) (hf2 : F2 W) (hH : HodgeExact (P.PD K) ↥LL.1 ↥(OL LL))
    (hrest : BrRest W) : BrHyp2 W Cc := by
  refine ⟨hs, unram_of_caseA hA, ?_, h5W, h6W, h9W, h2a, hwx, hwr, htools, hf1, hf2, hH, ?_, ?_, hrest⟩
  · rw [P.PD_p K]
    exact h5
  · unfold ValRing
    refine ⟨fun a b h => Subtype.ext h, fun x hx => ⟨⟨x, (P.v_O LL x).1 hx⟩, rfl⟩, fun o => ?_⟩
    exact (P.v_O LL _).2 o.2
  · rw [P.PD_p K]
    exact complete_OL LL

end Formalism.MainNotions.WachCoordinates.Br
