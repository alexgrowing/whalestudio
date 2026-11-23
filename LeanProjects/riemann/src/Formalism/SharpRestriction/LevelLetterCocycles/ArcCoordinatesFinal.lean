import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfFrobeniusLevels
import Formalism.SharpRestriction.LevelLetterCocycles.LevelSeriesFirstFactorOrderOne
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.JumpsLetExists
import Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences
import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module Formalism.MainNotions.N.Pv.LocalLengthBound.Ser Formalism.MainNotions.N.Pv.LocalLengthBound.MC

section Pf

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {PD : PeriodData G Qp K₀ K B BdR}
    (W : LocWach PD LL O v n)

theorem memCrit_of_free [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hFr : IsFractionRing O LL)
    (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : MemCrit W := by
  intro T hT c x k hk hxc hexp
  have hs : W.s = 1 := hA.2.1
  have hp : (PD.p : LL) ≠ 0 := by
    intro h0
    have := W.v_l
    rw [h0, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  obtain ⟨M, h, hJ⟩ := jumpsLet_exists W hA hD T hT
  have h5T := (h5 T M h hT hJ).2.2 x ⟨k, hk⟩
  refine h5T.2 fun i ζ hQ k' hk' => ?_
  by_cases hic : i = c
  · subst hic
    have hζ := qroot_prim W hs hp hQ
    have := fd_ιDi W hA hD T hT i
    exact mem_vanI_at W hFr T i ζ ((h1 T hT).2 i) (h3 T hT)
      (h4 T hT i 0 ζ (by rwa [zero_add, pow_one])) (W.Q ^ k' • x) hk'
      (by rw [smul_comm, hxc]) k' (shift_exp W hs hp T i hζ x k hk (hexp ζ hζ) k' hk')
  · have hl : (letE c : LetA O n) ∈ Formalism.MainNotions.DeltaInvariantLattices.vanI W i ζ k' := by
      show W.lev i ζ (letE c) ∈ Ideal.span {(PowerSeries.X : PowerSeries LL) ^ k'}
      rw [W.lev_letter i ζ _ (by simp [letE, Pi.single_eq_of_ne hic])]
      exact Ideal.zero_mem _
    have e1 : W.Q ^ k' • x = (letE c : LetA O n) • (W.Q ^ k' • x) := by rw [smul_comm, hxc]
    rw [e1]
    exact Submodule.smul_mem_smul hl hk'

end Pf

theorem memCritL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1f : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
      haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
      MemCrit ((HW l).W K 1 LL hG) := by
  intro l _ K LL hG hCA h5l
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  have hCW : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hG) :=
    Formalism.MainNotions.UnusedSlot80.caseA_of_unram' (D.loc l) (HW l) hG hCA.1 hCA.2.1
  have hLev := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm h4 (Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F h9) l K LL hCA h5l
  exact memCrit_of_free _ hCW (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL) (h1f l K 1 LL hG) (h3 l K 1 LL hG) hLev
    (h5 l K 1 LL hG) (h11 l K LL).2.2

end Formalism.MainNotions.N.Pv.LocalLengthBound

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem arc_coordinates_final (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : AdmArcA D HW F Cm) (h1f : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D) :
    ArcLiftingCoordinates D HW F Cm :=
  arc_coordinates_of_frobenius_levels D HW F Cm hA hA.2.1 hA.2.2.2.1
    (lev0MprL_of D HW F Cm hA (Formalism.MainNotions.N.Pv.LocalLengthBound.memCritL_of D HW F Cm h1f hA.1 hA.2.1 hA.2.2.1 hA.2.2.2.1 h11))

theorem split_case_A_final (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : AdmSplitA D HW F Cm) (hArc : AdmArcA D HW F Cm) (h1f : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F)
    (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F) (h17 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D) :
    SplittingArcLifting D HW F Cm :=
  split_case_A_of_hypotheses D HW F Cm hA hArc hArc.2.1 h6 hArc.2.2.2.1 hArc.2.2.2.2.1 hArc.2.2.2.2.2.1 hWX hFont h23 h17
    (lev0MprL_of D HW F Cm hArc
      (Formalism.MainNotions.N.Pv.LocalLengthBound.memCritL_of D HW F Cm h1f hArc.1 hArc.2.1 hArc.2.2.1 hArc.2.2.2.1 h11))

end Formalism.MainNotions.UnusedSlot80
