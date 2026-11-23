import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RhoLiftOf
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FrobeniusSqBoundOfLocal
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
import Formalism.SharpRestriction.LevelLetterCocycles.HermFlagUnipotentAnisotropicVectorSubMem
import Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfFrobeniusHyps
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LengthBoundOfHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSeriesDeltaZero
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.JumpsLetExists
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PtTransRec
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSZeroSplit
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentMemInvariantsLetter
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowerCongruenceOfAdmitted
import Formalism.SharpRestriction.LevelLetterCocycles.CompleteMax
import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerClauseOfAdmitted
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
import Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfGammaLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.LiftRingOfUniformizerClause
import Formalism.SharpRestriction.LevelLetterCocycles.QPowSmulFrobeniusMem
import Formalism.SharpRestriction.LevelLetterCocycles.LemGA0ConvVanish
import Formalism.SharpRestriction.LevelLetterCocycles.EqUniformizerMulOfConstantCoeffZero
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerClauseOfAdmittedAlt

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Asm

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (TensorProduct Zl O Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : TensorProduct Zl O Ai}
    {E : EtTie W (TensorProduct Zl O Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem content_bound_level_of_dcris_exact [NeZero n] {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hLev : Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (hpt : Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → ∀ (c : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∃ τ : K →ₐ[Qp] LL, Pt c ζ τ)
    (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W) (hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W) (hGs : LemmaGs W)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Formalism.MainNotions.N.Pv.LocalLengthBound.ContentBoundLevel W := by
  intro d T₁ T₂ F' b S η m hset
  have hCA := hset.1
  have h11 := hset.2.1
  exact Formalism.MainNotions.N.Pv.LocalLengthBound.contentBoundLevel_of W h5 h9 (hLev hCA h11)
    (fun T hT c ζ hζ x k hk j hj => by
      obtain ⟨τ, hτ⟩ := hpt hCA h11 c ζ hζ
      exact (((h4 T hT).2 c ζ τ hτ).1.1 x k hk j).2 hj)
    hT2 hTH hGs hE hC hQ d T₁ T₂ F' b S η m hset

theorem frobenius_lift_lemmas_general [NeZero n] (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (Ct : CmpTie W E ιdR p1 tS zS)
    (hLev : Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (hPT : Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → Formalism.MainNotions.N.Pv.LocalLengthBound.PtTrans W)
    (hH2 : Formalism.MainNotions.N.Pv.LocalLengthBound.H2Bound W) (hL41 : Formalism.MainNotions.N.Pv.LocalLengthBound.ContentBoundLevel W) (hDN : LemmaDN W)
    (hDN0 : Formalism.MainNotions.N.Pv.LocalLengthBound.LemmaDN0 W) : WachVectorLiftingBound W := by
  intro d T₁ T₂ F' b S η m hset
  have hCA := hset.1
  have h11 := hset.2.1
  obtain ⟨_, -, hFrac⟩ := hset.2.2.2.1
  have hL := hLev hCA h11
  have hMC := Formalism.MainNotions.N.Pv.LocalLengthBound.memCrit_of W hCA hFrac h1 h3 hL h5 hQ
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie W hCA.2.1 Ct
  have hGΔ := Formalism.MainNotions.N.Pv.LocalLengthBound.gamΔ_of_tie W Ct
  have hP := hPT hCA h11
  refine Formalism.MainNotions.N.Pv.LocalLengthBound.length_bound_of_hypotheses W h3 h5 h9 hL hE hC hQ hMC hH2 hL41 hDN hDN0
    (((W.χΓ W.gam).isUnit.map (algebraMap O LL)).ne_zero) (Formalism.MainNotions.N.Pv.LocalLengthBound.chi_zpow_ne_one W hCA)
    (fun T hT c ζ hζ x hx hγx k => hG.1 T hT c ζ hζ ⟨x, hx⟩ hγx k) hG.2 ?_ d T₁ T₂ F' b S η m hset
  intro T hT c ζ ζ₀ hζ hζ₀
  obtain ⟨δ, hδ, a, hζa, hv⟩ := hP ζ ζ₀ hζ hζ₀
  exact ⟨δ, hδ, algebraMap O LL (W.χΓ δ : O), ((W.χΓ δ).isUnit.map (algebraMap O LL)).ne_zero,
    fun x hx k => hGΔ T hT c ζ ζ₀ δ a hζ hζa hv x hx k,
    fun f => Ct.lev_Γ δ c ζ ζ₀ 1 a (by rwa [pow_one]) hv hζa f⟩

end Gen

section Rec

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem caseA_loc {l : ℕ} [Fact l.Prime] {K LL : Loc.FinExt l} (hg : Loc.Good K 1 LL)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg)) : Loc.CaseA K LL := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, hg⟩
  obtain ⟨y, hy⟩ := hCA.1.2 ⟨x, hx⟩
  have h2 := y.2.2
  have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
  rw [this] at h2
  exact h2

variable {CR CA CB CK : ℝ}

theorem crystalline_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.1

theorem laurent_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.1

theorem gamma_sub_one_in_coordinates (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1

theorem level_tools_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm :=
  Formalism.MainNotions.UnusedSlot80.tools_unramified_statement D HW F Cm ⟨crystalline_clause_of_admitted D HW F Cm hA, laurent_clause_of_admitted D HW F Cm hA, gamma_sub_one_in_coordinates D HW F Cm hA⟩

theorem truncation_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.CrystallineLiftingInputs.adm15 D HW F Cm := by
  refine ⟨Formalism.MainNotions.CrystallineLiftingInputs.TToolAlg_holds, fun l _ K LL hg _ => ?_⟩
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hg) := (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hO2 : ∀ x : ↥LL.1, 0 ≤ (D.loc l).v LL x → ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = x :=
    fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev.complete_max LL
  have hlm : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
  exact ⟨Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.tTool1_of _ hinj hO2 hP9 (hA.2.2.2.2.2.2.2.1 l K 1 LL hg),
    Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.tTool2_of _ hinj hO2 hlm hP9 (hA.2.2.2.2.2.2.2.1 l K 1 LL hg) (hA.2.2.2.2.2.2.2.2.1 l K 1 LL hg)⟩

theorem rhoLift_of_Adm (hA : admitted D HW F Cm CR CA CB CK) : rhoLift D HW F :=
  Formalism.MainNotions.N.Pv.LocalLengthBound.rhoLift_D D HW F Cm CR CA CB CK hA fun l _ K LL hg _ =>
    ⟨((truncation_clause_of_admitted D HW F Cm hA).2 l K LL hg).2, Formalism.MainNotions.CrystallineLiftingInputs.Tools.local_clause_of_admitted_statements D HW F Cm hA l K LL hg⟩

set_option maxHeartbeats 1600000 in

theorem h2_bound_of_admitted (hA : admitted D HW F Cm CR CA CB CK) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] :
    Formalism.MainNotions.N.Pv.LocalLengthBound.H2Bound ((HW l).W K 1 LL hg) := by
  intro d T₁ T₂ F' b S η m hset
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := caseA_loc D HW hg hCA
  have h5l : 5 ≤ l := by have := hset.2.1; rw [hpl] at this; omega
  have h1 := hA.1 l K 1 LL hg
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs : ((HW l).W K 1 LL hg).s = 1 := hCA.2.1
  have C := ((Cm l).C K 1 LL hg).tie
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie _ hs C
  have hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hg) := (level_tools_of_admitted D HW F Cm hA l K LL hCAl h5l).2
  haveI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) :=
    Formalism.MainNotions.UnusedSlot80.eq_sum_herm_smul_frame_of_inW (D.loc l) K LL
  have hΔ : IsUnit ((((HW l).W K 1 LL hg).DelF.card : ℕ) : ↥(OL LL)) := by
    haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
    have hcard : ((HW l).W K 1 LL hg).DelF.card = l - 1 :=
      Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F (gamma_sub_one_in_coordinates D HW F Cm hA) l K LL hCAl
    by_contra hnu
    have hm : ((((HW l).W K 1 LL hg).DelF.card : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := hnu
    have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
    have e : ((l : ℕ) : ↥(OL LL)) - ((((HW l).W K 1 LL hg).DelF.card : ℕ) : ↥(OL LL)) = 1 := by
      rw [hcard, Nat.cast_sub (by omega)]; simp
    have h3 := Submodule.sub_mem _ hlm hm
    rw [e] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(OL LL)).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  exact Formalism.MainNotions.N.Pv.LocalLengthBound.h2Bound_of_hypotheses _ Subtype.val_injective hΔ Formalism.MainNotions.CrystallineLiftingInputs.power_series_dvr_factorisation h1.2.2.2.2.1
    h1.2.2.2.2.2.2.2.2.1 hLev ((truncation_clause_of_admitted D HW F Cm hA).2 l K LL hg).2
    (Formalism.MainNotions.CrystallineLiftingInputs.Tools.frobenius_power_congruence_of_admitted D HW F Cm hA l K LL hg) hE hC hQ
    ((((HW l).W K 1 LL hg).χΓ ((HW l).W K 1 LL hg).gam).isUnit.map (algebraMap _ ↥LL.1)).ne_zero
    (Formalism.MainNotions.N.Pv.LocalLengthBound.chi_zpow_ne_one _ hCA)
    (fun T hT c ζ hζ x hx hγx k => hG.1 T hT c ζ hζ ⟨x, hx⟩ hγx k) hG.2 d T₁ T₂ F' b S η m hset

set_option maxHeartbeats 1600000 in

theorem lemGA_rec (hA : admitted D HW F Cm CR CA CB CK) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] :
    LemGA ((HW l).W K 1 LL hg) := by
  have h9 := (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
  have h5 := (hA.1 l K 1 LL hg).2.2.2.2.1
  have hT2 := ((truncation_clause_of_admitted D HW F Cm hA).2 l K LL hg).2
  have hTH := Formalism.MainNotions.CrystallineLiftingInputs.Tools.frobenius_power_congruence_of_admitted D HW F Cm hA l K LL hg
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hP9 := gamma_sub_one_in_coordinates D HW F Cm hA
  have hLev := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm (laurent_clause_of_admitted D HW F Cm hA) (Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F hP9)
  have hB : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l).W K 1 LL hg) := by
    intro l _ K LL hg _
    haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
    exact Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of _ (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
  have hEC := Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_D' D HW F Cm CR CA CB CK hA hLev hB
  have hCT := ((Cm l).C K 1 LL hg).tie
  intro d T₁ T₂ F' b S η m hS
  have hCA := hS.1
  have hl11 : 11 ≤ ((D.loc l).PD K).p := hS.2.1
  rw [(D.loc l).PD_p K] at hl11
  have hrec : Loc.CaseA K LL := caseA_loc D HW hg hCA
  have hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hg) :=
    Formalism.MainNotions.UnusedSlot80.ring_condition_uniformizer_polynomial D HW F hP9 l K LL hrec
  obtain ⟨hGN, hGA⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie ((HW l).W K 1 LL hg) hCA.2.1 hCT
  have hER : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hg) :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of ((HW l).W K 1 LL hg) hR
  have h4L : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hg) := hLev l K LL hrec (by omega)
  have hEU : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hg) :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of ((HW l).W K 1 LL hg) h4L hGN hGA
  have hla : LemGA_la ((HW l).W K 1 LL hg) :=
    lemGA_la_of_adm ((HW l).W K 1 LL hg) hT2 h9 h5 hE hC hQ
  have hlR : Formalism.MainNotions.LiftingTheory.lifta_Ring ((HW l).W K 1 LL hg) :=
    liftRing_of_uniformizer_clause ((HW l).W K 1 LL hg) h9 hCA T₂ hS.2.2.2.2.2.1.2.1
  have hx : GammaActionLemma ((HW l).W K 1 LL hg) :=
    lemGA_x_of ((HW l).W K 1 LL hg) hER hEU (hEC l K LL hrec (by omega)) hTH h9 h5 hlR
      (jumps_in_letter_of_crystalline ((HW l).W K 1 LL hg) hE hC hQ)
  have h0 : LemGA_0 ((HW l).W K 1 LL hg) := lemGA0_of_tools ((HW l).W K 1 LL hg) hCT hTH h9
  exact lemGA_of_pieces ((HW l).W K 1 LL hg) hla hx h0 d T₁ T₂ F' b S η m hS

theorem lemGB_rec (hA : admitted D HW F Cm CR CA CB CK) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] :
    LemGB ((HW l).W K 1 LL hg) := by
  have hQ := Formalism.MainNotions.CrystallineLiftingInputs.Tools.level_clause_of_admitted_statements D HW F Cm hA h23 l K LL hg
  have h9 := (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
  refine lemGB_of _ hQ (fun hCA => Formalism.MainNotions.CrystallineLiftingInputs.RToolNum_holds (D.loc l) (HW l) K LL hg hCA)
    (hC4 l K 1 LL hg) h9 (Formalism.MainNotions.LiftingTheory.lattice_clause_every_situation D HW F l K 1 LL hg)
    (fun _ => lemmaGD_cc (HW l) hg) (fun _ => ?_)
    (Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.gamma_lemma_of_crystalline D HW F (gamma_sub_one_in_coordinates D HW F Cm hA) l K LL hg)
  rw [(D.loc l).PD_p K]
  exact Formalism.MainNotions.UnusedSlot80.Split2.isUnit_pred l LL

theorem lemmaGs_rec (hA : admitted D HW F Cm CR CA CB CK) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] :
    LemmaGs ((HW l).W K 1 LL hg) :=
  lemmaGs_of_lemGAB _ (lemGA_rec D HW F Cm hA l K LL hg) (lemGB_rec D HW F Cm hA h23 hC4 l K LL hg)

theorem wach_basis_lemma_of_admitted (hA : admitted D HW F Cm CR CA CB CK)
    (hGs : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaGs ((HW l).W K 1 LL hg))
    (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] : Formalism.MainNotions.N.Pv.LocalLengthBound.ContentBoundLevel ((HW l).W K 1 LL hg) :=
  content_bound_level_of_dcris_exact _ (hA.1 l K 1 LL hg).2.2.2.1 (hA.1 l K 1 LL hg).2.2.2.2.1 (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
    (fun hCA h11 => (level_tools_of_admitted D HW F Cm hA l K LL (caseA_loc D HW hg hCA)
      (by rw [(D.loc l).PD_p K] at h11; omega)).2)
    (fun hCA h11 c ζ hζ => Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F (gamma_sub_one_in_coordinates D HW F Cm hA) l K LL (caseA_loc D HW hg hCA)
      (by rw [(D.loc l).PD_p K] at h11; omega) c ζ (by rwa [(D.loc l).PD_p K] at hζ))
    (((truncation_clause_of_admitted D HW F Cm hA).2 l K LL hg).2) (Formalism.MainNotions.CrystallineLiftingInputs.Tools.frobenius_power_congruence_of_admitted D HW F Cm hA l K LL hg)
    (hGs l K LL hg) (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).1 (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).2.1
    (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).2.2

theorem frobenius_lift_lemmas_of_admitted (hA : admitted D HW F Cm CR CA CB CK)
    (hH2 : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], Formalism.MainNotions.N.Pv.LocalLengthBound.H2Bound ((HW l).W K 1 LL hg))
    (hDN : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaDN ((HW l).W K 1 LL hg))
    (hDN0 : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], Formalism.MainNotions.N.Pv.LocalLengthBound.LemmaDN0 ((HW l).W K 1 LL hg))
    (hGs : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaGs ((HW l).W K 1 LL hg)) :
    wachVectorLiftingBoundAtGoodExtensions D HW F := fun l _ K LL hg _ =>
  frobenius_lift_lemmas_general _ (hA.1 l K 1 LL hg).1 (hA.1 l K 1 LL hg).2.2.1 (hA.1 l K 1 LL hg).2.2.2.2.1
    (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1 (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).1
    (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).2.1 (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).2.2 ((Cm l).C K 1 LL hg).tie
    (fun hCA h11 => (level_tools_of_admitted D HW F Cm hA l K LL (caseA_loc D HW hg hCA)
      (by rw [(D.loc l).PD_p K] at h11; omega)).2)
    (fun hCA h11 => Formalism.MainNotions.N.Pv.LocalLengthBound.ptTrans_rec D HW F (gamma_sub_one_in_coordinates D HW F Cm hA) l K LL (caseA_loc D HW hg hCA)
      (by rw [(D.loc l).PD_p K] at h11; omega))
    (hH2 l K LL hg) (wach_basis_lemma_of_admitted D HW F Cm hA hGs l K LL hg) (hDN l K LL hg) (hDN0 l K LL hg)

end Rec

theorem theorem_of_local_lemmas (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR CA CB CK : ℝ)
    (h12 : admitted D HW F Cm CR CA CB CK → cocyclesToWachVectorsBoundAtGoodExtensions D HW F)
    (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F) (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) :
    Stmt D HW F Cm 25 CR CA CB CK :=
  stmt_of_lemmas D HW F Cm CR CA CB CK fun hA =>
    have hG : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
        [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaGs ((HW l).W K 1 LL hg) :=
      fun l _ K LL hg _ => lemmaGs_rec D HW F Cm hA h23 hC4 l K LL hg
    have hDN : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
        [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaDN ((HW l).W K 1 LL hg) :=
      fun l _ K LL hg _ => Formalism.MainNotions.RamifiedCoefficientChains.S9.bigCellDetWeightedEnergyIntegral.dual_lemma_of_admitted D HW F Cm hA l K LL hg
    have hDN0 := Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev.lemmaDN0_L D HW F Cm hA.1 hA.2.2.2.2.2.2.2.2.2.2.1
    ⟨h12 hA,
      fun l _ K LL hg _ => lattice_bound_three_six_of _
        (frobenius_lift_lemmas_of_admitted D HW F Cm hA (fun l _ K LL hg _ => h2_bound_of_admitted D HW F Cm hA l K LL hg) hDN hDN0 hG
          l K LL hg)
        (Formalism.MainNotions.N.Pv.LocalLengthBound.steps6_of D HW F Cm CR CA CB CK hA hG hDN hDN0 l K LL hg),
      rhoLift_of_Adm D HW F Cm hA⟩

theorem theorem_of_literature_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR CA CB CK : ℝ) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F) (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F)
    (hHerr : Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F)
    (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : Stmt D HW F Cm 25 CR CA CB CK :=
  theorem_of_local_lemmas D HW F Cm CR CA CB CK
    (fun hA => Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature.local_lemmas_of_literature D HW F Cm hA h23 hHerr a22 hFont) h23 hC4

end Formalism.MainNotions.RamifiedCoefficientChains.Asm
