import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveOfSumFor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNoetherianRingOL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinesAtOfLatticeAtLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsOverLettersOfCrysWith
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIntegralBis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

noncomputable section

namespace GlobalTheory.WachQN

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem invBasis_of_basisModule [Nontrivial O] (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {π' : LetA O n}
    (h : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π') :
    ∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, (∀ j, b j ∈ W.NΔ T) ∧ LinearIndependent (LetA O n) b ∧
      W.N T = Submodule.span (LetA O n) (Set.range b) := by
  obtain ⟨⟨r, b, hbN, huniq, -⟩, -⟩ := h
  obtain ⟨a0, -, ha0⟩ := huniq 0 (W.N T).zero_mem
  have hli : LinearIndependent (LetA O n) b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    exact congrFun ((ha0 g hg.symm).trans (ha0 0 (by simp)).symm) j
  have hsp : W.N T = Submodule.span (LetA O n) (Set.range b) := by
    refine le_antisymm (fun x hx => ?_) (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (hbN j).1))
    obtain ⟨a, ha, -⟩ := huniq x hx
    rw [ha]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hr : r = Module.finrank O ↥T.L.T := by
    let bN := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp.symm)
    have hbc := W.N_base T hT
    let bD := (Algebra.TensorProduct.basis W.EE bN).map hbc.equiv
    haveI : Nontrivial W.EE := W.EE_inj.nontrivial
    rw [← (W.DD_free T).2, Module.finrank_eq_card_basis bD, Fintype.card_fin]
  subst hr
  exact ⟨b, hbN, hli, hsp⟩

end Generic

theorem invBasis_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.InvBasis ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F h9 l _ K LL hA T hT
  have hbij : Function.Bijective (algebraMap ↥(K0 K) ↥K.1) :=
    ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩
  have hfr : Module.finrank ↥(K0 K) ↥K.1 = 1 :=
    (LinearEquiv.ofBijective (Algebra.linearMap ↥(K0 K) ↥K.1) hbij).finrank_eq.symm.trans (Module.finrank_self _)
  exact invBasis_of_basisModule _ T hT ((h9 l K 1 LL hA.2.2 T hT ((HW l).W_s K 1 LL hA.2.2)
    (by rw [(D.loc l).PD_p]; exact hA.2.1)).2.2 hfr).2

theorem heights_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.Heights ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F h5 l _ K LL hA T U M hh hU hb i
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1
  have hJ := GlobalTheory.WachUse.HeightsProof.jumpsOverLetters_of_crysWith _ T U M hh hU hb
  have hp := h5 l K 1 LL hA.2.2 T M hh hU.1
    (fun τ j hτ => hJ j τ (fun c => by simpa using congrArg (fun f => f c) hτ))
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [← GlobalTheory.WachUse.HeightsProof.φD_letE]
    exact hp.1 i _ ⟨x, hx, rfl⟩
  · exact Submodule.span_mono (Set.image_mono (GlobalTheory.WachUse.HeightsProof.Nl_le _ T (i - 1)))
      (hp.2.1 i _ ⟨y, hy, rfl⟩)

theorem saturated_caseA (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) :
    GlobalTheory.WachUse.Saturated ((HW l).W K 1 LL hA.2.2) := by
  intro T' T f hT hb x hx
  have hT' : IsCrys ((D.loc l).PD K) T'.ρ :=
    GlobalTheory.HTW.Rec.isCrys_of_equiv ((D.loc l).PD K) (LinearEquiv.ofBijective f.f hb) f.equiv hT
  exact ((GlobalTheory.NL.Isog.isog_loc (HW l) K 1 LL hA.2.2 T' T f hT' hT hb).2.2 x).1 hx

theorem qN_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    tableLineDegreeTwo.admitted D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      GlobalTheory.WachUse.QN ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F Cm h l _ K LL hA
  have hI := invBasis_of_admitted D HW F h.2.2.2.2.2.2.2.2.1 l K LL hA
  have hS := GlobalTheory.SenOperator.senOp_of_record D HW F Cm l K LL hA
  exact ⟨hI, heights_of_admitted D HW F h.2.2.2.2.1 l K LL hA,
    GlobalTheory.WachRankOne.rankOne_of_senOp (D.locA l) (HW l) (F l) (Cm l) K LL hA hI hS,
    saturated_caseA D HW l K LL hA,
    GlobalTheory.WachUse.additive_of_caseA (D.locA l) (HW l) (F l) (Cm l) K LL hA, hS⟩

end GlobalTheory.WachQN
