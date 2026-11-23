import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOfInhab
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WRowPinHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsFinal
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LocalFormOfHypotheses
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BetaLUniq

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf

namespace Formalism.L2.SG.LoopsFinal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section admitted

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)

def AdmRec : Prop :=
  VanishingOnXAndXPlus.FamilyFirstVolumeHypothesis Fm ∧ VanishingOnXAndXPlus.FamilySecondVolumeHypothesis Fm ∧ VanishingOnXAndXPlus.FamilyMassVolumeForGauge Fm ∧ VanishingOnXAndXPlus.BranchingMultiplicityVariant ∧ VanishingOnXAndXPlus.MinkowskiCounting ∧ VanishingOnXAndXPlus.HeckeCommutation ∧ VanishingOnXAndXPlus.MinkowskiSubgroupOrderBound ∧
  VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.FamilyWeylAndVandermonde Fm ∧ VanishingOnXAndXPlus.FamilyTwelfthHypothesis Fm ∧ VanishingOnXAndXPlus.FamilyThirteenthHypothesis Fm ∧ VanishingOnXAndXPlus.FamilyFourteenthHypothesis Fm ∧ VanishingOnXAndXPlus.FamilyFifteenthHypothesis Fm ∧
  VanishingOnXAndXPlus.FamilyRowMassIdentity Fm ∧ VanishingOnXAndXPlus.FamilyTotalRowMassIdentity Fm ∧ VanishingOnXAndXPlus.FamilyNineteenthHypothesis Fm ∧
  ∀ Cg cb Cu cT CT C0 A : ℝ,
    VanishingOnXAndXPlus.FamilyOneParameterPlancherelBound Fm Cg cb Cu cT CT C0 C1 ∧ VanishingOnXAndXPlus.FamilyFiniteSumPlancherelBound Fm Cg cb Cu cT CT C0 C1 ∧ VanishingOnXAndXPlus.FamilyPlancherelDifferenceBound Fm Cg cb Cu cT CT C0 C1 ∧
    VanishingOnXAndXPlus.FamilyDegreeNormalization Fm Cg cb Cu cT CT C0 C1 ∧ VanishingOnXAndXPlus.FamilyFormalDegreeUnitShiftRatio Fm Cg cb Cu cT CT C0 C1 ∧ VanishingOnXAndXPlus.admF2 Fm Cg cb Cu cT CT C0 C1 ∧
    VanishingOnXAndXPlus.FamilyRankTwoMassEstimate Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.admF4 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧
    VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.admF9 Fm Cg cb Cu cT CT C0 C1 ∧
    VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.FamilySixteenthHypothesis Fm Cg cb Cu cT CT C0 A ∧
    VanishingOnXAndXPlus.FamilyBesselUniqueness Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyTwentiethHypothesis Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyTwentyFirstHypothesis Fm Cg cb Cu cT CT C0 A ∧
    VanishingOnXAndXPlus.FamilyAmplitudeBoundsShared Fm Cg cb Cu cT CT C0 A C1 ∧ VanishingOnXAndXPlus.FamilyTermMassEstimate Fm Cg cb Cu cT CT C0 A

variable (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)

theorem family_admitted_of_parts (h : AdmRec Fm C1) (hV : ∀ Cg cb Cu cT CT C0 A : ℝ, VanishingOnXAndXPlus.FamilyTermVolumeSmallCellBound Fm C1 At Yt Cg cb Cu cT CT C0 A) :
    VanishingOnXAndXPlus.AdmF Fm C1 At Yt := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, h⟩ := h
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, fun Cg cb Cu cT CT C0 A => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19⟩ := h Cg cb Cu cT CT C0 A
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, hV Cg cb Cu cT CT C0 A⟩

theorem admissible_split_volumes (h : VanishingOnXAndXPlus.AdmF Fm C1 At Yt) : AdmRec Fm C1 ∧
    ∀ Cg cb Cu cT CT C0 A : ℝ, VanishingOnXAndXPlus.FamilyTermVolumeSmallCellBound Fm C1 At Yt Cg cb Cu cT CT C0 A := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, h⟩ := h
  refine ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, fun Cg cb Cu cT CT C0 A => ?_⟩,
    fun Cg cb Cu cT CT C0 A => (h Cg cb Cu cT CT C0 A).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, -⟩ := h Cg cb Cu cT CT C0 A
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19⟩

end admitted

section AtOne

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))
  (H : TieHyp W hI) (A : AmpDat X) (hV : PvalForm W hI A)

theorem jtPin_of (hA : AmpFibreConst Y) : JtPin hF hI (termTieOf W hI H A hV) := by
  intro u u' t s hs
  have h : ∃ s' : TT Y u u', s'.toTerm = tc hI t := ⟨s, hs⟩
  show hsNormSq (JtOf hI t) = ampL s ^ 2
  unfold JtOf
  rw [dif_pos h, ← Formalism.L2.SG.PackageTie.norm_hsEmb_sq]
  have e := hA u u' (tc hI t) ⟨h.choose, h.choose_spec⟩ ⟨s, hs⟩
  unfold ampL at e ⊢
  rw [e]

def FrameChangeAt : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u') (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)),
    (∀ a b, b < a → ξ a b = 0) → (∀ a, ξ a a = 1) →
      ∃ m ∈ NLam (lamOf W hI t) (fl'Of W hI t), ∀ b, m (frame (fl'Of W hI t) b) = frameAct (frame (fl'Of W hI t)) ξ b

theorem frameEqvInj_of (hFC : FrameChangeAt W hI) (u u' : D.what₂.Word) :
    FrameEqvInj (termTieOf W hI H A hV) (u' := u') (FlagOfWord W u) := by
  intro t t' hL hE
  obtain ⟨n, hn, ξ, hl, hd, hfr⟩ := hE
  obtain ⟨m, hm, hmf⟩ := hFC u u' t ξ hl hd
  refine term_injC W hI t t' hL ⟨n, hn, m, hm, fun b => ?_⟩
  have e1 : frame (fl'Of W hI t') b = frameAct (fun a => n (frame (fl'Of W hI t) a)) ξ b := congrFun hfr b
  rw [e1, hmf b]
  simp only [frameAct, map_sum, map_smul]

end AtOne

section Ev

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
  (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt (Fm.D x i) (At x hx i))

theorem rowLoopsF_of_ev
    (hFo : ∀ Cg cb Cu cT CT C0 : ℝ, OwnEv Fm fun C' Cl x i =>
      Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u)
    (hR : Formalism.MainNotions.BridgeLemma.RowsF Fm C1 At Yt) : RowLoopsF Fm At Cc := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨C₀, H⟩ := hR Cg cb Cu cT CT C0 A
  refine ⟨C₀, fun C hC => ?_⟩
  obtain ⟨a, Ha⟩ := H C hC
  obtain ⟨b, Hb⟩ := hFo Cg cb Cu cT CT C0
  refine ⟨max a b, fun x hx i => ?_⟩
  intro hx1 u u' hH
  obtain ⟨hn, hd, h1⟩ := Ha x (le_trans (le_max_left _ _) hx) i hx1 u u' hH
  have hF := Hb x (le_trans (le_max_right _ _) hx) i hH.1 u
  let K := Cc x hx1 i
  refine ⟨fun s h2 hk => ?_, ?_⟩
  · exact gam_mul_le K.gam (Yt x hx1 i u u') hF
      (classS_le (hI := K.hI) (At x hx1 i) K.jt K.wr K.fc (Yt x hx1 i u u') C hn hd s h2 hk)
  · exact gam_mul_le K.gam (Yt x hx1 i u u') hF
      (classOne_le (hI := K.hI) (At x hx1 i) K.jt K.wr K.fc (Yt x hx1 i u u') C h1)

end Ev

section Summ

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} {hI : SIso D.s (sOf hF)}

open Formalism.MainNotions.BridgeLemma in

theorem summable_of_rows (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y)
    {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1) (Q : D.s.Pair u u' → Prop) (B : ℝ)
    (hB : RowBound T L Q B) (Q' : Set (TT Y u u' × TT Y u u'))
    (hQ : ∀ x ∈ Q', ∃ h : rowL x.1 = rowL x.2, Q (recP (hI := hI) x h)) :
    Summable (Q'.indicator (fun p : TT Y u u' × TT Y u u' => ‖(Y.tO u u').vec p.1‖ * ‖(Y.tO u u').vec p.2‖)) := by
  refine summable_of_sum_le (c := massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u * B)
    (fun p => Set.indicator_nonneg (fun q _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) p) fun S => ?_
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter]
  have hS : ∀ x ∈ S.filter (· ∈ Q'), rowL x.1 = rowL x.2 := fun x hx => (hQ x (Finset.mem_filter.1 hx).2).1
  refine (finSum_le T hJ hW hC _ hS).trans (hB _ ?_)
  intro p hp
  rw [Finset.mem_image] at hp
  obtain ⟨x, _, rfl⟩ := hp
  exact (hQ x.1 (Finset.mem_filter.1 x.2).2).2

end Summ

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (sOf (hF x hx i)))
  (W : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WittDat (X x hx i))
  (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TieHyp (W x hx i) (hI x hx i))
  (A : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpDat (X x hx i))
  (hV : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PvalForm (W x hx i) (hI x hx i) (A x hx i))

def AtF : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i) :=
  fun x hx i => termTieOf (W x hx i) (hI x hx i) (H x hx i) (A x hx i) (hV x hx i)

variable (hFC : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FrameChangeAt (W x hx i) (hI x hx i))
  (B : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' C1)
  (M : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTermDat (Fm.D x i) (Fm.L x i) (AtF Fm X Y hF hI W H A hV x hx i) u u' C1 (B x hx i u u'))

def YtF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (AtF Fm X Y hF hI W H A hV x hx i) u u' C1 :=
  fun x hx i u u' => loopTieOfParts
    (loopRowsOf (W x hx i) (hI x hx i) (H x hx i) (A x hx i) (hV x hx i)
      (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds (Fm.D x i)) u u'
      (frameEqvInj_of (W x hx i) (hI x hx i) (H x hx i) (A x hx i) (hV x hx i) (hFC x hx i) u u'))
    (B x hx i u u') (M x hx i u u')

variable (hAF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpFibreConst (Y x hx i))
  (hRF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.L2.SG.Pf.FibreCounting.RowFree (Y x hx i))
  (gam : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), GamPin (Y x hx i))

def CcF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt (Fm.D x i) (AtF Fm X Y hF hI W H A hV x hx i) :=
  fun x hx i => ⟨X x hx i, Y x hx i, hF x hx i, hI x hx i,
    jtPin_of (W x hx i) (hI x hx i) (H x hx i) (A x hx i) (hV x hx i) (hAF x hx i),
    Formalism.L2.SG.Pf.WittFlags.WRowPin_holds (hF x hx i) (hI x hx i) (W x hx i) (H x hx i) (A x hx i) (hV x hx i),
    Formalism.L2.SG.Pf.FibreCounting.fibreCount_of (hRF x hx i), gam x hx i⟩

theorem termInjF (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word) :
    BridgeLemma₂.wordPairTermInjective (AtF Fm X Y hF hI W H A hV x hx i) (YtF Fm C1 X Y hF hI W H A hV hFC B M x hx i u u') :=
  fun t t' hL hE => frameEqvInj_of (W x hx i) (hI x hx i) (H x hx i) (A x hx i) (hV x hx i) (hFC x hx i) u u' t t' hL hE

theorem loop_bound_families
    (hRk : ∀ Cg cb Cu cT CT C0 : ℝ, PX.RanksF Fm C0 Cg cb Cu cT CT) (hL3 : VanishingOnXAndXPlusMass.Conclusion3Family Fm)
    (hAdm : AdmRec Fm C1)
    (hVol : ∀ Cg cb Cu cT CT C0 Aa : ℝ, VanishingOnXAndXPlus.FamilyTermVolumeSmallCellBound Fm C1 (AtF Fm X Y hF hI W H A hV)
      (YtF Fm C1 X Y hF hI W H A hV hFC B M) Cg cb Cu cT CT C0 Aa)
    (hAmp : BridgeLemma₂.FamilyAmplitudeBounds Fm C1)
    (hN : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
      BridgeLemma₂.wordPairNormRelation (AtF Fm X Y hF hI W H A hV x hx i) u u')
    (hG0 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
      @Formalism.MainNotions.BridgeLemma.LatticeDeterminantFactorization (Fm.D x i) (AtF Fm X Y hF hI W H A hV x hx i) u u')
    (hEL : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
      BridgeLemma₂.wordPairEntriesInLattice (AtF Fm X Y hF hI W H A hV x hx i) u u') :
    RowLoopsF Fm (AtF Fm X Y hF hI W H A hV) (CcF Fm X Y hF hI W H A hV hAF hRF gam) :=
  rowLoopsF_of_ev Fm C1 (AtF Fm X Y hF hI W H A hV) (YtF Fm C1 X Y hF hI W H A hV hFC B M)
    (CcF Fm X Y hF hI W H A hV hAF hRF gam)
    (fun Cg cb Cu cT CT C0 => Formalism.MainNotions.BridgeLemma.formAt_family Fm Cg cb Cu cT CT C0 (hRk Cg cb Cu cT CT C0) hL3
      (hAdm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 Cg cb Cu cT CT C0 0).2.2.2.2.2.2.2.2.2.2.2.2.1)
    (BridgeLemma₂.family_gluing_bounds_of_beta Fm C1 (AtF Fm X Y hF hI W H A hV) (YtF Fm C1 X Y hF hI W H A hV hFC B M)
      (family_admitted_of_parts Fm C1 _ _ hAdm hVol) hAmp
      (fun x hx i u u' => ⟨hN x hx i u u', hG0 x hx i u u', hEL x hx i u u',
        termInjF Fm C1 X Y hF hI W H A hV hFC B M x hx i u u'⟩)
      (fun x i => beta_l_unique (Fm.D x i)))

end Fam

section Closed

def NormTieC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    BridgeLemma₂.wordPairNormRelation (termTieOf W hI H A hV) u u'

def GramDeterminantCount : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    @Formalism.MainNotions.BridgeLemma.LatticeDeterminantFactorization D (termTieOf W hI H A hV) u u'

def EntryLatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    BridgeLemma₂.wordPairEntriesInLattice (termTieOf W hI H A hV) u u'

def FrameChangeC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X), FrameChangeAt W hI

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (sOf (hF x hx i)))
  (W : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WittDat (X x hx i))
  (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TieHyp (W x hx i) (hI x hx i))
  (A : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpDat (X x hx i))
  (hV : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PvalForm (W x hx i) (hI x hx i) (A x hx i))

def hFCOf (hFC : FrameChangeC) : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FrameChangeAt (W x hx i) (hI x hx i) :=
  fun x hx i => hFC _ _ _ (hF x hx i) (hI x hx i) (W x hx i)

theorem loop_bound_concrete_families (hFC : FrameChangeC) (hNC : NormTieC) (hGC : GramDeterminantCount) (hEC : EntryLatC)
    (B : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' C1)
    (M : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtF Fm X Y hF hI W H A hV x hx i) u u' C1 (B x hx i u u'))
    (hAF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpFibreConst (Y x hx i))
    (hRF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.L2.SG.Pf.FibreCounting.RowFree (Y x hx i))
    (gam : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), GamPin (Y x hx i))
    (hRk : ∀ Cg cb Cu cT CT C0 : ℝ, PX.RanksF Fm C0 Cg cb Cu cT CT) (hL3 : VanishingOnXAndXPlusMass.Conclusion3Family Fm)
    (hAdm : AdmRec Fm C1)
    (hVol : ∀ Cg cb Cu cT CT C0 Aa : ℝ, VanishingOnXAndXPlus.FamilyTermVolumeSmallCellBound Fm C1 (AtF Fm X Y hF hI W H A hV)
      (YtF Fm C1 X Y hF hI W H A hV (hFCOf Fm X Y hF hI W hFC) B M) Cg cb Cu cT CT C0 Aa)
    (hAmp : BridgeLemma₂.FamilyAmplitudeBounds Fm C1) :
    RowLoopsF Fm (AtF Fm X Y hF hI W H A hV) (CcF Fm X Y hF hI W H A hV hAF hRF gam) :=
  loop_bound_families Fm C1 X Y hF hI W H A hV (hFCOf Fm X Y hF hI W hFC) B M hAF hRF gam hRk hL3 hAdm hVol hAmp
    (fun x hx i u u' => hNC _ _ _ (hF x hx i) (hI x hx i) (W x hx i) (H x hx i) (A x hx i) (hV x hx i) u u')
    (fun x hx i u u' => hGC _ _ _ (hF x hx i) (hI x hx i) (W x hx i) (H x hx i) (A x hx i) (hV x hx i) u u')
    (fun x hx i u u' => hEC _ _ _ (hF x hx i) (hI x hx i) (W x hx i) (H x hx i) (A x hx i) (hV x hx i) u u')

end Closed

end Formalism.L2.SG.LoopsFinal
