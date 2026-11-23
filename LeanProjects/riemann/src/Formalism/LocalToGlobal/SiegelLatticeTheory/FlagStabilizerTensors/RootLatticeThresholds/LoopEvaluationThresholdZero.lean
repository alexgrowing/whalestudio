import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsTies
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GammaFixedOfHypotheses
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCountHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittExistsHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairAmpConstWd
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AutLzFinite

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsCut
  Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsEv Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ConcAt0 (D : D7) (T : TermTie D) where
  X : HidaSetting D
  Y : Full X
  hF : FinX Y
  hI : SIso D.s (sOf hF)
  jt : JtPin hF hI T
  wr : WRowPin hF hI T
  fc : FibreCount Y

section TransportedAlt

def RowLoopsEv0 {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
    (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt0 (Fm.D x i) (At x hx i)) : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ C'₀ Cl₀ : ℝ, OwnEv Fm fun C' Cl x i => C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (hx : Fm.x1 < x) (u u' : (Fm.D x i).what₂.Word),
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie (Cc x hx i).X (Cc x hx i).Y →
      ((Cc x hx i).Y.tO u u').AbsConv →
      ((Cc x hx i).Y.tO u u').RowBig (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u') ∧
      ((Cc x hx i).Y.tO u u').RowNotScalar (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u')

theorem loop_evaluation_threshold_zero (hLC : PN.LoopCores) (hSub : PB.SubFamily) (hS : Formalism.HermitianLatticesTheory.SiegelMassRatio)
    (Cg cb Cw cT CT C0 A C₀ : ℝ) :
    ∃ C'₀ Cl₀ : ℝ, ∀ {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
      (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
        LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
      (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt0 (Fm.D x i) (At x hx i)),
      (∀ C : ℝ, C₀ ≤ C → OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) (u u' : (Fm.D x i).what₂.Word),
        Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cw cT CT C0 A →
          Formalism.MainNotions.BridgeLemma.RowsND (At x hx i) (Yt x hx i u u') C ∧ Formalism.MainNotions.BridgeLemma.RowsDeg (At x hx i) (Yt x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsOne (At x hx i) (Yt x hx i u u') C) →
      (OwnEv Fm fun C' Cl x i =>
        Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cw cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) →
      OwnEv Fm fun C' Cl x i => C'₀ ≤ C' → Cl₀ ≤ Cl →
        ∀ (hx : Fm.x1 < x) (u u' : (Fm.D x i).what₂.Word),
          Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie (Cc x hx i).X (Cc x hx i).Y →
          ((Cc x hx i).Y.tO u u').AbsConv →
          ((Cc x hx i).Y.tO u u').RowBig (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u') ∧
          ((Cc x hx i).Y.tO u u').RowNotScalar (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
  obtain ⟨C₃, _, HX⟩ := xiSizesC_of hS Cg cb Cw cT CT C0 A
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (max C₀ C₃) (max CT 1) := ⟨_, rfl⟩
  have hCC₀ : C₀ ≤ C := by rw [hCdef]; exact le_max_of_le_left (le_max_left _ _)
  have hCC₃ : C₃ ≤ C := by rw [hCdef]; exact le_max_of_le_left (le_max_right _ _)
  have hCT : CT ≤ C := by rw [hCdef]; exact le_max_of_le_right (le_max_left _ _)
  have hC : 1 ≤ C := by rw [hCdef]; exact le_max_of_le_right (le_max_right _ _)
  obtain ⟨K₀, hJ⟩ := Formalism.L2.SG.RowsOther.rowLoops_of_input hLC hSub C hC
  obtain ⟨a3, b3, HX'⟩ := HX C hCC₃
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = max 1 C0 := ⟨_, rfl⟩
  have hA₀1 : 1 ≤ A₀ := by rw [hA₀]; exact le_max_left _ _
  refine ⟨max a3 K₀, max b3 (max 4 (3 + 6 * Real.log (3 * A₀))), ?_⟩
  intro eps Fm C1 At Yt Cc HR hFo
  refine (OwnEv.and (HR C hCC₀) hFo).mono ?_
  rintro C' Cl x i ⟨H1, H2⟩ hC' hCl hx u u' hH hT hA
  have ha3 : a3 ≤ C' := le_trans (le_max_left _ _) hC'
  have hK₀ : K₀ ≤ C' := le_trans (le_max_right _ _) hC'
  have hb3 : b3 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl4 : 4 ≤ Cl := le_trans (le_max_of_le_right (le_max_left _ _)) hCl
  have hClA : 3 + 6 * Real.log (3 * A₀) ≤ Cl := le_trans (le_max_of_le_right (le_max_right _ _)) hCl
  obtain ⟨hn, hd, h1⟩ := H1 hx u u' hH
  have hFo' := H2 hH.1 u
  have hGP : GamPin (Cc x hx i).Y := gammaFixed_of_hypotheses (Cc x hx i).Y hH.1
  have hXiH := HX' C' Cl ha3 hb3 (Fm.D x i) (Fm.L x i) u u' hH
  have hP := params_at hH.1 (Cc x hx i).X u hCl4 hCT hC hK₀
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b (Fm.D x i) (Fm.L x i)
  have hb0 : (0 : ℝ) < (Fm.L x i).sc.b := by linarith
  have hk0 : (0 : ℝ) < (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < (Fm.D x i).R.k)
  have hg : 0 < ((Cc x hx i).X.B.g : ℝ) := by
    have h5 : (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 ≤ ((Cc x hx i).X.B.g : ℝ) := hP.2.2.2.2.1
    have h8 : 0 < (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 := by positivity
    linarith
  have hv : 0 ≤ (Fm.D x i).host.v := by linarith [hP.2.2.2.2.2.2.1]
  have hC0' : (0 : ℝ) ≤ C := by linarith
  have hGam : 0 ≤ GamS (Fm.D x i) (Fm.L x i) := by unfold GamS; exact (Real.exp_pos _).le
  have HS : ∀ s, 2 ≤ s → s ≤ (Fm.D x i).R.k →
      ClassLe ((Cc x hx i).Y.tO u u') (bigS ((Cc x hx i).Y.tO u u') s)
        (A₀ * rowS C (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f s (Fm.L x i).sc.b ((Cc x hx i).X.B.g : ℝ)
          (Fm.D x i).host.v (GamS (Fm.D x i) (Fm.L x i)) (Formalism.MainNotions.BridgeLemma.XiB (Fm.D x i) (Fm.L x i) u C) *
          ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
    intro s h2 hk
    have hX0 := xi_nonneg hXiH s h2 hk
    rw [hA₀]
    exact rowsSC_at (At x hx i) (Cc x hx i).jt (Cc x hx i).wr (Cc x hx i).fc hGP (Yt x hx i u u') hFo' hT
      hH C hn hd s h2 hk (ndRow_nonneg hC0' hb0 hg hv hGam hX0) (degRow_nonneg hC0' hb0 hg hv hGam hX0)
  have H1' : ClassLe ((Cc x hx i).Y.tO u u') (((Cc x hx i).Y.tO u u').nsc ((Cc x hx i).Y.tO u u').genSet)
      (A₀ * oneT C (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f (Fm.L x i).sc.b ((Cc x hx i).X.B.g : ℝ)
        (GamS (Fm.D x i) (Fm.L x i)) * ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
    rw [hA₀]
    exact oneSC_at (At x hx i) (Cc x hx i).jt (Cc x hx i).wr (Cc x hx i).fc hGP (Yt x hx i u u') hFo' hT
      C0 C hC0' h1
  obtain ⟨Al, NT', Gam, Xi, hAl, hP', hX', h6, hAmp⟩ :=
    loopsAmp_at hH hT hA hC hCT hK₀ hA₀1 hCl4 hClA hXiH HS H1'
  exact hJ _ _ _ _ _ ((Cc x hx i).Y.tO u u') (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f Al (Fm.L x i).sc.b
    ((Cc x hx i).X.B.g : ℝ) (Fm.D x i).host.v NT' Gam Xi (ddC (Cc x hx i).X (Cc x hx i).Y u u')
    hAl hP' hX' h6 (dd_nonneg hT u u') hA
    (Formalism.L2.SG.RowsOther.loopsInput_of_amp _ hA.2.2.le _ _ _ _ _ _ _ _ _ _ _ hAmp)

end TransportedAlt

section Fam5

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (sOf (hF x hx i)))
  (hCT : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcTie (X x hx i) (Y x hx i))

def W5 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WittDat (X x hx i) :=
  fun x hx i => Classical.choice (Formalism.L2.SG.Pf.WittFlags.WittExists_holds (Fm.D x i) (X x hx i))

theorem H5 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TieHyp (W5 Fm X x hx i) (hI x hx i) := fun x hx i =>
  { lat := Formalism.L2.SG.Pf.WittFlags.LatIso_holds (Fm.D x i)
    idG := fun u u' => identityCell_vanishes u u'
    atSome := fun u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds _ _ (Y x hx i) u u'
    autFin := fun u => Formalism.L2.SG.Pf.autFin_of (automorphism_lattice_finite (Fm.D x i)) ((Fm.D x i).sp.Y_sig 0)
      (Formalism.MainNotions.BridgeLemma.tie_Tu_pos (Fm.D x i) u)
      (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds (Fm.D x i) ((W5 Fm X x hx i).δ u) ((W5 Fm X x hx i).isom u)
        ((X x hx i).Fu u) ((Y x hx i).what₂ u) ((Y x hx i).rowsOK u))
    dim := fun u => Formalism.L2.SG.Pf.dimTie (X x hx i) u
    pairs := Formalism.L2.SG.Pf.pairTiesAll_holds _ _ (Y x hx i) (hF x hx i) (W5 Fm X x hx i) (hI x hx i) }

def A5 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpDat (X x hx i) :=
  fun x hx i => Classical.choose (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (W5 Fm X x hx i) (hI x hx i) (hCT x hx i).2.2.2.2.1)

theorem hV5 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PvalForm (W5 Fm X x hx i) (hI x hx i) (A5 Fm X Y hF hI hCT x hx i) :=
  fun x hx i => Classical.choose_spec (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (W5 Fm X x hx i) (hI x hx i) (hCT x hx i).2.2.2.2.1)

def termRelationsOfFamily : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i) :=
  AtF Fm X Y hF hI (W5 Fm X) (H5 Fm X Y hF hI) (A5 Fm X Y hF hI hCT) (hV5 Fm X Y hF hI hCT)

def termRelationsBaseData : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt0 (Fm.D x i) (termRelationsOfFamily Fm X Y hF hI hCT x hx i) :=
  fun x hx i => ⟨X x hx i, Y x hx i, hF x hx i, hI x hx i,
    jtPin_of (W5 Fm X x hx i) (hI x hx i) (H5 Fm X Y hF hI x hx i) (A5 Fm X Y hF hI hCT x hx i)
      (hV5 Fm X Y hF hI hCT x hx i) (Formalism.L2.SG.Pf.FibreCounting.AmpFibreConst_holds (Y x hx i)),
    Formalism.L2.SG.Pf.WittFlags.WRowPin_holds (hF x hx i) (hI x hx i) (W5 Fm X x hx i) (H5 Fm X Y hF hI x hx i)
      (A5 Fm X Y hF hI hCT x hx i) (hV5 Fm X Y hF hI hCT x hx i),
    Formalism.L2.SG.Pf.FibreCounting.FibreCount_holds (Y x hx i)⟩

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem loop_evaluation_concrete (hFC : FrameChangeC) (hDU : DetUUC)
    (B : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' C1)
    (M : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (termRelationsOfFamily Fm X Y hF hI hCT x hx i) u u' C1 (B x hx i u u'))
    (hRk : ∀ Cg cb Cu cT CT C0 : ℝ, PX.RanksF Fm C0 Cg cb Cu cT CT) (hL3 : VanishingOnXAndXPlusMass.Conclusion3Family Fm)
    (hAdm : AdmRec Fm C1)
    (hVol : ∀ Cg cb Cu cT CT C0 Aa : ℝ, VanishingOnXAndXPlus.FamilyTermVolumeSmallCellBound Fm C1 (termRelationsOfFamily Fm X Y hF hI hCT)
      (YtF Fm C1 X Y hF hI (W5 Fm X) (H5 Fm X Y hF hI) (A5 Fm X Y hF hI hCT) (hV5 Fm X Y hF hI hCT)
        (hFCOf Fm X Y hF hI (W5 Fm X) hFC) B M) Cg cb Cu cT CT C0 Aa)
    (hAmp : BridgeLemma₂.FamilyAmplitudeBounds Fm C1) :
    RowLoopsEv0 Fm (termRelationsOfFamily Fm X Y hF hI hCT) (termRelationsBaseData Fm X Y hF hI hCT) := by
  intro Cg cb Cw cT CT C0 A
  have hR := BridgeLemma₂.family_gluing_bounds_of_beta Fm C1 (termRelationsOfFamily Fm X Y hF hI hCT)
    (YtF Fm C1 X Y hF hI (W5 Fm X) (H5 Fm X Y hF hI) (A5 Fm X Y hF hI hCT) (hV5 Fm X Y hF hI hCT)
      (hFCOf Fm X Y hF hI (W5 Fm X) hFC) B M) (family_admitted_of_parts Fm C1 _ _ hAdm hVol) hAmp
    (fun x hx i u u' => ⟨normTieC_holds (Fm.D x i) (X x hx i) (Y x hx i) (hF x hx i) (hI x hx i) (W5 Fm X x hx i) (H5 Fm X Y hF hI x hx i) (A5 Fm X Y hF hI hCT x hx i) (hV5 Fm X Y hF hI hCT x hx i) u u',
      gramDeterminant_of_unipotent_det hDU (Fm.D x i) (X x hx i) (Y x hx i) (hF x hx i) (hI x hx i) (W5 Fm X x hx i) (H5 Fm X Y hF hI x hx i) (A5 Fm X Y hF hI hCT x hx i) (hV5 Fm X Y hF hI hCT x hx i) u u',
      entryLatC_holds (Fm.D x i) (X x hx i) (Y x hx i) (hF x hx i) (hI x hx i) (W5 Fm X x hx i) (H5 Fm X Y hF hI x hx i) (A5 Fm X Y hF hI hCT x hx i) (hV5 Fm X Y hF hI hCT x hx i) u u',
      termInjF Fm C1 X Y hF hI (W5 Fm X) (H5 Fm X Y hF hI) (A5 Fm X Y hF hI hCT) (hV5 Fm X Y hF hI hCT)
        (hFCOf Fm X Y hF hI (W5 Fm X) hFC) B M x hx i u u'⟩)
    (fun x i => beta_l_unique (Fm.D x i))
  obtain ⟨C₀, HR⟩ := hR Cg cb Cw cT CT C0 A
  obtain ⟨C'₀, Cl₀, H⟩ := loop_evaluation_threshold_zero Formalism.FourierDecayAlt.P.loop_kernels Formalism.FourierDecayAlt.P.subfamilyAlt
    Formalism.HermitianLattices.Ext.L3.siegelMassRatio Cg cb Cw cT CT C0 A C₀
  exact ⟨C'₀, Cl₀, H Fm C1 _ _ (termRelationsBaseData Fm X Y hF hI hCT) HR
    (Formalism.MainNotions.BridgeLemma.formAt_family Fm Cg cb Cw cT CT C0 (hRk Cg cb Cw cT CT C0) hL3
      (hAdm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 Cg cb Cw cT CT C0 0).2.2.2.2.2.2.2.2.2.2.2.2.1)⟩

end Fam5

end Formalism.L2.SG.LoopsTies
