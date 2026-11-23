import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsFinalS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FamRaise
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BetaLUniq

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SelQ

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def QS {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : Prop :=
  ∃ h0 : (sel Fm hc).1 ≤ x, ∃ _ : FinX ((sel Fm hc).2 x hx h0 i).Y,
    ConcTie ((sel Fm hc).2 x hx h0 i).X ((sel Fm hc).2 x hx h0 i).Y

variable {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm)

def atS (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (hq : QS sel Fm hc x hx i) : TermTie (Fm.D x i) :=
  atOf ((sel Fm hc).2 x hx hq.fst i).X ((sel Fm hc).2 x hx hq.fst i).Y hq.snd.fst
    (((sel Fm hc).2 x hx hq.fst i).hI hq.snd.fst) hq.snd.snd

def ccS (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (hq : QS sel Fm hc x hx i) :
    ConcAt0 (Fm.D x i) (atS sel Fm hc x hx i hq) :=
  ccOf ((sel Fm hc).2 x hx hq.fst i).X ((sel Fm hc).2 x hx hq.fst i).Y hq.snd.fst
    (((sel Fm hc).2 x hx hq.fst i).hI hq.snd.fst) hq.snd.snd

def YtS (hFC : FrameChangeC) (C1 : ℝ)
    (B : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), QS sel Fm hc x hx i → ∀ (u u' : (Fm.D x i).what₂.Word),
      LoopLocDat (Fm.D x i) (Fm.L x i) u u' C1)
    (M : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (hq : QS sel Fm hc x hx i) (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (atS sel Fm hc x hx i hq) u u' C1 (B x hx i hq u u'))
    (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (hq : QS sel Fm hc x hx i) (u u' : (Fm.D x i).what₂.Word) :
    LoopTie (Fm.D x i) (Fm.L x i) (atS sel Fm hc x hx i hq) u u' C1 :=
  loopTieOfParts
    (loopRowsOf (wOf ((sel Fm hc).2 x hx hq.fst i).X) (((sel Fm hc).2 x hx hq.fst i).hI hq.snd.fst)
      (hOf _ ((sel Fm hc).2 x hx hq.fst i).Y hq.snd.fst _)
      (aOf _ ((sel Fm hc).2 x hx hq.fst i).Y hq.snd.fst _ hq.snd.snd)
      (hvOf _ ((sel Fm hc).2 x hx hq.fst i).Y hq.snd.fst _ hq.snd.snd)
      (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds (Fm.D x i)) u u'
      (frameEqvInj_of (wOf ((sel Fm hc).2 x hx hq.fst i).X) (((sel Fm hc).2 x hx hq.fst i).hI hq.snd.fst)
        (hOf _ ((sel Fm hc).2 x hx hq.fst i).Y hq.snd.fst _)
        (aOf _ ((sel Fm hc).2 x hx hq.fst i).Y hq.snd.fst _ hq.snd.snd)
        (hvOf _ ((sel Fm hc).2 x hx hq.fst i).Y hq.snd.fst _ hq.snd.snd)
        (hFC _ _ _ hq.snd.fst (((sel Fm hc).2 x hx hq.fst i).hI hq.snd.fst) _) u u'))
    (B x hx i hq u u') (M x hx i hq u u')

end SelQ

section Closed

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞)

theorem cOut_take {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).take 16 = Fm.cOut := by
  unfold FamP.cOut; simp

theorem constant_list_cylinder {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 6 0 = Fm.CYL := by
  unfold FamP.cOut; simp

theorem constant_list_trace {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 13 0 = Fm.CTu := by
  unfold FamP.cOut; simp

def RowsFQ (hFC : FrameChangeC) (C1f C₀f : List ℝ → ℝ)
    (B : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (i : Fm.Ix x), QS sel Fm hc x hx i →
      ∀ (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut))
    (M : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (i : Fm.Ix x) (hq : QS sel Fm hc x hx i)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (atS sel Fm hc x hx i hq) u u' (C1f Fm.cOut) (B Fm hc x hx i hq u u')) : Prop :=
  ∀ aF : List ℝ → ℝ, Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, ∀ C : ℝ, C₀f Fm.cOut ≤ C →
    OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) (hq : QS sel Fm hc x hx i) (u u' : (Fm.D x i).what₂.Word),
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) →
        Formalism.MainNotions.BridgeLemma.RowsND (atS sel Fm hc x hx i hq)
                  (YtS sel Fm hc hFC (C1f Fm.cOut) (B Fm hc) (M Fm hc) x hx i hq u u') C ∧
          Formalism.MainNotions.BridgeLemma.RowsDeg (atS sel Fm hc x hx i hq)
            (YtS sel Fm hc hFC (C1f Fm.cOut) (B Fm hc) (M Fm hc) x hx i hq u u') C ∧
          Formalism.MainNotions.BridgeLemma.RowsOne (atS sel Fm hc x hx i hq)
            (YtS sel Fm hc hFC (C1f Fm.cOut) (B Fm hc) (M Fm hc) x hx i hq u u') C

end Closed

section Raised

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞)
  (yF : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → ℝ)

def YFOK : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x), yF Fm hc ≤ x →
    ∀ i : Fm.Ix x, FinX ((sel Fm hc).2 x hx h0 i).Y ∧ Formalism.L2.SG.WuDecay.WuDecay ((sel Fm hc).2 x hx h0 i).X

def yR {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) : ℝ := max (sel Fm hc).1 (yF Fm hc)

theorem h0R {eps : ℝ} {Fm : FamP eps} {hc : 𝒞 Fm} {x : ℝ} (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) :
    (sel Fm hc).1 ≤ x :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans hx.le

theorem hyR {eps : ℝ} {Fm : FamP eps} {hc : 𝒞 Fm} {x : ℝ} (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) :
    yF Fm hc ≤ x :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans hx.le

def AtR (hyF : YFOK sel yF) {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x)
    (i : Fm.Ix x) : TermTie (Fm.D x i) :=
  atOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1
    (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2

def CcR (hyF : YFOK sel yF) {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x)
    (i : Fm.Ix x) : ConcAt0 (Fm.D x i) (AtR sel yF hyF Fm hc x hx i) :=
  ccOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1
    (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem loopRowS_of_raised (hyF : YFOK sel yF) (C1f : List ℝ → ℝ) (C₀f : (List ℝ → ℝ) → List ℝ → ℝ)
    (Yt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut))
    (hRowsF : ∀ aF : List ℝ → ℝ, Closed 𝒞 fun Fm CH => ∀ hc : 𝒞 Fm, ∀ C : ℝ, C₀f aF (Fm.cOut ++ Fm.cMid CH) ≤ C →
      OwnEv Fm fun C' Cl x i => ∀ (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (u u' : (Fm.D x i).what₂.Word),
        Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) →
          Formalism.MainNotions.BridgeLemma.RowsND (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsDeg (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsOne (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C)
    (hForm : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      Hyp0 (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :
    LoopRowS C0 𝒞 sel := by
  intro aF
  choose f g hfg using fun p : ℝ × ℝ × ℝ × ℝ =>
    loop_evaluation_threshold_zero Formalism.FourierDecayAlt.P.loop_kernels Formalism.FourierDecayAlt.P.subfamilyAlt Formalism.HermitianLattices.Ext.L3.siegelMassRatio
      (p.1 + 1) (1 / 4) 3 (1 / 2) p.2.1 C0 p.2.2.1 p.2.2.2
  let par : List ℝ → ℝ × ℝ × ℝ × ℝ := fun l => (l.getD 6 0, l.getD 13 0, aF (l.take 16), C₀f aF l)
  obtain ⟨e1, he1, H1⟩ := hRowsF aF
  obtain ⟨e2, he2, H2⟩ := hForm
  refine ⟨min e1 e2, lt_min he1 he2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := H1 eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := H2 eps he (hle.trans (min_le_right _ _))
  let K4 : TransportedAlt := ⟨0, fun _ => 0, fun _ => 0, fun l => max (f (par l)) (g (par l))⟩
  refine ⟨(K1.sup K2).sup K4, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL12, hL4⟩ := (Fm.large_sup _ _ CH).1 hL
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL12
  intro hc'
  have epar : par (Fm.cOut ++ Fm.cMid CH) = (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) := by
    simp only [par, constant_list_cylinder, constant_list_trace, cOut_take]
  have hthr : ∀ c ∈ Fm.cLast, max (f (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)))
      (g (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH))) ≤ c := by
    intro c hc0
    have := hL4.2.2.2 c hc0
    simpa only [K4, epar] using this
  have hC' : f (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) ≤ sC' Fm :=
    (le_max_left _ _).trans (hthr _ (by unfold FamP.cLast sC'; simp))
  have hCl : g (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) ≤ sCl Fm := by
    have h := fun c hc => (le_max_right _ _).trans (hthr c hc)
    unfold sCl
    refine le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
      (le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
        (le_min (h _ (by unfold FamP.cLast; simp)) (h _ (by unfold FamP.cLast; simp))))))
  have hE := hfg (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) (Fm.raise (yR sel yF Fm hc')) (C1f Fm.cOut)
    (AtR sel yF hyF Fm hc') (Yt Fm hc') (CcR sel yF hyF Fm hc') (hK1 Fm CH hc hL1 hc') (hK2 Fm CH hc hL2)
  obtain ⟨x0, H⟩ := hE
  refine ⟨max x0 (yR sel yF Fm hc' + 1), fun x hx0 i => ?_⟩
  intro hx h0 u u' hH hCT hA
  have hx' : (Fm.raise (yR sel yF Fm hc')).x1 < x := by
    show max Fm.x1 (yR sel yF Fm hc') < x
    refine max_lt hx ?_
    have := (le_max_right _ _).trans hx0
    linarith
  exact H x ((le_max_left _ _).trans hx0) i hC' hCl hx' u u' hH hCT hA

theorem constant_list_gamma {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam := by
  unfold FamP.cOut FamP.cMid; simp

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem loopRowS_of_U (hyF : YFOK sel yF) (C1f : List ℝ → ℝ) (Uf : (List ℝ → ℝ) → List ℝ → Formalism.L2.SG.RowsU.UC)
    (Yt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut))
    (hAdmR : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm,
      VanishingOnXAndXPlus.AdmF (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc) (Yt Fm hc))
    (hUR : ∀ aF : List ℝ → ℝ, Closed 𝒞 fun Fm CH => ∀ hc : 𝒞 Fm,
      Formalism.L2.SG.RowsU.UAdm (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc) (Yt Fm hc)
        (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) (Uf aF (Fm.cOut ++ Fm.cMid CH)))
    (hTR : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm,
      Formalism.MainNotions.BridgeLemma₂.rows_TiesF (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc) (Yt Fm hc) ∧
      ∀ x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
        Formalism.MainNotions.BridgeLemma₂.wordPairTermInjective (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u'))
    (hForm : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      Hyp0 (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :
    LoopRowS C0 𝒞 sel := by
  refine loopRowS_of_raised C0 sel yF hyF C1f
    (fun aF l => Formalism.L2.SG.RowsU.c0U (l.getD 13 0) (aF (l.take 16)) C0 (l.getD 17 0) (Uf aF l)) Yt ?_ hForm
  intro aF
  obtain ⟨e, he, H⟩ := hAdmR.and ((hUR aF).and hTR)
  refine ⟨e, he, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := H eps h1 h2
  refine ⟨K, fun Fm CH hc hL hc' C hC => ?_⟩
  obtain ⟨hA, hU, hT⟩ := hK Fm CH hc hL
  rw [constant_list_trace, cOut_take, constant_list_gamma] at hC
  exact Formalism.L2.SG.RowsU.rowsFU (Fm.raise (yR sel yF Fm hc')) (C1f Fm.cOut) (AtR sel yF hyF Fm hc') (Yt Fm hc')
    (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) (hA hc') (hT hc').1 (hT hc').2
    (fun x i => _root_.beta_l_unique (Fm.D x i)) _ (hU hc') C hC

end Raised

end Formalism.L2.SG.LoopsTies
