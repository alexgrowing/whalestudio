import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPins3RealTOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPinsRealTOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RecursionLocalRowConditionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleWitnessZeroSectionEqLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleWitnessConstantEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleWitnessPlacesEqImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelConjugateCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLocalLevelCharacterStatement

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.TieOfLink

theorem tie_of_rpk {D : D7} {O : Obj D} {c : ℝ} (b : Bundle D O c) {x : TwIn O.ex} (y : RealIn x b.R b.S) (r : RecIn y)
    (e : rpkB b = rpkX y)
    (hpsi : PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG)
    (h3 : RealPins3 (realTOf y)) (hp : ∃ pins : RealPins (realTOf y), RealRecPins pins (realRecOf r)) :
    Nonempty b.Comparison₂ := by
  have key : ∀ z : RPk b.R b.S, z = rpkX y → ∃ Rr : RealRec z.B.Q, PsiPPTie D z.P.P0 z.P.ψ0 z.P.Ps z.P.ψs z.P.I.eG ∧
      RealPins3 z.B.Q ∧ ∃ pins : RealPins z.B.Q, RealRecPins pins Rr := by
    rintro z rfl
    exact ⟨realRecOf r, hpsi, h3, hp⟩
  obtain ⟨Rr, h⟩ := key _ e
  exact ⟨⟨Rr, h⟩⟩

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

theorem tie_of_wit (q : WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c) (w : BWit q b)
    (hF0 : HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)))
    (hp : RealPins (realTOf w.y.y))
    (hloc : Formalism.IndefR.principalLevelFrame.RowLocPin b.R.T.n.gal.lp w.x.R.θ w.x.Y.PY (w.x.R.MY 0)
      (fun b => levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b)))
      (fun b => Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b))) (fun _ => w.x.R.e0) w.x.Y.eFT) :
    Nonempty b.Comparison₂ := by
  have hI := GlobalTheory.T.recursion_local_row_condition _ _ _ _ _ _ _ _ q.O.ex w.x b.R b.S w.y.y w.y.r
  have h3 : RealPins3 (realTOf w.y.y) := by
    obtain ⟨x, a, ax, y⟩ := w
    cases ax
    exact realPins3_realTOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.what₂ a b.R b.S y.y hF0
  exact tie_of_rpk b w.y.y w.y.r w.y.eq hI.2.2 h3 ⟨hp, hI.1 hp hloc⟩

theorem rowE_hasTie {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (Q : V4.Slot) :
    RowE Q (IsLinked p) fun _ => HasTie := by
  have hH := EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  refine ((((((GlobalTheory.T.bundle_witness_zero_section_eq_local hL p).and (GlobalTheory.T.bundle_witness_constant_eq hL p)).and (GlobalTheory.T.bundle_witness_places_eq_image hL p)).and (GlobalTheory.T.theta_level_conjugate_character hL p)).and (GlobalTheory.T.row_local_level_character hL p)).and hH).mono
    fun κ K _ h β _ c b hl => ?_
  obtain ⟨⟨⟨⟨⟨h0, hc⟩, hg⟩, ht⟩, hl'⟩, hh⟩ := h
  obtain ⟨q, b', ⟨w⟩, e⟩ := hl
  have eO : (⟨β.D, β.O⟩ : Σ D : D7, Obj D) = ⟨q.w.D q.Z, q.O⟩ := congrArg (fun s => (⟨s.1, s.2.1⟩ : Σ D : D7, Obj D)) e
  have hsc : q.O.L.sc = K.s := by
    have := congrArg (fun s : Σ D : D7, Obj D => s.2.L.sc) eO
    exact this.symm.trans β.sc
  have hfd := (hh (q.w.st q.Z) q.x.isOver).2.2.1
  have hp : RealPins (realTOf w.y.y) :=
    realPins_realTOf _ _ _ _ _ _ _ _ q.O.ex w.x b'.R b'.S w.y.y (hc q c b' w hsc) hfd (hg q c b' w hsc)
      (ht q c b' w hsc).1 (ht q c b' w hsc).2.1 (ht q c b' w hsc).2.2
  have h' : HasTie _ _ c b' := tie_of_wit q b' w (h0 q c b' w hsc) hp (hl' q c b' w hsc)
  have tr : ∀ s : Σ (D : D7) (O : Obj D), Bundle D O c, s = ⟨q.w.D q.Z, q.O, b'⟩ → HasTie s.1 s.2.1 c s.2.2 := by
    rintro s rfl; exact h'
  exact tr _ e

end GlobalTheory.Fc.TieOfLink
