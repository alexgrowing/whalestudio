import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.BadQNotOver
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

namespace GlobalTheory.ServedPlace

theorem places_prime : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v ∧
        (∀ w' ∈ Formalism.L2.Forms.badQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)), (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal) ∧
        ¬ (w.D Z).what₂.places.resChar v ∣ ((w.D Z).mem u).A.T := by
  intro K B f T w hK hF hP Z t Wt nch n Y hMu hQ O hO hU E hE Fl hfl hw u v hg hμ tt hStd
  have hok : Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v := by
    intro w' hw' hpw
    obtain ⟨P0, hP0, hu⟩ := (tt.ch.Q_iff _ w').1 hw'
    rw [n.xi] at hu
    have hq := GlobalTheory.Mem.ReadTwist.mem_qprime_iff (w.ok.xi_reads ((w.D Z).what₂.muAt v)) w'
    have hab : P0.under (𝓞 (w.D Z).host.F) = w' := by
      unfold Formalism.L2.Host.aboveF at hP0
      rw [Set.Finite.mem_toFinset] at hP0
      exact hP0
    have hv := hq.2 ⟨P0, hab, hu⟩
    have hPQ : w.I.sel w' ∈ ColIn.Q w.I ((w.D Z).what₂.muAt v) :=
      (Formalism.L2.Col.mem_QE w.I.sel (w.I.tup _) _).2 ⟨w', hv, rfl⟩
    have hund : (w.I.sel w').under (𝓞 B.host.F) = w' := GlobalTheory.TwistPlaces.under_eq_iff.2 (w.ok.sel_ok w')
    have hp : Nat.Prime ((w.D Z).what₂.places.resChar v) := hg.1
    have hmem : ((((w.D Z).what₂.places.resChar v : ℕ)) : 𝓞 B.host.E) ∈ (w.I.sel w').asIdeal := by
      rw [← hund] at hpw
      have := hpw
      simp only [HeightOneSpectrum.under, Ideal.under, Ideal.mem_comap, map_natCast] at this
      exact this
    have hQp := (hQ ((w.D Z).what₂.muAt v) ((w.D Z).what₂.places.resChar v)).2 ⟨hp, w.I.sel w', hPQ, hmem⟩
    exact Y.Qp_muAt v hQp
  exact ⟨hok, fun w' hw' => Formalism.MainNotions.G.CmpJ.badQ_notOver u v hg _ hok w' hw', hg.2.2.2.2.2⟩

end GlobalTheory.ServedPlace
