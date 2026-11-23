import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinColTOfPinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToBlocksMulFinZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexCouplingCosetStabilizerEqChartWeightStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryStepRelationStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PenVol

theorem relIndex_ne_zero_of_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K U U0 : Subgroup G)
    (hU0 : U0 ≤ K) (hc : IsCompact (U0 : Set G)) (ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K)) :
    U.relIndex U0 ≠ 0 := by
  haveI : CompactSpace U0 := isCompact_iff_compactSpace.1 hc
  have hcont : Continuous (fun x : U0 => (⟨x.1, hU0 x.2⟩ : K)) := Continuous.subtype_mk continuous_subtype_val _
  have ho' : IsOpen ((U.subgroupOf U0 : Subgroup U0) : Set U0) := ho.preimage hcont
  haveI : Finite (U0 ⧸ U.subgroupOf U0) := (U.subgroupOf U0).quotient_finite_of_isOpen ho'
  haveI : (U.subgroupOf U0).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.FiniteIndex.index_ne_zero

theorem wt_cast (C : ℕ → Type) (w : ∀ j, C j → ℂ) {j j' : ℕ} (h : j = j') (x : C j) :
    w j' (cast (congrArg C h) x) = w j x := by
  subst h; rfl

end GlobalTheory.PenVol

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.PenVol.pen_vol : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j, j + 1 = B.R.m → ∃ v : ℂ, v ≠ 0 ∧ ∀ t (J : QJ a t), J.Reads → ∀ α, (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj
  obtain ⟨U0, hU0le, hU0c, hU0⟩ := GlobalTheory.T.true_geometry_step_relation W hW u a ha haT j hj
  have hI : I.Ok := hW.tr.ok
  have hP : TC.Pins B X := hW.tr.pins.some
  have hjm : j ≤ B.R.m := by omega
  have key : ∀ t (J : QJ a t), J.Reads → ∀ α,
      GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) * ((J.A.U j (J.ι j α)).relIndex U0 : ℝ) =
        GlobalTheory.SeeSaw.volLev (a.g.x j).vol U0 ∧
      ((J.A.U j (J.ι j α)).relIndex U0 : ℂ) = J.wt j α ∧
      GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) ≠ 0 ∧ (J.A.U j (J.ι j α)).relIndex U0 ≠ 0 := by
    intro t J hR α
    obtain ⟨hle, hidx⟩ := hU0 t J hR α
    have hrep := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hP l Z u (W.P.I.tup t) J.Ch₀ J.A hR.is j hjm (J.ι j α)).1
    refine ⟨GlobalTheory.T.archimedeanLevelVolume_mul_relIndex (I.rec7 l Z) ((I.rec7 l Z).sp.X j) (a.g.x j).vol _ _ hle hU0le hU0c hrep.opn, ?_,
      GlobalTheory.AdForm.PinInhab.volLev_ne_zero hI haT.pinX.inf j (a.g.x j).vol (J.ι j α) hrep,
      GlobalTheory.PenVol.relIndex_ne_zero_of_open (GfC _) _ _ hU0le hU0c hrep.opn⟩
    rw [hidx, Nat.cast_prod, QJ.wt]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [GlobalTheory.T.relIndex_couplingCosetStabilizer_eq_chartWeight (J.G i) (J.E i)]
    exact GlobalTheory.PenVol.wt_cast _ (J.E i).wt (by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega) (α i)
  by_cases hex : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j)
  · obtain ⟨t0, J0, hR0, ⟨α0⟩⟩ := hex
    obtain ⟨h1, -, h3, h4⟩ := key t0 J0 hR0 α0
    refine ⟨(GlobalTheory.SeeSaw.volLev (a.g.x j).vol U0 : ℂ), ?_, fun t J hR α => ?_⟩
    · rw [← h1]; exact_mod_cast mul_ne_zero h3 (Nat.cast_ne_zero.2 h4)
    · obtain ⟨e1, e2, -, -⟩ := key t J hR α
      rw [← e2, ← e1]; push_cast; ring
  · exact ⟨1, one_ne_zero, fun t J hR α => absurd ⟨t, J, hR, ⟨α⟩⟩ hex⟩

end
