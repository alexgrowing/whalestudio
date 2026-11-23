import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.StepSplit

theorem main : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → (∀ j, j + 1 < D.R.m → ∃ dG, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) dG ∧ ∀ t, ∃ dQ, IsDQ W t j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) dQ ∧ (f.row t).vP j = comb (pk W).ψ _ _ dQ (comb (pk W).ψ _ _ dG ((pk W).vac j))) ∧ ∀ j h, ∃ dG, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) dG ∧ ∀ t, ∃ dQ, IsDQ W t (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) dQ ∧ (f.row t).vT j h = comb (pk W).ψ _ _ dQ (comb (pk W).ψ _ _ dG (vacT (pk W) j h)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR
  have hlev := W.Q.charW.base.lev
  refine ⟨fun j hj => ?_, fun j h => ?_⟩
  · have hv := (hR.row W.P.A3.A.μ0).vP j hj
    obtain ⟨dG, hG, hQ⟩ := GlobalTheory.T.self_dual_frame_vacuum_step W u hP j (by omega) (Yc D (j + 1)) _ ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1))
      ((pk W).βY (j + 1)) ((pk W).vac j) (Or.inr (hlev.βY (j + 1) hj)) hv.1
    refine ⟨dG, hG, fun t => ?_⟩
    obtain ⟨dQ, hdQ, hiff⟩ := hQ t
    exact ⟨dQ, hdQ, (hiff _).1 ((hR.row t).vP j hj)⟩
  · have hm : D.R.m = j + 1 + 1 := by omega
    have hv := (hR.row W.P.A3.A.μ0).vT j h
    obtain ⟨dG, hG, hQ⟩ := GlobalTheory.T.self_dual_frame_vacuum_step W u hP (j + 1) (by omega) D.sp.X' _ (pk W).MX (pk W).ΛX (pk W).βX
      (vacT (pk W) j h) (Or.inl hlev.βX) hv.1
    refine ⟨dG, hG, fun t => ?_⟩
    obtain ⟨dQ, hdQ, hiff⟩ := hQ t
    refine ⟨dQ, hdQ, (hiff _).1 ?_⟩
    have hvt := (hR.row t).vT j h
    have e : (pk W).chi D.R.m = (pk W).chi (j + 1 + 1) := congrArg _ hm
    rw [e] at hvt
    exact hvt

end GlobalTheory.StepSplit
