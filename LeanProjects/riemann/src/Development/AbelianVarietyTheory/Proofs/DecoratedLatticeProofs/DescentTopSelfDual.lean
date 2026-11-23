import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumOfCarriesLatticeCompletions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.TopVac

section Fam

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

theorem isWeil_top (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : ∃ χS χT, IsWeilDatumO (pk W).ψ (Yc D (j + 1)) D.sp.X' χS χT
    (omT (pk W) W.P.A3.A.μ0 j h) := by
  have hω := W.Q.charW.base.chain.ωX W.P.A3.A.μ0
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (pk W).ψ (Yc D n) D.sp.X'
      (Lift.chrStep ((pk W).toLevCh.mu W.P.A3.A.μ0) (pk W).eta D.R.m).1
      (Lift.chrStep ((pk W).toLevCh.mu W.P.A3.A.μ0) (pk W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((pk W).ωX W.P.A3.A.μ0) e) := by
    intro n e
    subst e
    exact hω
  exact ⟨_, _, key _ (GlobalTheory.Fam.idx_top h)⟩

end Fam

theorem moved_vacuum : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ j (h : j + 2 * 0 + 2 = D.R.m) d₀, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d₀ → IsSelfDualC (Yc D (j + 1)) ((pk W).ΛY (j + 1)) ∧ IsSelfDualC D.sp.X' (pk W).ΛX ∧ ∃ M : GlobalTheory.FinPl.Lat (Yc D (j + 1)), IsSelfDualC (Yc D (j + 1)) M ∧ (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((pk W).ΛY (j + 1)) M P) ∧ GlobalTheory.FinPl.Vac f.c.ψ (Yc D (j + 1)) D.sp.X' M f.g.LT (fun _ => True) (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk _ v hv hVT j h d₀ hd₀
  have hLev := hPk.bot.hyp.2.2.2.1.lev
  have sdY : IsSelfDualC (Yc D (j + 1)) ((pk W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (pk W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  obtain ⟨M, hM, hmov⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sdY).1 (f.g.b (j + 1))
  obtain ⟨χS, χT, hWe⟩ := isWeil_top W j h
  have sdT : IsSelfDualC D.sp.X' f.g.LT := hVT.bT.2 ▸ hv.sdT
  refine ⟨sdY, sdX, M, hM, hmov, ?_⟩
  exact GlobalTheory.VacMove.vac_of_moves D (pk W).ψ _ _ χS χT _ hWe _ _ sdY sdX _ _ ⟨hd₀.2.1.2.theta, hd₀.2.1.2.lat⟩ _ _ M f.g.LT hM sdT
    (hmov _) (hVT.movesT _)

end GlobalTheory.TopVac

end
