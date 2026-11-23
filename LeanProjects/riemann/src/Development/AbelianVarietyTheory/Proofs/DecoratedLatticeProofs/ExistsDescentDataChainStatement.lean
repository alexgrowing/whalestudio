import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDescentDataChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_data_chain : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → (∀ j, j + 1 < D.R.m → ∃ dG, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) dG ∧ ∀ t, ∃ dQ, IsDQ W t j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) dQ ∧ (f.row t).vP j = comb (pk W).ψ _ _ dQ (comb (pk W).ψ _ _ dG ((pk W).vac j))) ∧ ∀ j h, ∃ dG, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) dG ∧ ∀ t, ∃ dQ, IsDQ W t (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) dQ ∧ (f.row t).vT j h = comb (pk W).ψ _ _ dQ (comb (pk W).ψ _ _ dG (vacT (pk W) j h)) := by
  first | exact @GlobalTheory.StepSplit.main | exact GlobalTheory.StepSplit.main | (intros; apply GlobalTheory.StepSplit.main <;> assumption)
