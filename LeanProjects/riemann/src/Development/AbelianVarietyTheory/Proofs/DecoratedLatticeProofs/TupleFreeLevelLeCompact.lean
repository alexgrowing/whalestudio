import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLev

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

def relax (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.PenBridge.plF J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i =>
      KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0)).comap (GlobalTheory.PenBridge.rd J j hj)

def U0 (a : GeoAll W u) (j : ℕ) (hj : j + 1 = B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) then
    relax h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥

theorem relax_le (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) : relax J j hj α ≤ GfC _ :=
  fun _ hg => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2

theorem tuple_free_level_le_compact (a : GeoAll W u) (j : ℕ) (hj : j + 1 = B.R.m) : U0 a j hj ≤ GfC _ := by
  unfold U0
  split_ifs
  · exact relax_le _ _ _ _
  · exact bot_le

theorem mem_relax_iff (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :
    g ∈ relax J j hj α ↔ g ∈ J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.PenBridge.plF J) ∧ g ∈ GfC _ ∧
      ∀ i, GlobalTheory.PenBridge.rd J j hj g i ∈ KO (J.G i).k _ := by
  simp only [relax, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, and_assoc]

theorem tuple_free_level_eq_relaxed (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) (hJ : J.Reads) (α : J.Ch j) :
    ∃ (t₀ : W.P.T) (J₀ : QJ a t₀) (α₀ : J₀.Ch j), J₀.Reads ∧ U0 a j hj = relax J₀ j hj α₀ := by
  have h : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2.some, h.choose_spec.choose_spec.1, ?_⟩
  unfold U0
  rw [dif_pos h]

end GlobalTheory.PenLev
end
