import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartPointRightTranslateStabilizerSplitPlaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChOfDil
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartScalarFormAdelicPointEqClassTransportStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnCharts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlMemGfC
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdForm.rd_dia_sum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b y (c : {c // A.chOf j c = b}), (∑ᶠ s, A.rd θ j hj b φ y (A.h j b c * (β j i).gl (g s))) = (∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT j v s c.1 (φ ((I.fm l u a).dil j v s c.1))) y := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hT j hj φ hφ i v hv g hg b y c
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_chartPoint_rightTranslate_stabilizer_splitPlace I hok hpins l Z u a Ch A hA k ι p β Q L hT j hj i v hv g hg b c
  have hs : ∀ s, A.rd θ j hj b φ y (A.h j b c * (β j i).gl (g s)) =
      (I.fm l u a).dilT j v (e s) c.1 (φ ((I.fm l u a).dil j v (e s) c.1)) y := by
    intro s
    obtain ⟨z, hz, hpt⟩ := he s
    have hG : A.h j b c * (β j i).gl (g s) ∈ GfC _ := mul_mem (hA.h j hj b c).1 (GlobalTheory.FrameGfCImg.gl_mem_GfC (β j i) (g s))
    have hch : A.chOf j ((I.stp u a j).cl c.1.1 (((I.atIn u a).A j).diaPt v (e s) c.1)) = b :=
      (GlobalTheory.AdForm.chOf_dil I hok hpins l Z u a Ch A hA j hj v (e s) c.1).trans c.2
    have hco : cosetIn (GlobalTheory.Mem.Col2.DiaChart.dp I u a j v (e s) c.1) =
        cosetIn ((I.stp u a j).rep ((I.stp u a j).cl c.1.1 (GlobalTheory.Mem.Col2.DiaChart.dp I u a j v (e s) c.1))) :=
      (GlobalTheory.Mem.Col2.DiaChart.cosetIn_dia _ v (e s)).trans (GlobalTheory.Mem.Col2.DiaChart.cosetIn_rep I l u a j v (e s) c.1).symm
    exact GlobalTheory.T.chartScalarForm_adelicPoint_eq_classTransport I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b c.1 _ _ z hG hz hpt hch hco y
  rw [finsum_congr hs]
  rw [finsum_comp_equiv e (f := fun s' => (I.fm l u a).dilT j v s' c.1 (φ ((I.fm l u a).dil j v s' c.1)) y)]
  rw [finsum_apply]
  exact Set.toFinite _
