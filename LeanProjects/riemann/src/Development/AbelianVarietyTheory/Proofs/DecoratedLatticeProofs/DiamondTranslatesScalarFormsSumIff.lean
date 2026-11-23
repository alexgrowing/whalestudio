import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RepresentativeDiamondTranslateSumScalarFormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiamondTranslateSumEqZeroOfChartRepresentativesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm

theorem diaSum_iff : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ((∀ b y, ∑ᶠ s, rTrans ((β j i).gl (g s)) (A.rd θ j hj b φ y) = 0) ↔
        ∀ c, ∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT j v s c (φ ((I.fm l u a).dil j v s c)) = 0) := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj φ hφ i v hv g hg
  have hfin : ∀ (f : 𝓀[k]ˣ → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ) x, (∑ᶠ s, f s) x = ∑ᶠ s, f s x :=
    fun f x => finsum_apply (Set.toFinite _) x
  constructor
  · intro H c
    funext y
    have h1 := congrFun (H (A.chOf j c) y) (A.h j _ ⟨c, rfl⟩)
    rw [hfin] at h1
    simp only [GlobalTheory.MixPer.rTrans] at h1
    rw [GlobalTheory.T.representative_diamond_translate_sum_scalarForm I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj φ hφ i v hv g hg _ y ⟨c, rfl⟩] at h1
    simpa using h1
  · intro H b y
    funext x
    rw [hfin]
    simp only [GlobalTheory.MixPer.rTrans, Pi.zero_apply]
    refine GlobalTheory.T.diamondTranslateSum_eq_zero_of_chartRepresentatives I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj φ hφ i v hv g hg b y (fun c y' => ?_) x
    rw [GlobalTheory.T.representative_diamond_translate_sum_scalarForm I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj φ hφ i v hv g hg b y' c, H c.1]
    rfl

end GlobalTheory.AdForm
