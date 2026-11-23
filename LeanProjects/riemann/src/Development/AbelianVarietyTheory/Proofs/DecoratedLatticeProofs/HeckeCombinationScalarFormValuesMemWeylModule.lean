import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTupleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.TransAct

set_option maxHeartbeats 1000000 in

theorem trc_val_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ e : (I.stp u a j).Cl, (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e ∈ ValC (Gr B.fields.emb B.embLL (B.R.N j)) (Col2.lamT (B.hcW u) j) := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj c hc φ hφ hinv e
  have hR := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hP l Z u a Ch A hA j hj (A.chOf j e)).1
  have key : ∀ g, (fun z : (I.chain l u a).Y j =>
      A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) ∈
      ValC (Gr B.fields.emb B.embLL (B.R.N j)) (Col2.lamT (B.hcW u) j) := by
    intro g
    obtain ⟨γ, hγ, e', g', hg', κ, hκ, hdec⟩ := hR.dec (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)
    let U : (I.rec7 l Z).what₂.Tau → GL (Fin (B.R.N j)) ℂ := fun τ =>
      ((Matrix.isUnit_iff_isUnit_det _).2 (RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) g' τ)).unit
    have hfun : (fun z : (I.chain l u a).Y j =>
        A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) =
        (A.chi j (A.chOf j e) ⟨κ, hκ⟩ : ℂ) • GlobalTheory.Mem.ColAd.lT (Gr B.fields.emb B.embLL (B.R.N j)) U (φ e'.1) := by
      funext z
      rw [hdec]
      exact (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hP l Z u a Ch A hA θ hθ j hj φ hφ).2 (A.chOf j e) z γ hγ e' g' hg' ⟨κ, hκ⟩
        (GlobalTheory.Mem.ColAd.frL (Gr B.fields.emb B.embLL (B.R.N j)) U z) (fun τ => rfl)
    rw [hfun]
    exact Submodule.smul_mem _ _ (GlobalTheory.Mem.ColAd.lT_mem _ _ U (hφ e'.1).1)
  have hsum : (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) =>
      trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e =
      ∑ g ∈ c.support, c g • (fun z : (I.chain l u a).Y j =>
        A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) := by
    funext z
    simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (key g)

end GlobalTheory.AdForm.TransAct

end
