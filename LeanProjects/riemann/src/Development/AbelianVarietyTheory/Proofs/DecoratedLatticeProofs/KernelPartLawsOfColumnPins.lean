import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIdentityAtEveryTupleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueChainKernelEqClassSumJetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelPairActionFiniteDatumLawStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTupleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCharExponentInfinityKernelShiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOOnb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOComb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LivechartKernelVectorsRealPointsDetPowersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiveChartsKernelEqClassSumJetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KerLaws

theorem clsKL_is : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Is := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  refine ⟨?forms, ?real, ?lev, ?core, ?kval⟩
  case lev =>
    intro j hj α γ κ κ'
    exact GlobalTheory.T.chartLevelPair_action_finiteDatum_law I hOk hPins l Z u a Ch₀ k.Ch A ι _ _ _ _ _ _ _ _ _ _ _ hX hP j hj α γ κ κ'
  case core =>
    intro j hj α γ a₁ a₂ P'
    have hs := hS j hj
    have h1 := GlobalTheory.T.thetaKernelIdentity_at_every_tuple I hOk hPins l Z u a Ch₀ k.Ch A ι _ _ _ _ _ _ _ _ _ _ _ hX hP j hj (s j) hs.2 α γ a₁ a₂ P'
    have hx1 := hX.xs j (Nat.le_of_succ_le hj)
    have hx2 := hX.xs (j + 1) hj
    simp only [Tup.ker, KerDat.pt, realOf, clsKL, tupOf, commOf, hx1.1, hx1.2.1, hx2.1, hx2.2.1, if_neg hs.1]
    exact h1
  case forms =>
    refine ⟨fun j hj β => ?_, fun j hj β => ?_, fun j hj φ hφ β c => ?_, fun j hj φ hφ β y γ hγ c k₁ hk κ y' htr => ?_⟩
    · exact (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hPins l Z u a Ch₀ A hP.is j hj (ι j β)).1
    · exact (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hPins l Z u a Ch₀ A hP.is j hj (ι j β)).2.1
    · have hR := ((hP.ram j hj φ).1 hφ).1.1
      exact (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hPins l Z u a Ch₀ A hP.is R.θ hX.inf j hj φ hR).1 c.1
    · have hR := ((hP.ram j hj φ).1 hφ).1.1
      have hx1 := hX.xs j hj
      have h2 := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hPins l Z u a Ch₀ A hP.is R.θ hX.inf j hj φ hR).2 (ι j β) y γ hγ c k₁ hk κ
        ⟨y'.1, y'.2⟩ (fun τ => by
          show y'.1 τ = _
          rw [htr τ]
          simp only [RealD.r, inN, inB, infM, realOf, commOf, hx1.2.1, inv_one, one_mul, mul_one]
          rfl)
      exact (congrFun (hP.rdq j hj β φ y) _).trans h2
  case real => exact GlobalTheory.T.livechart_kernelVectors_realPoints_detPowers I hOk hPins l Z u R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  case kval => exact GlobalTheory.T.liveCharts_kernel_eq_classSum_jets I hOk hPins l Z u R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP

end GlobalTheory.KerLaws
