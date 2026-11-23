import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceBoxProductInnerFactorizes
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOOneOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledSpace_boxProduct_inner_factorizes : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D),
    ∃ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T))) (𝓕 : Set (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T)))
      (μ₁ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕₁ : Set (Formalism.IndefR.Datum.WO S T)),
      μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL (GlobalTheory.Doubling.dblSp T) S) 𝓕 μ ∧
      μ₁.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL T S) 𝓕₁ μ₁ ∧
      ∀ a a' b b' : Formalism.IndefR.Datum.WO S T → ℂ, Formalism.IndefR.Datum.IsThetaFunO ψ S T a → Formalism.IndefR.Datum.IsThetaFunO ψ S T a' →
        Formalism.IndefR.Datum.IsThetaFunO ψ S T b → Formalism.IndefR.Datum.IsThetaFunO ψ S T b' →
        ∫ w in 𝓕, GlobalTheory.DblBox.box a b w * star (GlobalTheory.DblBox.box a' b' w) ∂μ =
          (∫ u in 𝓕₁, a u * star (a' u) ∂μ₁) * star (∫ u in 𝓕₁, b u * star (b' u) ∂μ₁) := by
  first | exact @GlobalTheory.DblBoxHaar.box_integral | exact GlobalTheory.DblBoxHaar.box_integral | (intros; apply GlobalTheory.DblBoxHaar.box_integral <;> assumption)
