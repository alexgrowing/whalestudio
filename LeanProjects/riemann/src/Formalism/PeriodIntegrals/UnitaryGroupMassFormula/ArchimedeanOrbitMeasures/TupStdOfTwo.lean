import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HermEuc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SquareChartC1Local

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def ChartD {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) (a : HmI X → MfI X) : Prop :=
  ∀ {η μ' : Type} [Fintype η] [Fintype μ'] (eH : HmI X ≃ₜ EuclideanSpace ℝ η)
    (eM : MfI X ≃ₜ EuclideanSpace ℝ μ'),
    (∀ x y, eH (x + y) = eH x + eH y) → (∀ x y, eM (x + y) = eM x + eM y) →
    ContDiffAt ℝ 1 (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) ∧
    ∀ v, fderiv ℝ (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) v =
      (1 / 2 : ℝ) • eM (TinvI X u' * ((eH.symm v : HmI X) : Matrix _ _ _))

def PolarMapContDiffAtBase : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → ChartD X u' hT a →
    ∀ {η : Type} [Fintype η] (eH : HmI X ≃ₜ EuclideanSpace ℝ η), (∀ S T, eH (S + T) = eH S + eH T) →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → PolarChartContDiffAt X u' hT a (kap0 X hb c L) eH

def TupDet : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → ChartD X u' hT a →
    ∀ {η : Type} [Fintype η] (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ), (∀ S T, eH (S + T) = eH S + eH T) →
    νinf.map eH = ENNReal.ofReal cν • volume →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → PsiDet X u' hT a (kap0 X hb c L) eH cν

theorem tupPieces_of (h1 : PolarMapContDiffAtBase) (h2 : TupDet) : TupPieces := by
  intro D X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω, a, hC, hD⟩ := square_chart_c1 X u' ψ hT μinf νinf fibInf hP
  obtain ⟨η, hη, eH, cν, hadd, hν⟩ := hermEuc X u' ψ hT μinf νinf fibInf hP
  refine ⟨Ω, a, hC, η, hη, eH, cν, hν, fun hb c S ι _ L hc hL => ⟨?_, ?_⟩⟩
  · exact h1 X u' ψ hT μinf νinf fibInf hP Ω a hC hD eH hadd hb c S L hc hL
  · exact h2 X u' ψ hT μinf νinf fibInf hP Ω a hC hD eH cν hadd hν hb c S L hc hL

theorem tupStd_of_two (h1 : PolarMapContDiffAtBase) (h2 : TupDet) : TupStd := tupStd_of_pieces (tupPieces_of h1 h2)

end PI.AprimeInfW
