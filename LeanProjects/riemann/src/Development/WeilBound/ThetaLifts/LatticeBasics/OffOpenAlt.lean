import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def OffOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsSkew σ B r s →
    ∀ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, (∀ h h', IsEmb h h' (e (h, h'))) → ∀ γ ∈ rat2 σ Y,
      (¬ ∃ δ ∈ ratU σ Y.J, γ * (e (1, δ))⁻¹ ∈ par2 σ Y) →
      ∃ U : Submodule E (Fin n → E), U ≠ ⊥ ∧ (∀ u ∈ U, ∀ u' ∈ U, form σ Y.J u u' = 0) ∧
        (∀ m ∈ PositivityTheory.ThKEnd.unipU σ Y U, ∃ t, IsPar (γ * e (1, m) * γ⁻¹) t ∧ Matrix.GeneralLinearGroup.det t = 1 ∧
          Matrix.GeneralLinearGroup.det m.1 = 1) ∧
        ∀ δ ∈ ratU σ Y.J, γ * e (1, δ) * γ⁻¹ ∈ par2 σ Y → ∀ m ∈ PositivityTheory.ThKEnd.unipU σ Y U, δ * m * δ⁻¹ ∈ PositivityTheory.ThKEnd.unipU σ Y U

def HtEmb : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n),
    ∃ C : ℝ≥0, (∀ h h' x, IsEmb (σ := σ) (Y := Y) h h' x → ht2 x ≤ C * (ht h * ht h')) ∧
      (∀ h h' : UA σ Y.J, ht (h * h') ≤ C * (ht h * ht h')) ∧ ∀ h : UA σ Y.J, 1 ≤ ht h

end GlobalTheory.ThK.Dbl

end
