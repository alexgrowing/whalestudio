import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.LocFinType
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE

noncomputable section

namespace SiegelEisensteinSeries

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

variable (σ) in

def growForms (Y : Spc F E n) : Set (modFun σ Y →ₗ[ℂ] ℂ) := {μ | IsGrowForm μ}

def EisHalf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ (t : ℝ) (v : ℂ → modFun σ Y), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) ((v s).1 x)) ∧
        WHolo (growForms σ Y) v {s | t < s.re}

def EisSys : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ (I : Type) (Ξ : LinSys (modFun σ Y) I) (t : ℝ) (v : ℂ → modFun σ Y), (∀ i, Differentiable ℂ (Ξ.c i)) ∧
        Ξ.LocFinType (growForms σ Y) Set.univ ∧ (∀ s : ℂ, t < s.re → Ξ.Sol s = {v s}) ∧
        ∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) ((v s).1 x)

end SiegelEisensteinSeries
