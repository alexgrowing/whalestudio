import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField
open GlobalTheory.Size (l2O)
open scoped ENNReal NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Defs

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W))

structure IsBoundedCommutant (T : Module.End ℂ (WO V W → ℂ)) : Prop where
  pres : ∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (T f)
  bdd : ∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ V W f → l2O μ 𝓕 (T f) ≤ C * l2O μ 𝓕 f
  comm : ∀ w f, IsThetaFunO ψ V W f → T (heisO ψ V W w f) = heisO ψ V W w (T f)

variable {V W}

def L2DenseIn (M : Submodule ℂ (WO V W → ℂ)) (P : (WO V W → ℂ) → Prop) : Prop :=
  ∀ f, P f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g ∈ M, l2O μ 𝓕 (f - g) < ε

variable (V W)

def IsVac (θ : InfFam D) (sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sV τ) (sW τ)) f

def finSpan (f : WO V W → ℂ) : Submodule ℂ (WO V W → ℂ) :=
  Submodule.span ℂ {g | ∃ w : WO V W, w.map (infPart D) = 0 ∧ g = heisO ψ V W w f}

def CommutantScalar : Prop :=
  ∀ T : Module.End ℂ (WO V W → ℂ), IsBoundedCommutant ψ V W μ 𝓕 T →
    ∃ c : ℂ, ∀ f, IsThetaFunO ψ V W f → T f = c • f

def StableDense : Prop :=
  ∀ M : Submodule ℂ (WO V W → ℂ), (∀ f ∈ M, IsThetaFunO ψ V W f) → M ≠ ⊥ →
    (∀ w, ∀ f ∈ M, heisO ψ V W w f ∈ M) → L2DenseIn μ 𝓕 M (IsThetaFunO ψ V W)

def VacuumDense : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ τ, IsCartanInv (gramAt D V τ) (sV τ)) → (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) →
      ∀ f, IsVac ψ V W θ sV sW f → f ≠ 0 → L2DenseIn μ 𝓕 (finSpan ψ V W f) (IsVac ψ V W θ sV sW)

def VacuumDenseModel : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ),
    GlobalTheory.Chain.IsVacVec ψ θ M M' f → L2DenseIn μ 𝓕 (finSpan ψ V W f) (GlobalTheory.Chain.IsVacVec ψ θ M M')

end Defs

def HeisSchur (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      CommutantScalar ψ V W μ 𝓕 ∧ StableDense ψ V W μ 𝓕 ∧ VacuumDense ψ V W μ 𝓕

section Basic₂

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} {θ : InfFam D}

theorem VacuumDense.model (h : VacuumDense ψ V W μ 𝓕) : VacuumDenseModel ψ V W μ 𝓕 :=
  fun θ hθ _ _ M M' f hf g hg =>
    h θ hθ (cart M) (cart M') (GlobalTheory.Chain.VacVec.cart_isCartanInv M) (GlobalTheory.Chain.VacVec.cart_isCartanInv M') f
      ⟨hf.theta, hf.vac⟩ hf.ne g ⟨hg.theta, hg.vac⟩

theorem exists_isVac_ne_zero (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) (sV τ)) (hW : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) :
    ∃ f, IsVac ψ V W θ sV sW f ∧ f ≠ 0 := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ V W _ _ hV hW _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame _) (GlobalTheory.PlaceModel.isSelfDualC_latFrame _)
  have h := hf 1
  simp only [one_mul] at h
  exact ⟨f, ⟨h.1, h.2.2⟩, f0⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua

end
