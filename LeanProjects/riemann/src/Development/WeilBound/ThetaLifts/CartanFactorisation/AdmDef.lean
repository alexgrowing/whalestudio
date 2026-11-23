import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def AdmAt (om : Rep σ X W) (v : Pl F) : Prop :=
  ∀ U ∈ 𝓝 (1 : UA σ W.J), ∃ t : Finset (((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
    ∀ l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ, augAt om v ≤ LinearMap.ker l →
      (∀ h ∈ U, h ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → l φ₁ = l φ) →
      ∃ l' ∈ Submodule.span ℂ (t : Set (((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ)), ∀ φ ∈ SB _, l φ = l' φ

def AdmTri : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, AdmAt om v ∧ AdmAt om' v

end PositivityTheory.ThKF

end
