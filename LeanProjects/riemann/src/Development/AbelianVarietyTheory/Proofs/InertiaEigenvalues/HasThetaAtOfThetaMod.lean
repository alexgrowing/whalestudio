import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod

noncomputable section

namespace GlobalTheory.RefPair

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain GlobalTheory.NPin GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def HasThetaAt (D : D7) {μt : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μt j) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (X : RowMod D rep j) (μ η : HChar D.host.E) : Prop :=
  ∃ (Ω : Type) (_ : AddCommGroup Ω) (_ : Module ℂ Ω) (ω : GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ Ω)
    (Λ : Ω →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ) (φ₀ : Ω),
    (∀ h g φ (F F' : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)) (y y' : ↥X.C),
      (F' : GAf D.host.E D.R.nV → Mr.wt.W) = NG.rt D.host.E D.R.nV h F → (y' : X.A) = X.ρ g y →
      Λ (ω (h, g) φ) F' y' = Λ φ F y) ∧
    (∀ x y (F : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)), (F : GAf D.host.E D.R.nV → Mr.wt.W) = Mr.real x →
      inner ℂ y (D.what₂.thetaP μt j x) = Λ φ₀ F ⟨X.φ y, X.φ_mem y⟩) ∧
    ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw →
      φ₀ ∈ ⨆ (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Ω)
        (_ : IsLinAt ω s μw ηw ι), LinearMap.range ι

end GlobalTheory.RefPair

end
