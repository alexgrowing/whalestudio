import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.KFinLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def FinMapsAt (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : FinMaps F a a') (v : Pl F) : Prop :=
  (SB _).map (R.p v) = ⊤ ∧ (SB _).map (R.p' v) = ⊤ ∧ augAt om v ≤ LinearMap.ker (R.p v) ∧
    augAt om' v ≤ LinearMap.ker (R.p' v) ∧
    (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
      R.p v φ = R.p' v φ' → R.p v φ₁ = R.p' v φ₁') ∧
    Nontrivial (R.Pi v) ∧
    (∀ N : Submodule ℂ (R.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ → R.p v φ ∈ N → R.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) ∧
    (v ∉ X.T → R.p v (G.M.vac v) = R.p' v (G.M'.vac v) ∧ R.p v (G.M.vac v) ≠ 0) ∧
    ∀ hv : v ∈ B.P, v ∈ X.T → IsZetaAt B G X R ⟨v, hv⟩

end GlobalTheory.KFinLoc

end
