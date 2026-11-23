import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf

noncomputable section

namespace GlobalTheory.IndLine

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def KEqOn (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (V : Submodule ℂ P) (T : P →ₗ[ℂ] P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f ∈ V →
    ∀ g ∈ M.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) g g₁ → T (p f) = p g →
      T (p f₁) = p g₁

end GlobalTheory.IndLine
