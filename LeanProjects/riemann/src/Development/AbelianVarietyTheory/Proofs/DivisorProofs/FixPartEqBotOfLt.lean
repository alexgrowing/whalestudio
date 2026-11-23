import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId

noncomputable section

namespace GlobalTheory.IndLine

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def IsKFix (B : Base F E) (om : Rep σ Y W) (f : SInf F (Fin n × Fin d)) : Prop :=
  ∀ k ∈ KInf σ Y B.emb, Acts (evI F) (om (k, 1)) f f

def fixPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (m : ℕ) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Submodule.span ℂ {f | f ∈ fockDeg M B.ψ B.emb m ∧ IsKFix B om f}

def fixDeg (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) : ℕ :=
  sInf {m | ∃ f ∈ fockDeg M B.ψ B.emb m, f ≠ 0 ∧ IsKFix B om f}

def KStabUp (B : Base F E) (om : Rep σ Y W) (H : Submodule ℂ (SInf F (Fin n × Fin d))) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ f ∈ H, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ H

theorem fixPart_le_pol (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (m : ℕ) :
    fixPart B M om m ≤ M.Pol B.ψ B.emb :=
  Submodule.span_le.2 fun _ hf => fockDeg_le_pol M B.ψ B.emb m hf.1

theorem fixPart_eq_bot_of_lt (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {m : ℕ} (hm : m < fixDeg B M om) :
    fixPart B M om m = ⊥ := by
  rw [fixPart, Submodule.span_eq_bot]
  intro f hf
  by_contra h
  exact Nat.notMem_of_lt_sInf hm ⟨f, hf.1, h, hf.2⟩

end GlobalTheory.IndLine
