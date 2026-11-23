import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

namespace GlobalTheory.CoinvKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

def IsStabW (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  N ≤ A ∧ (∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N) ∧
    (∀ k ∈ KInf σ W emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N) ∧
    ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def HasRelY (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  (∀ v : Pl F, ∀ g ∈ UAt σ Y (evFin F v), ∀ Φ ∈ A, om (g, 1) Φ - Φ ∈ N) ∧
    (∀ k ∈ KInf σ Y emb, ∀ Φ ∈ A, om (k, 1) Φ - Φ ∈ N) ∧
    ∀ γ ∈ Lines σ Y, ∀ Φ ∈ A, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def IsThetaSub (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  IsStabW om emb A N ∧ HasRelY om emb A N

end GlobalTheory.CoinvKer

end
