import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead
open scoped TensorProduct

namespace GlobalTheory.ProdReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V₀ V₁ V₂ V₃ V₄ V₅ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] [AddCommGroup V₄] [Module ℂ V₄]
  [AddCommGroup V₅] [Module ℂ V₅]

theorem ind₂_congr_right_prod {a b c N M : ℕ} (h : a + M = N) (h' : b + c = M)
    (ρ₀ : Representation ℂ (GL (Fin a) k) V₀) (ρ₁ : Representation ℂ (GL (Fin b) k) V₁)
    (ρ₂ : Representation ℂ (GL (Fin c) k) V₂) (μ : Representation ℂ (GL (Fin M) k) V₃)
    (φ : Nonempty (μ.Equiv (ind₂ (stdSum h') (extTensor ρ₁ ρ₂)))) :
    Nonempty ((ind₂ (stdSum h) (extTensor ρ₀ μ)).Equiv
      (ind₂ (stdSum h) (extTensor ρ₀ (ind₂ (stdSum h') (extTensor ρ₁ ρ₂))))) :=
  ind₂_congr h (eqv_refl ρ₀) φ

theorem ind₂_congr_left_prod {a b c N M : ℕ} (h : M + c = N) (h' : a + b = M)
    (ρ₁ : Representation ℂ (GL (Fin a) k) V₁) (ρ₂ : Representation ℂ (GL (Fin b) k) V₂)
    (ρ₃ : Representation ℂ (GL (Fin c) k) V₃) (μ : Representation ℂ (GL (Fin M) k) V₀)
    (φ : Nonempty (μ.Equiv (ind₂ (stdSum h') (extTensor ρ₁ ρ₂)))) :
    Nonempty ((ind₂ (stdSum h) (extTensor μ ρ₃)).Equiv
      (ind₂ (stdSum h) (extTensor (ind₂ (stdSum h') (extTensor ρ₁ ρ₂)) ρ₃))) :=
  ind₂_congr h φ (eqv_refl ρ₃)

theorem ind₂_congr_left_prod₂ {a b c d e N M : ℕ} (h : M + e = N) (h₁ : a + b = M) (h₂ : c + d = M)
    (ρ₁ : Representation ℂ (GL (Fin a) k) V₁) (ρ₂ : Representation ℂ (GL (Fin b) k) V₂)
    (ρ₃ : Representation ℂ (GL (Fin c) k) V₃) (ρ₄ : Representation ℂ (GL (Fin d) k) V₄)
    (ρ₅ : Representation ℂ (GL (Fin e) k) V₅)
    (φ : Nonempty ((ind₂ (stdSum h₁) (extTensor ρ₁ ρ₂)).Equiv (ind₂ (stdSum h₂) (extTensor ρ₃ ρ₄)))) :
    Nonempty ((ind₂ (stdSum h) (extTensor (ind₂ (stdSum h₁) (extTensor ρ₁ ρ₂)) ρ₅)).Equiv
      (ind₂ (stdSum h) (extTensor (ind₂ (stdSum h₂) (extTensor ρ₃ ρ₄)) ρ₅))) :=
  ind₂_congr h φ (eqv_refl ρ₅)

theorem ind₂_congr_right_prod₂ {a b c d e N M : ℕ} (h : e + M = N) (h₁ : a + b = M) (h₂ : c + d = M)
    (ρ₁ : Representation ℂ (GL (Fin a) k) V₁) (ρ₂ : Representation ℂ (GL (Fin b) k) V₂)
    (ρ₃ : Representation ℂ (GL (Fin c) k) V₃) (ρ₄ : Representation ℂ (GL (Fin d) k) V₄)
    (ρ₅ : Representation ℂ (GL (Fin e) k) V₅)
    (φ : Nonempty ((ind₂ (stdSum h₁) (extTensor ρ₁ ρ₂)).Equiv (ind₂ (stdSum h₂) (extTensor ρ₃ ρ₄)))) :
    Nonempty ((ind₂ (stdSum h) (extTensor ρ₅ (ind₂ (stdSum h₁) (extTensor ρ₁ ρ₂)))).Equiv
      (ind₂ (stdSum h) (extTensor ρ₅ (ind₂ (stdSum h₂) (extTensor ρ₃ ρ₄))))) :=
  ind₂_congr h (eqv_refl ρ₅) φ

theorem multiProd_head_comp {s u : ℕ} {d : Fin s → ℕ} (σ : ∀ a, Irr k (d a)) (ι : Fin (u + 1) → Fin s)
    (a₀ : Fin s) (κ : Fin u → Fin s) (h0 : ι 0 = a₀) (hκ : ∀ i, ι i.succ = κ i) {T N : ℕ}
    (e : (Σ i, Fin (d (ι i))) ≃ Fin N) (h : d a₀ + T = N) (e' : (Σ i, Fin (d (κ i))) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (σ (ι i)).π).Equiv
      (ind₂ (stdSum h) (extTensor (σ a₀).π (multiProd e' fun i => (σ (κ i)).π)))) := by
  subst h0
  have hk : (fun i => ι i.succ) = κ := funext hκ
  subst hk
  exact multiProd_head (fun i => (σ (ι i)).π) e h e'

end GlobalTheory.ProdReorder
