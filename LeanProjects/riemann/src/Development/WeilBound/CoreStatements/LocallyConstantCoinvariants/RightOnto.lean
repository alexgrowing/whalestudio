import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def aug (n d : ℕ) (ν α : kˣ →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ g : GL (Fin n) k, ∃ Φ ∈ SB (Matrix (Fin n) (Fin d) k), z = omB ν α g 1 Φ - Φ}

def Full (Φ : Matrix (Fin n) (Fin d) k → ℂ) : Prop := Φ ∈ SB (Matrix (Fin n) (Fin d) k) ∧ ∀ Y, Y.rank ≠ n → Φ Y = 0

def USm (χ : kˣ →* ℂˣ) : Prop := (∀ x, ‖(χ x : ℂ)‖ = 1) ∧ IsOpen (χ.ker : Set kˣ)

end Local

def SurjSt : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
  (ν α : kˣ →* ℂˣ), USm ν → ν ≠ 1 → ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Φ₀, Full Φ₀ ∧ Φ - Φ₀ ∈ aug n d ν α

def IrrSt : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
  (ν α : kˣ →* ℂˣ), n ≤ d → USm ν → USm α → ∀ N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ), aug n d ν α ≤ N →
  (∀ h : GL (Fin d) k, ∀ Φ ∈ N, Φ ∈ SB (Matrix (Fin n) (Fin d) k) → omB ν α 1 h Φ ∈ N) →
  (∀ Φ, Full Φ → Φ ∈ N) ∨ ∀ Φ ∈ N, Full Φ → Φ ∈ aug n d ν α

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Dict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def Reads (v : Pl F) (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ))
    (T : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ)
    (S : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) → Matrix (Fin n) (Fin d) (Fv F v) → ℂ) : Prop :=
  ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) T φ φ₁ ∧ ι φ₁ = S (ι φ)

structure IsDict (om : Rep σ X W) (v : Pl F) (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ))
    (ν α : (Fv F v)ˣ →* ℂˣ) : Prop where
  left : ∀ g ∈ UAt σ X (evFin F v), ∃ g₀, Reads v ι (om (g, 1)) (omB ν α g₀ 1)
  leftOnto : ∀ g₀, ∃ g ∈ UAt σ X (evFin F v), Reads v ι (om (g, 1)) (omB ν α g₀ 1)
  right : ∀ h ∈ UAt σ W (evFin F v), ∃ h₀, Reads v ι (om (1, h)) (omB ν α 1 h₀)
  rightOnto : ∀ h₀, ∃ h ∈ UAt σ W (evFin F v), Reads v ι (om (1, h)) (omB ν α 1 h₀)

end Dict

def DictSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E), B.IsGood σ → (∃ r s, X.IsHerm σ B r s) →
    (∃ r s, W.IsSkew σ B r s) → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om → IsHecke F E χX → IsHecke F E χW →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinBar B.ψ t 1 1 ι) ∧ ∃ ν α, USm ν ∧ USm α ∧ (1 ≤ n → 1 ≤ d → ν = 1 → chrW χW t = 1 ∨ chrW χW (t.comp σ) = 1) ∧
      ∀ ι, M.IsLinBar B.ψ t 1 1 ι → IsDict om v ι ν α

def ActsUniq : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ),
    ∀ φ ∈ SB (κ → Fv F v), ∀ φ₁ φ₂, Acts (evFin F v) T φ φ₁ → Acts (evFin F v) T φ φ₂ → φ₁ = φ₂

def NuSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ v, X.Good v → ∀ t : E →ₐ[F] Fv F v, chrW X.ν t ≠ 1

def SoSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' →
    ∀ γ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, om' γ Φ' ∈ G.M'.So B.ψ B.τ₁

end PositivityTheory.KCo
