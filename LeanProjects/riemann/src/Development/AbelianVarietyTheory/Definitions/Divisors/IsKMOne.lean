import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

noncomputable section

namespace GlobalTheory.UCls

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def IsUA (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  IsUnit g.det ∧ ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y

def IsKM (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    (k : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  IsUA c G k ∧ (∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ x - x = M • y) ∧ ∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ y = x

def ratM (F : Type) [Field F] [NumberField F] [Algebra F E] (γ : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) (RA F E) :=
  γ.map fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ x

def UEquiv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    (g g' : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ γ : Matrix (Fin n) (Fin n) E, IsUA c G (ratM F γ) ∧ ∃ k, IsKM c G L M k ∧ g' = ratM F γ * g * k

def classNo (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) : ℕ∞ :=
  ENat.card (Quot fun a b : {g // IsUA c G g} => UEquiv c G L M a.1 b.1)

def IsTA (c : E ≃ₐ[F] E) (t : RA F E) : Prop := t * sg (FiniteAdeleRing (𝓞 F) F) c t = 1

def TEquiv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) (t t' : RA F E) : Prop :=
  ∃ u : E, u * c u = 1 ∧ ∃ k, IsKM c G L M k ∧ t' = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ u) * t * k.det

def torusNo (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) : ℕ∞ :=
  ENat.card (Quot fun a b : {t // IsTA c t} => TEquiv c G L M a.1 b.1)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in

theorem _root_.GlobalTheory.UCls.isKM_one (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (L : Set (Fin n → E)) (M : ℕ) :
    _root_.GlobalTheory.UCls.IsKM c G L M 1 := by
  refine ⟨⟨by simp, fun x y => by simp only [one_mulVec]⟩, fun x _ => ⟨0, ?_, ?_⟩,
    fun x hx => ⟨x, hx, one_mulVec x⟩⟩
  · exact (_root_.GlobalTheory.AdLat.hat F L).zero_mem
  · simp

end GlobalTheory.UCls
