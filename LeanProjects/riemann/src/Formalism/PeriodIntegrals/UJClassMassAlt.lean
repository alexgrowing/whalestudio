import Formalism.PeriodIntegrals.UJClassFin
import Formalism.HermitianLattices.StatementMass

noncomputable section

open Matrix NumberField
open scoped TensorProduct
open PI.UJClassFin

namespace PI.UJClassMass2

def gramOf {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) : Matrix (Fin M) (Fin M) E :=
  fun i j => h (b i) (b j)

def crdOf {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) : Set (Fin M → E) :=
  {x | ∑ i, x i • b i ∈ L0}

def stab {G : Type*} [Group G] (Γ K : Subgroup G) (g : G) : Set Γ := {γ | g⁻¹ * ((γ : G) * g) ∈ K}

def UJClassMass : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (n : ℕ) (g : Fin n → HA (AF F) σ (gramOf h b)),
      (∀ x, ∃ i, ∃ γ : GamG σ (gramOf h b), ∃ k : SFin σ (gramOf h b) (crdOf b L0),
        x = (γ : HA (AF F) σ (gramOf h b)) * g i * k) →
      (∀ i j (γ γ' : GamG σ (gramOf h b)) (k k' : SFin σ (gramOf h b) (crdOf b L0)),
        (γ : HA (AF F) σ (gramOf h b)) * g i * k = (γ' : HA (AF F) σ (gramOf h b)) * g j * k' → i = j) →
      ∑ i, ((Nat.card (stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) (g i)) : ℝ))⁻¹ =
        Formalism.HermitianLatticesTheory.mass h L0

end PI.UJClassMass2
