import Mathlib
import GroundTheory.AutomorphicForms.WhittakerOrbit
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.Gal.LocD

section General

variable {G : Type} [Group G] [TopologicalSpace G]

abbrev Cc (X : Type) [TopologicalSpace X] : Submodule ℂ (X → ℂ) := GroundTheory.Automorphic.locallyConstantCompactSupport X ℂ ℂ

def indF (B : Subgroup G) (χ : B →* ℂˣ) : Submodule ℂ (G → ℂ) where
  carrier := {f | (∀ (b : B) (g : G), f (b * g) = (χ b : ℂ) * f g) ∧
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, ∀ g : G, f (g * k) = f g}
  add_mem' := by
    rintro f₁ f₂ ⟨h₁, K₁, hK₁, hf₁⟩ ⟨h₂, K₂, hK₂, hf₂⟩
    refine ⟨fun b g => by simp [h₁ b g, h₂ b g, mul_add], K₁ ⊓ K₂, hK₁.inter hK₂, fun k hk g => ?_⟩
    simp [hf₁ k hk.1 g, hf₂ k hk.2 g]
  zero_mem' := ⟨fun b g => by simp, ⊤, by simp, fun k _ g => rfl⟩
  smul_mem' := by
    rintro c f ⟨h, K, hK, hf⟩
    exact ⟨fun b g => by simp [h b g, mul_left_comm], K, hK, fun k hk g => by simp [hf k hk g]⟩

theorem mem_indF {B : Subgroup G} {χ : B →* ℂˣ} {f : G → ℂ} :
    f ∈ indF B χ ↔ (∀ (b : B) (g : G), f (b * g) = (χ b : ℂ) * f g) ∧
      ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, ∀ g : G, f (g * k) = f g := Iff.rfl

example : (fun _ => 1 : G → ℂ) ∈ indF ⊤ 1 := ⟨fun _ _ => by simp, ⊤, by simp, fun _ _ _ => rfl⟩

def pr {G : Type} [Group G] (B : Subgroup G) [MeasurableSpace B] (μ : Measure B) (χ : B →* ℂˣ) (f : G → ℂ) : G → ℂ :=
  fun g => ∫ b : B, (χ b : ℂ) * f ((b : G)⁻¹ * g) ∂μ

def cell {G : Type} [Group G] (B N : Subgroup G) (w : G) : Set G := {g | ∃ b ∈ B, ∃ u ∈ N, g = b * w * u}

end General

section GeneralLinearIntegers

variable {E : Type} [Field E] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sg_val (σ : E ≃+* E) (g : GL (Fin n) E) (i j : Fin n) :
    (sg σ g : Matrix (Fin n) (Fin n) E) i j = σ ((g : Matrix (Fin n) (Fin n) E) i j) := rfl

theorem sg_mem_unipB (σ : E ≃+* E) {g : GL (Fin n) E} (hg : g ∈ unipB E (Fin n)) : sg σ g ∈ unipB E (Fin n) := by
  rw [mem_unipB] at hg ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [sg_val, hg.1 i j hij, map_zero]
  · rw [sg_val, hg.2 i, map_one]

def Semi (σ : E ≃+* E) (π : Representation ℂ (GL (Fin n) E) V) (A : V →ₗ[ℂ] V) : Prop :=
  ∀ g v, A (π g v) = π (sg σ g) (A v)

example (π : Representation ℂ (GL (Fin n) E) V) : Semi (RingEquiv.refl E) π LinearMap.id := fun _ _ => rfl

def jacA {σ : E ≃+* E} {π : Representation ℂ (GL (Fin n) E) V} {A : V →ₗ[ℂ] V} (hA : Semi σ π A) :
    Jacquet π (unipB E (Fin n)) →ₗ[ℂ] Jacquet π (unipB E (Fin n)) :=
  (twKer π (unipB E (Fin n)) 1).mapQ (twKer π (unipB E (Fin n)) 1) A (by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨⟨_, sg_mem_unipB σ u.2⟩, A v, ?_⟩
    simp [hA u v])

theorem jacA_mk {σ : E ≃+* E} {π : Representation ℂ (GL (Fin n) E) V} {A : V →ₗ[ℂ] V} (hA : Semi σ π A) (v : V) :
    jacA hA (Submodule.Quotient.mk v) = Submodule.Quotient.mk (A v) := rfl

def Inv (σ : E ≃+* E) (ω : Eˣ →* ℂˣ) : Prop := ∀ x : Eˣ, ω (Units.map (σ : E →* E) x) = ω x

example (σ : E ≃+* E) : Inv σ 1 := fun _ => rfl

end GeneralLinearIntegers

def Scalar : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ)
    (σ : E ≃+* E) (q : ℕ), Cyc σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V),
    π.IsIrreducible → ∀ ω : Fin n → Eˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) → (∀ i, Inv σ (ω i)) →
    IsSubquotient π (prinSeries ω) → ∀ A : V →ₗ[ℂ] V, Semi σ π A →
      ∃ c : ℂ, (A ≠ 0 → c ≠ 0) ∧ ∀ ψ : AddChar E Circle, Continuous ψ → (∀ x, ψ (σ x) = ψ x) →
        ∀ v, A v - c • v ∈ twKer π (unipB E (Fin n)) (whitChar ψ n)

def LocDesc : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ)
    (σ : E ≃+* E) (q : ℕ), Cyc σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V),
    π.IsIrreducible → ∀ ω : Fin n → Eˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) → (∀ i, Inv σ (ω i)) →
    IsSubquotient π (prinSeries ω) → ∀ (A : V →ₗ[ℂ] V) (hA : Semi σ π A), A ≠ 0 →
      Nontrivial (Jacquet π (unipB E (Fin n))) ∧ FiniteDimensional ℂ (Jacquet π (unipB E (Fin n))) ∧
      (∀ μ : (Fin n → Eˣ) →* ℂˣ,
        (⨅ t, Module.End.maxGenEigenspace (jacB π t) (μ t : ℂ) : Submodule ℂ (Jacquet π (unipB E (Fin n)))) ≠ ⊥ →
          ∃ w : Equiv.Perm (Fin n), μ = torusChar (ω ∘ w)) ∧
      ∃ c : ℂ, c ≠ 0 ∧ jacA hA = c • LinearMap.id ∧
        (∀ ψ : AddChar E Circle, Continuous ψ → (∀ x, ψ (σ x) = ψ x) → ∀ (l : V →ₗ[ℂ] ℂ) (a : ℂ), l ≠ 0 →
          (∀ (u : unipB E (Fin n)) (v : V), l (π u v) = (whitChar ψ n u : ℂ) * l v) → (∀ v, l (A v) = a * l v) → c = a) ∧
        ∀ U : Submodule ℂ (Jacquet π (unipB E (Fin n))), U ≠ ⊥ → (∀ t, ∀ y ∈ U, jacB π t y ∈ U) →
          ∀ (t : Fin n → Eˣ) (k₀ : ℕ), ∃ k ≥ k₀, ∃ h : ∀ y ∈ U, (jacB π (t ^ k) ∘ₗ jacA hA) y ∈ U,
            LinearMap.trace ℂ U ((jacB π (t ^ k) ∘ₗ jacA hA).restrict h) ≠ 0

def OfSupport : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V)
    (ω : Fin n → Eˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i)),
    HasSupport π (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) ↔
      π.IsIrreducible ∧ IsSubquotient π (prinSeries ω)

def InvOfNorm : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (σ : E ≃ₐ[F] E), Isom (σ : E ≃+* E) → ∀ (ω : Eˣ →* ℂˣ) (χ : Fˣ →* ℂˣ),
    (∀ u : Eˣ, valuation E (u : E) = 1 → ω u = χ (Units.map (Algebra.norm F : E →* F) u)) → Inv (σ : E ≃+* E) ω

def InvOfProd : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (σ : E ≃+* E) (q : ℕ), Cyc σ q → ∀ ω : Eˣ →* ℂˣ,
    (∀ u : Eˣ, valuation E (u : E) = 1 → ∏ i ∈ Finset.range q, σ^[i] (u : E) = 1 → ω u = 1) → Inv σ ω

end UpperTheory.Gal.LocD

end
