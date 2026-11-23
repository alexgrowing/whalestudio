import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.SA

open Matrix NumberField IsDedekindDomain TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hf {R : Type*} [CommRing R] (σ : R →+* R) (J : Matrix ι ι R) (x y : ι → R) : R :=
  ∑ i, ∑ j, x i * J i j * σ (y j)

def SU {R : Type*} [CommRing R] (σ : R →+* R) (J : Matrix ι ι R) : Set (Matrix ι ι R) :=
  {g | g.det = 1 ∧ gᵀ * J * g.map σ = J}

def eich {R : Type*} [CommRing R] (σ : R →+* R) (J : Matrix ι ι R) (e u : ι → R) (c : R) :
    Matrix ι ι R :=
  1 + vecMulVec u (J *ᵥ (σ ∘ e)) - vecMulVec e (J *ᵥ (σ ∘ u)) + c • vecMulVec e (J *ᵥ (σ ∘ e))

def eichAlong {R : Type*} [CommRing R] (σ : R →+* R) (J : Matrix ι ι R) (e f : ι → R) :
    Set (Matrix ι ι R) :=
  {M | ∃ (u : ι → R) (c : R), hf σ J u e = 0 ∧ hf σ J u f = 0 ∧ c + σ c + hf σ J u u = 0 ∧
    M = eich σ J e u c}

def eichSet {R : Type*} [CommRing R] (σ : R →+* R) (J : Matrix ι ι R) (e f : ι → R) :
    Set (Matrix ι ι R) :=
  eichAlong σ J e f ∪ eichAlong σ J f e

def LocGenStatement : Prop :=
  ∀ (k K : Type) [Field k] [CommRing K] [Algebra k K] (σ : K →ₐ[k] K),
    (∀ x, σ (σ x) = x) → (∀ x, σ x = x ↔ x ∈ Set.range (algebraMap k K)) →
    Module.finrank k K = 2 → IsReduced K → (2 : k) ≠ 0 →
    ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) K), Jᵀ = J.map σ → IsUnit J.det →
    ∀ e f : Fin N → K, hf σ.toRingHom J e e = 0 → hf σ.toRingHom J f f = 0 →
      hf σ.toRingHom J e f = 1 →
      SU σ.toRingHom J = (Submonoid.closure (eichSet σ.toRingHom J e f) : Set (Matrix (Fin N) (Fin N) K))

abbrev AE (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : Type :=
  FiniteAdeleRing (𝓞 F) F ⊗[F] E

def sigA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) :
    AE F E →+* AE F E :=
  (Algebra.TensorProduct.map (AlgHom.id F (FiniteAdeleRing (𝓞 F) F)) c.toAlgHom).toRingHom

def inclA (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : E →+* AE F E :=
  (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).toRingHom

def SAStatement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), Jᵀ = J.map c → IsUnit J.det →
    (∃ e : Fin N → E, e ≠ 0 ∧ hf c.toRingHom J e e = 0) →
    ∀ [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)],
      SU (sigA c) (J.map (inclA F E)) ⊆
        closure ((fun γ : Matrix (Fin N) (Fin N) E => γ.map (inclA F E)) '' SU c.toRingHom J)

def SAOpenStatement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), Jᵀ = J.map c → IsUnit J.det →
    (∃ e : Fin N → E, e ≠ 0 ∧ hf c.toRingHom J e e = 0) →
    ∀ [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)]
      (Kg : Set (Matrix (Fin N) (Fin N) (AE F E))), Kg ⊆ SU (sigA c) (J.map (inclA F E)) →
      1 ∈ Kg → (∀ a ∈ Kg, ∀ b ∈ Kg, a * b ∈ Kg) → (∀ a ∈ Kg, a⁻¹ ∈ Kg) →
      (∃ O, IsOpen O ∧ O ∩ SU (sigA c) (J.map (inclA F E)) = Kg) →
      ∀ x ∈ SU (sigA c) (J.map (inclA F E)),
        ∃ γ ∈ SU c.toRingHom J, ∃ k ∈ Kg, x = γ.map (inclA F E) * k

end ReciprocityTheory.ChartRestriction.G.SA
