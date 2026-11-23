import Formalism.PeriodIntegrals.LocFramePrim

noncomputable section

namespace PI.LocFramePrimWork

open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct

def DiffLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (y : Fv F v ⊗[F] E),
    y ∈ Submodule.span (v.adicCompletionIntegers F)
        (inclR (F := F) (Fv F v) '' ((ddE F ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) ↔
      ∃ p ∈ OEv (E := E) v, y = sc (E := E) v ((dV v)⁻¹ ^ k) * p

def Dual : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n r : ℕ) (Λ Lb : Submodule (𝓞 E) (Fin n → E)) (e f : Fin r → Fin n → E) (z : Fin n → E),
    Λ.FG →
    Λ = latSpan (fun a : Fin r => ddE F ^ (-((r : ℤ) - (a : ℕ)))) e ⊔ Lb ⊔
      latSpan (fun a : Fin r => (ddE F ^ (-((r : ℤ) - (a : ℕ))))⁻¹) f →
    LinearIndependent E (Fin.append e f) →
    (∀ y ∈ Lb, y ∈ Submodule.span E (Set.range e ∪ Set.range f) → y = 0) →
    z ∈ Lb →
    (∀ c : E, c • z ∈ Lb → ∃ o : 𝓞 E, (o : E) = c) →
    ∃ (φ : Fin r → (Fin n → E) →ₗ[E] E) (φz : (Fin n → E) →ₗ[E] E),
      (∀ a b, φ a (e b) = if a = b then 1 else 0) ∧ (∀ a b, φ a (f b) = 0) ∧
      (∀ a, ∀ l ∈ Lb, φ a l = 0) ∧ (∀ a, φz (e a) = 0) ∧ (∀ a, φz (f a) = 0) ∧
      φz z = 1 ∧ ∀ l ∈ Lb, ∃ o : 𝓞 E, φz l = o

def Assemble : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (n r : ℕ) (Λ Lb : Submodule (𝓞 E) (Fin n → E))
    (e f : Fin r → Fin n → E) (z : Fin n → E),
    (∀ (k : ℕ) (y : Fv F v ⊗[F] E),
      y ∈ Submodule.span (v.adicCompletionIntegers F)
        (inclR (F := F) (Fv F v) '' ((ddE F ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) ↔
      ∃ p ∈ OEv (E := E) v, y = sc (E := E) v ((dV v)⁻¹ ^ k) * p) →
    Λ = latSpan (fun a : Fin r => ddE F ^ (-((r : ℤ) - (a : ℕ)))) e ⊔ Lb ⊔
      latSpan (fun a : Fin r => (ddE F ^ (-((r : ℤ) - (a : ℕ))))⁻¹) f →
    z ∈ Lb →
    ∀ (φ : Fin r → (Fin n → E) →ₗ[E] E) (φz : (Fin n → E) →ₗ[E] E),
      (∀ a b, φ a (e b) = if a = b then 1 else 0) → (∀ a b, φ a (f b) = 0) →
      (∀ a, ∀ l ∈ Lb, φ a l = 0) → (∀ a, φz (e a) = 0) → (∀ a, φz (f a) = 0) →
      φz z = 1 → (∀ l ∈ Lb, ∃ o : 𝓞 E, φz l = o) →
    IsPrim v (Λ : Set (Fin n → E))
      (locF v (ratTup (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E)))

theorem Steps_top (h1 : DiffLoc) (h2 : Dual) (h3 : Assemble) : PI.LocFramePrim.Statement := by
  intro F E _ _ _ _ _ v n r Λ Lb e f z hfg hΛ hli hdis hz hprim
  obtain ⟨φ, φz, p1, p2, p3, p4, p5, p6, p7⟩ := h2 F E n r Λ Lb e f z hfg hΛ hli hdis hz hprim
  exact h3 F E v n r Λ Lb e f z (h1 F E v) hΛ hz φ φz p1 p2 p3 p4 p5 p6 p7

end PI.LocFramePrimWork
