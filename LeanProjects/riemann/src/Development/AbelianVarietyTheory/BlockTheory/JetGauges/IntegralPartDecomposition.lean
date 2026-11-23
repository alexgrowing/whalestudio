import Mathlib

open scoped TensorProduct NumberField nonZeroDivisors Classical
open Module UniqueFactorizationMonoid IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralPartDecomposition

variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [CharZero C]
variable {ι : Type} [Fintype ι]

def ratBasis (b : Basis ι ℤ (𝓞 E)) : Basis ι ℚ E :=
  b.localizationLocalization ℚ ℤ⁰ E

def dualBasis (b : Basis ι ℤ (𝓞 E)) : Basis ι ℚ E :=
  (ratBasis b).traceDual

def evalAt (σ : E →+* C) : E ⊗[ℚ] C →ₐ[ℚ] C :=
  Algebra.TensorProduct.productMap σ.toRatAlgHom (AlgHom.id ℚ C)

def idem (b : Basis ι ℤ (𝓞 E)) (τ : E →+* C) : E ⊗[ℚ] C :=
  ∑ i, ((b i : 𝓞 E) : E) ⊗ₜ[ℚ] τ (dualBasis b i)

def integralMap (E : Type) [Field E] [NumberField E] (R : Subring C) :
    (𝓞 E) ⊗[ℤ] R →ₐ[ℤ] E ⊗[ℚ] C :=
  Algebra.TensorProduct.productMap
    ((Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := E) (B := C)).comp
      (algebraMap (𝓞 E) E)).toIntAlgHom
    ((Algebra.TensorProduct.includeRight (R := ℚ) (A := E) (B := C)).toRingHom.comp
      R.subtype).toIntAlgHom

def integralPart (E : Type) [Field E] [NumberField E] (R : Subring C) : Subring (E ⊗[ℚ] C) :=
  (integralMap E R).toRingHom.range

def Induces (O : ValuationSubring C) (τ : E →+* C) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ O.valuation (τ (a : E)) < 1

def placeEmbeddings (O : ValuationSubring C) (w : HeightOneSpectrum (𝓞 E)) :
    Finset (E →+* C) :=
  Finset.univ.filter fun τ => Induces O τ w

def placeIdem (b : Basis ι ℤ (𝓞 E)) (O : ValuationSubring C) (w : HeightOneSpectrum (𝓞 E)) :
    E ⊗[ℚ] C :=
  ∑ τ ∈ placeEmbeddings O w, idem b τ

def differentExp_vw (w : HeightOneSpectrum (𝓞 E)) : ℕ :=
  (normalizedFactors (differentIdeal ℤ (𝓞 E))).count w.asIdeal

def ramExp (p : ℕ) (w : HeightOneSpectrum (𝓞 E)) : ℕ :=
  (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count w.asIdeal

def ValGeDifferent_vp (O : ValuationSubring C) (p : ℕ) (w : HeightOneSpectrum (𝓞 E)) (c : C) :
    Prop :=
  O.valuation c ^ ramExp p w ≤ O.valuation (p : C) ^ differentExp_vw w

def EvalClaim (b : Basis ι ℤ (𝓞 E)) (τ : E →+* C) : Prop :=
  evalAt τ (idem b τ) = 1 ∧ ∀ σ : E →+* C, σ ≠ τ → evalAt σ (idem b τ) = 0

def IdemClaim (b : Basis ι ℤ (𝓞 E)) (τ : E →+* C) : Prop :=
  IsIdempotentElem (idem b τ) ∧
    (∀ σ : E →+* C, σ ≠ τ → idem b σ * idem b τ = 0) ∧
    (∀ a : E, (a ⊗ₜ[ℚ] (1 : C)) * idem b τ = ((1 : E) ⊗ₜ[ℚ] τ a) * idem b τ) ∧
    ∑ σ : E →+* C, idem b σ = 1

def DifferentClaim (b : Basis ι ℤ (𝓞 E)) (τ : E →+* C) : Prop :=
  ∀ R : Subring C, (∀ a : 𝓞 E, τ (a : E) ∈ R) →
    ∀ δ ∈ differentIdeal ℤ (𝓞 E),
      ((1 : E) ⊗ₜ[ℚ] τ (δ : E)) * idem b τ ∈ integralPart E R

def DifferentClaim_vp (b : Basis ι ℤ (𝓞 E)) (τ : E →+* C) : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ O : ValuationSubring C, O.valuation (p : C) < 1 →
    ∀ w : HeightOneSpectrum (𝓞 E), Induces O τ w →
      ∀ c : C, ValGeDifferent_vp O p w c →
        ((1 : E) ⊗ₜ[ℚ] c) * idem b τ ∈ integralPart E O.toSubring

def PlaceClaim (C : Type) [Field C] [CharZero C] (b : Basis ι ℤ (𝓞 E)) : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ O : ValuationSubring C, O.valuation (p : C) < 1 →
    ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal →
      (placeEmbeddings O w).Nonempty ∧
      placeIdem b O w ∈ integralPart E O.toSubring ∧
      (∀ σ : E →+* C, Induces O σ w → evalAt σ (placeIdem b O w) = 1) ∧
      (∀ σ : E →+* C, ¬ Induces O σ w → evalAt σ (placeIdem b O w) = 0)

def IdempotentBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] [IsAlgClosed C]
    (ι : Type) [Fintype ι] (b : Basis ι ℤ (𝓞 E)),
    (∀ τ : E →+* C, EvalClaim b τ ∧ IdemClaim b τ ∧ DifferentClaim b τ ∧ DifferentClaim_vp b τ) ∧
      PlaceClaim C b

theorem evalAt_tmul (σ : E →+* C) (a : E) (x : C) : evalAt σ (a ⊗ₜ[ℚ] x) = σ a * x := by
  simp [evalAt]

omit [Fintype ι] in
theorem ratBasis_apply (b : Basis ι ℤ (𝓞 E)) (i : ι) : ratBasis b i = ((b i : 𝓞 E) : E) := by
  simp [ratBasis]

theorem integralMap_tmul (R : Subring C) (a : 𝓞 E) (x : R) :
    integralMap E R (a ⊗ₜ[ℤ] x) = (a : E) ⊗ₜ[ℚ] (x : C) := by
  refine (Algebra.TensorProduct.productMap_apply_tmul _ _ a x).trans ?_
  change ((a : E) ⊗ₜ[ℚ] (1 : C)) * ((1 : E) ⊗ₜ[ℚ] (x : C)) = _
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralPartDecomposition
