import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol

noncomputable section

open NumberField Matrix Polynomial GlobalTheory.DefU GlobalTheory.UnitaryBC Formalism.BasicNotions
open UpperTheory.Gal.Schur (sch)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

def lamOf {E : Type} [Field E] {n : ℕ} (W : InfinitePlace E → DomWeight n) (m : InfinitePlace E → ℕ) (τ : E →+* ℂ) (i : Fin n) : ℕ :=
  if τ = (InfinitePlace.mk τ).embedding then m (InfinitePlace.mk τ) else ((W (InfinitePlace.mk τ)).w i + m (InfinitePlace.mk τ)).toNat

def TrRho : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (g : InfinitePlace E → GL (Fin n) ℂ),
  LinearMap.trace ℂ _ (Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W g) = ∏ v, LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n (W v) (g v))

def TrSch : Prop := ∀ (n : ℕ) (lam : DomWeight n) (m : ℕ), (∀ i, 0 ≤ lam.w i + m) → ∀ (g : GL (Fin n) ℂ) (t : Fin n → ℂ),
  Function.Injective t → g.val.charpoly = ∏ i, (X - C (t i)) →
  LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) * (∏ i, t i) ^ m = sch (fun i => (lam.w i + m).toNat) t

def SchHom : Prop := ∀ (n : ℕ) (t : Fin n → ℂ), Function.Injective t →
  (∀ (lam : Fin n → ℕ) (c : ℂ), c ≠ 0 → sch lam (fun i => c * t i) = c ^ (∑ i, lam i) * sch lam t) ∧
    ∀ m : ℕ, sch (fun _ => m) t = (∏ i, t i) ^ m

def CharConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y P : GL (Fin n) E) (s : ℚˣ),
  (y.val.map (IsCMField.complexConj E))ᵀ * P.val * y.val = ((s : ℚ) : E) • P.val → ∀ (φ : E →+* ℂ) (t : Fin n → ℂ),
  y.val.charpoly.map φ = ∏ i, (X - C (t i)) →
  (∀ i, t i ≠ 0) ∧ y.val.charpoly.map (ComplexEmbedding.conjugate φ) = ∏ i, (X - C (((s : ℚ) : ℂ) / t i))

def WtCore : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (m : InfinitePlace E → ℕ),
  (∀ v i, 0 ≤ (W v).w i + m v) → ∀ (y P y' : GL (Fin n) E) (s : ℚˣ),
  (y.val.map (IsCMField.complexConj E))ᵀ * P.val * y.val = ((s : ℚ) : E) • P.val → y.val.charpoly.Separable → y'.val = (y⁻¹).valᵀ →
  LinearMap.trace ℂ _ (xi W (∑ v, ((∑ i, (W v).w i) + n * m v)) (y', s⁻¹)) = LocalSmoothExtension.schW (lamOf W m) (LocalSmoothExtension.invPol y.val.charpoly)

def AutEx : Prop := ∀ (E : Type) [Field E] [NumberField E] (τ τ₀ : E →+* ℂ), ∃ σ : ℂ ≃+* ℂ, ∀ y, σ (τ y) = τ₀ y

def WtAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 0 < n → ∀ π : AutSub E n, (∃ W : Wt E n, π.finPart W ≠ ⊥) ∧
  ∀ W : Wt E n, π.finPart W ≠ ⊥ → ∀ τ lam, HasWeightAt π.V τ lam → lam = W.at τ

def EpsIff : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (x ω : E), 0 < d → x ^ 2 = -(d : E) →
  ω ∈ IntermediateField.adjoin ℚ {x} → x ∈ IntermediateField.adjoin ℚ {ω} → ∀ τ φ : E →+* ℂ,
  (φ ω = (starRingEnd ℂ) (τ ω) ↔ φ x = -τ x)

def ExpSum : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) →
  ∀ (W : Wt E n) (m : InfinitePlace E → ℕ), (∀ v i, 0 ≤ (W v).w i + m v) → ∀ τ : E →+* ℂ,
  ((∑ φ ∈ (Finset.univ.erase τ).erase (ComplexEmbedding.conjugate τ), (if φ x = -τ x then 1 else 0) * ∑ j, lamOf W m φ j : ℕ) : ℤ) +
      (n * m (InfinitePlace.mk τ) + if τ = (InfinitePlace.mk τ).embedding then ∑ i, (W (InfinitePlace.mk τ)).w i else 0) =
    mOf x W (∑ v, ((∑ i, (W v).w i) + n * m v)) τ

def ExpCore : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) →
  ∀ (W : Wt E n) (m : InfinitePlace E → ℕ), (∀ v i, 0 ≤ (W v).w i + m v) → (∀ τ, Antitone (lamOf W m τ)) ∧
  ∀ (τ τ₀ : E →+* ℂ) (σ : ℂ ≃+* ℂ), (∀ y, σ (τ y) = τ₀ y) → ∀ ε : (E →+* ℂ) → ℕ,
    (∀ φ : E →+* ℂ, ε ((σ : ℂ →+* ℂ).comp φ) = if φ x = -τ x then 1 else 0) → ∀ k : Fin n, ∃ (h : Fin n → ℕ) (i : Fin n),
      LocalSmoothExtension.IsHExp τ₀ ε (LocalSmoothExtension.conjWt σ (lamOf W m)) h ∧
        (h i : ℤ) = (((k : ℕ) : ℤ) - (W.at τ).w k) + mOf x W (∑ v, ((∑ i, (W v).w i) + n * m v)) τ

end UpperTheory.Gal.CertificateRingHomMap

end
