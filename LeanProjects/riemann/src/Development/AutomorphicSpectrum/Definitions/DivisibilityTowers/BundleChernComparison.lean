import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.IterateExamples.Statements

namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

structure LocPair {K : Type} (ι : K → Type) (R : Type) [CommRing R] (σ : Type) where

  x : σ → K → ℤ

  x' : σ → K → ℤ

  f : σ → MRing ι R

  g : σ → MRing ι R

variable {K : Type} {ι : K → Type} {σ σ' : Type}

def LocPair.map {R R' : Type} [CommRing R] [CommRing R'] (T : LocPair ι R σ) (ψ : R →+* R') :
    LocPair ι R' σ :=
  ⟨T.x, T.x', fun i => MvPolynomial.map ψ (T.f i), fun i => MvPolynomial.map ψ (T.g i)⟩

def LocPair.comp {R : Type} [CommRing R] (T : LocPair ι R σ) (e : σ' → σ) : LocPair ι R σ' :=
  ⟨T.x ∘ e, T.x' ∘ e, T.f ∘ e, T.g ∘ e⟩

def IsMixExpansion [Fintype σ] (m : ℕ) (V : MvPolynomial (σ ⊕ σ) ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ) : Prop :=
  V = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Gs i ∧ ∀ i, (Gs i).IsHomogeneous m

def mixDiff (F : MvPolynomial σ ℝ) : MvPolynomial (σ ⊕ σ) ℝ := rename Sum.inl F - rename Sum.inr F

variable [DecidableEq K]

def genNum (F : Type) [Field F] (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ)
    (Q : List (K → ℤ)) : ℝ :=
  ∑ μ ∈ H.support, H.coeff μ * (intNumL F V (classList cls μ ++ Q) : ℝ)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def cycList (Z : Ideal (MRing ι O) → ℤ) (l : List (K → ℤ)) : ℤ := cycEval (fun W => vNumL W l) Z

def cycNum (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)) : ℝ :=
  ∑ μ ∈ H.support, H.coeff μ * (cycList Z (classList cls μ ++ Q) : ℝ)

def LocPair.IsVert (T : LocPair ι O σ) (P : Ideal (MRing ι O)) (ϖ : O) : Prop :=
  ∀ i, IsVerticalDivisor P ϖ (T.x i - T.x' i) (T.f i) (T.g i)

def LocPair.val [Fintype σ] (T : LocPair ι O σ) (P : Ideal (MRing ι O))
    (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ) : ℝ :=
  ∑ i, cycNum (ratDiv P (T.f i) (T.g i)) (Sum.elim T.x T.x') (Gs i) []

def LocPair.ck {r : ℕ} (T : LocPair ι O (Fin r)) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)) : ℤ :=
  pairNum P T.x T.x' T.f T.g (psumExpansion r k) Q

def laNum {r : ℕ} (P : Ideal (MRing ι O)) (a : O) (x : Fin r → K → ℤ) (k : ℕ) (Q : List (K → ℤ)) : ℤ :=
  (k : ℤ) * cycEval (fun W => classNum x (psum (Fin r) ℤ (k - 1)) Q W) (divCycle P (C a))

section Labels

variable {Sg : Type} (P : Ideal (MRing ι O)) (d p : ℕ) (φ : Equiv.Perm Sg) {r s : Sg → ℕ}
  (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ)))

def Relations : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = d + 1 → ∃ h : Sg → ℝ,
    (∀ τ, (((lie τ).ck P k Q : ℤ) : ℝ) + (((om τ).ck P k Q : ℤ) : ℝ) =
      h τ - ((laNum P (p : O) (lie τ).x k Q : ℤ) : ℝ) / ((p : ℝ) - 1)) ∧
    ∀ τ, (p : ℝ) ^ k * h τ = h (φ τ) + ((laNum P (p : O) (lie (φ τ)).x k Q : ℤ) : ℝ)

def LabelChernComparison [Fintype Sg] [DecidableEq Sg] : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = d + 1 → ∀ τ,
    (((lie τ).ck P k Q : ℤ) : ℝ) + (((om τ).ck P k Q : ℤ) : ℝ) =
      ∑ τ', GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k τ τ' * ((laNum P (p : O) (lie τ').x k Q : ℤ) : ℝ)

end Labels

def BundleChernComparison (P : Ideal (MRing ι O)) (d p : ℕ) {r s : ℕ} (lie : LocPair ι O (Fin r))
    (om : LocPair ι O (Fin s)) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = d + 1 →
    ((lie.ck P k Q : ℤ) : ℝ) + ((om.ck P k Q : ℤ) : ℝ) =
      (1 / ((p : ℝ) ^ k - 1) - 1 / ((p : ℝ) - 1)) * ((laNum P (p : O) lie.x k Q : ℤ) : ℝ)

def IsFibreComp (P : Ideal (MRing ι O)) (W : Ideal (MRing ι O)) : Prop :=
  W ∈ (P ⊔ (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O)).minimalPrimes ∧ IsRelevant W

def PowerSumsVanish (P : Ideal (MRing ι O)) (d : ℕ) {N : ℕ} (x : Fin N → K → ℤ) : Prop :=
  ∀ W, IsFibreComp P W → ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = d →
    classNum x (psum (Fin N) ℤ k) Q W = 0

def TrivFlagAt [Fintype K] (W : Ideal (MRing ι O)) {N : ℕ} (x : Fin N → K → ℤ) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (IsLocalRing.ResidueField O) Ω) (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω (Fin N → Ω)),
    pointIdeal (IsLocalRing.ResidueField O) y = specialIdeal W ∧
      IsFlagFrame y (scaledTrivBundle (IsLocalRing.ResidueField O) (segreVec y) N (one_ne_zero (α := Ω))) w x

section Roots

variable {Ψ : Type} {N : ℕ}

def rootPs (τ : Ψ) (k : ℕ) : MvPolynomial (Ψ × Fin N) ℝ := ∑ i : Fin N, X (τ, i) ^ k

def liePs (j m : ℕ) : Ψ ⊕ Ψ → MvPolynomial (Ψ × Fin N) ℝ
  | Sum.inl τ => ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), X (τ, i) ^ m
  | Sum.inr τ => ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), (-X (τ, i)) ^ m

variable [Fintype Ψ] [DecidableEq Ψ]

def bracket (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (p k : ℕ) (τ : Ψ) : MvPolynomial (Ψ × Fin N) ℝ :=
  C (k : ℝ) * ∑ τ', C (GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k (Sum.inl τ) τ') * liePs j (k - 1) τ'

def psComb (Qs : Ψ → ℕ → MvPolynomial (Ψ × Fin N) ℝ) : MvPolynomial (Ψ × Fin N) ℝ :=
  ∑ τ, ∑ k ∈ Finset.Icc 1 N, rootPs τ k * Qs τ k

def deltaPoly (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (p : ℕ) (Qs : Ψ → ℕ → MvPolynomial (Ψ × Fin N) ℝ) :
    MvPolynomial (Ψ × Fin N) ℝ :=
  ∑ τ, ∑ k ∈ Finset.Icc 1 N, bracket j φ p k τ * Qs τ k

def FlagChernComparison (P : Ideal (MRing ι O)) (d p j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair ι O (Ψ × Fin N)) :
    Prop :=
  ∀ τ, ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = d + 1 →
    (((T.comp fun i : Fin N => (τ, i)).ck P k Q : ℤ) : ℝ) =
      cycNum (divCycle P (C (p : O))) T.x (bracket j φ p k τ) Q

end Roots

end

end GlobalTheory.CompanionTheory.Ar.Num
