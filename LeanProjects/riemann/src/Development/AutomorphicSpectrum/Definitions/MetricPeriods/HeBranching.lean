import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.PeriodIntegrals.DSInfCharCap
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.PairingAnalysis

open Formalism.REAL Formalism.MainNotions.S PI.DSInfCharCap

variable {n : ℕ}

abbrev um {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : Matrix (Fin m) (Fin m) ℂ := (g.1 : Matrix (Fin m) (Fin m) ℂ)

def emb (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (h : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex e e (Matrix.fromBlocks h 0 0 1)

def zi (e : Fin n ⊕ Unit ≃ Fin (n + 1)) : Fin (n + 1) := e (Sum.inr ())

def Fits (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) : Prop :=
  ε (zi e) = true ∧ ∀ a, ε (e (Sum.inl a)) = ε' a

def colSq {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) : ℝ := ∑ i, ‖g i j‖ ^ 2

def HeWord (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ) : Prop :=
  ∀ x y : Fin (n + 1) ⊕ Fin n, Sum.elim lam mu y < Sum.elim lam mu x →
    (∀ z, ¬ (Sum.elim lam mu y < Sum.elim lam mu z ∧ Sum.elim lam mu z < Sum.elim lam mu x)) →
    Xor' (x.isLeft = y.isLeft) (Sum.elim ε ε' x = Sum.elim ε ε' y)

structure Par (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ) (B : ℝ) : Prop where
  two : 2 ≤ n
  neg : ∃ a, ε a = false
  le : (univ.filter fun a => ε a = false).card ≤ (univ.filter fun a => ε a = true).card
  hc : Formalism.QuantumDeterminants.IsHCParam lam
  hc' : Formalism.QuantumDeterminants.IsHCParam mu
  bd : ∀ a, |lam a| ≤ B
  bd' : ∀ a, |mu a| ≤ B
  gap : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((n : ℝ) + 1) ^ 3)
  gap' : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((n : ℝ) + 1) ^ 3)

section

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

def Intertw (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (P : H →L[ℂ] H') : Prop :=
  ‖P‖ ≤ 1 ∧ ∀ h : UJ ε', ∀ x, P (π (emb e (um h)) x) = σ (um h) (P x)

end

def ForPairs (Q : ∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (_ : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (_ : Fin n → ℝ) (_ : ℝ)
    (_ : Fin n ⊕ Unit ≃ Fin (n + 1)) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'],
    (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) → (Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) →
    Measure (UJ ε') → Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ) (B : ℝ)
    (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (ν : Measure (UJ ε')), ν.IsHaarMeasure → Fits ε ε' e → Par ε lam ε' mu B → IsDS ε lam π → IsDS ε' mu σ →
    Q ε lam ε' mu B e π σ ν

def Moment : Prop := ForPairs fun {n} ε lam ε' _ B e H H' _ _ _ _ _ _ π σ ν =>
  ∀ (P : H →L[ℂ] H') (w : H') (κ : ℝ), Intertw ε' e π σ P → ‖w‖ = 1 → ‖ContinuousLinearMap.adjoint P w‖ = 1 → 0 < κ →
    Integrable (fun h : UJ ε' => ⟪w, σ (um h) w⟫_ℂ) ν →
    (∀ x : UJ ε', ∫ h : UJ ε', conj ⟪w, σ (um h) w⟫_ℂ * conj ⟪w, σ (um (h⁻¹ * x)) w⟫_ℂ ∂ν = κ * conj ⟪w, σ (um x) w⟫_ℂ) →
    (∀ a b : H, ∫ h : UJ ε', conj ⟪w, σ (um h) w⟫_ℂ * ⟪b, π (emb e (um h)) a⟫_ℂ ∂ν =
      κ * (⟪b, ContinuousLinearMap.adjoint P w⟫_ℂ * ⟪ContinuousLinearMap.adjoint P w, a⟫_ℂ)) →
    ∀ v ∈ lowKSub ε lam π, ‖v‖ = 1 →
      ∫⁻ g : UJ ε, ENNReal.ofReal (colSq (um g⁻¹) (zi e) * ‖⟪ContinuousLinearMap.adjoint P w, π (um g) v⟫_ℂ‖ ^ 2) ∂(muG ε) ≤
        ENNReal.ofReal ((8 * ((n : ℝ) + 1) * B) ^ (8 * (n + 1))) *
          ∫⁻ g : UJ ε, ENNReal.ofReal (‖⟪ContinuousLinearMap.adjoint P w, π (um g) v⟫_ℂ‖ ^ 2) ∂(muG ε)

def WordBd : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (B : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)), 2 ≤ m → Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam π → (∀ a, |lam a| ≤ B) →
    Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3) →
    ∀ v ∈ lowKSub ε lam π, v ∈ PI.PhMeasCore.smoothVecs (Jm ε) π ∧
      ∀ (S : ℕ) (W : List (Matrix (Fin m) (Fin m) ℂ)), W.length ≤ S → (∀ X ∈ W, hs X ≤ 1) →
        ‖dsigCW ε π W v‖ ≤ (8 * Real.sqrt m * (B + S)) ^ W.length * ‖v‖

def HeBranching : Prop :=
  ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ)
    (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    Fits ε ε' e → Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.IsHCParam mu → IsDS ε lam π → IsDS ε' mu σ → HeWord ε lam ε' mu →
    ∃ i : H' →ₗᵢ[ℂ] H, (∀ h : UJ ε', ∀ x, i (σ (um h) x) = π (emb e (um h)) (i x)) ∧
      ∀ j : H' →L[ℂ] H, (∀ h : UJ ε', ∀ x, j (σ (um h) x) = π (emb e (um h)) (j x)) → ∃ c : ℂ, ∀ x, j x = c • i x

section Analysis

open GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods Formalism.QuantumDeterminants

def VolR : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (μ : Measure (UJ ε)), μ.IsHaarMeasure → 1 ≤ m → ∀ δ R : ℝ, 0 < δ → δ ≤ 2 → 0 ≤ R →
    μ {g | hs (um g) ≤ R ^ 2} ≤ ENNReal.ofReal ((4 * m * (Real.sqrt m + 1) * R / δ) ^ (2 * m ^ 2)) * μ (ball ε δ)

def Decay : Prop :=
  ∀ (m N : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (A : Type) [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)), 1 ≤ m → m ≤ N → IsHCParam lam → IsDS ε lam π → GapAtLeast ε lam (200 * (N : ℝ) ^ 3) →
    ∀ v ∈ lowKSub ε lam π, ‖v‖ = 1 → ∀ (g₀ : UJ ε) (Y : ℝ), hs (um g₀) ≤ Y → ∀ g : UJ ε,
      ‖⟪π (um g₀) v, π (um g) (π (um g₀) v)⟫_ℂ‖ ≤
        Real.exp (6 * (N : ℝ) ^ 2 * Real.log m + 12 * (N : ℝ) ^ 2) * Y ^ (12 * N ^ 2) * hs (um g) ^ (-(6 * (N : ℝ) ^ 2))

def IntR : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (μ : Measure (UJ ε)), μ.IsHaarMeasure → 1 ≤ m → ∀ (φ : UJ ε → ℂ) (C a : ℝ), Continuous φ →
    (m : ℝ) ^ 2 + 1 ≤ a → (∀ g, ‖φ g‖ ≤ C * hs (um g) ^ (-a)) →
    Integrable φ μ ∧ ∫ g, ‖φ g‖ ∂μ ≤ C * (2 * (16 * (m : ℝ) ^ 2) ^ (2 * m ^ 2)) * μ.real (ball ε 1)

def HInt : Prop :=
  ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (ν : Measure (UJ ε')),
    ν.IsHaarMeasure → Fits ε ε' e → 2 ≤ n → ∀ (φ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ℂ) (C δ : ℝ), 0 ≤ C → 0 < δ → δ ≤ 1 →
    (∀ g : UJ ε, ‖φ (um g)‖ ≤ C * hs (um g) ^ (-(3 * ((n : ℝ) + 1) ^ 2))) → ∀ g : UJ ε,
      ∫⁻ h : UJ ε', ‖φ (um g * emb e (um h))‖ₑ ∂ν ≤
        ENNReal.ofReal (C * (100 * ((n : ℝ) + 1) ^ 2 / δ) ^ (10 * (n + 1) ^ 2) *
          colSq (um g) (zi e) ^ (-((2 * ((n : ℝ) + 1) + 5) / 2))) * ν (ball ε' δ)

def DUp : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (B : ℝ) (A : Type) [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)) (μ : Measure (UJ ε)) (d : ℝ), μ.IsHaarMeasure → 2 ≤ m → IsHCParam lam → IsDS ε lam π →
    (∀ a, |lam a| ≤ B) → GapAtLeast ε lam (100 * (m : ℝ) ^ 3) → IsFdeg μ π d →
    ENNReal.ofReal d * μ (ball ε ((100 * m * (B + 1)) ^ 2)⁻¹) ≤ 4

def Lip : Prop :=
  ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (B : ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1))
    (A : Type) [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (A →L[ℂ] A)) (ν : Measure (UJ ε')), ν.IsHaarMeasure → Fits ε ε' e → 2 ≤ n →
    IsHCParam lam → IsDS ε lam π → (∀ a, |lam a| ≤ B) → GapAtLeast ε lam (200 * ((n : ℝ) + 1) ^ 3) →
    ∀ v ∈ lowKSub ε lam π, ‖v‖ = 1 → ∀ (g₀ : UJ ε) (Y δ : ℝ), hs (um g₀) ≤ Y → 0 < δ → δ ≤ 1 →
    ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε' X →
      ∫⁻ h : UJ ε', ‖⟪π (um g₀) v, π (emb e (NormedSpace.exp (-X) * um h)) (π (um g₀) v)⟫_ℂ -
          ⟪π (um g₀) v, π (emb e (um h)) (π (um g₀) v)⟫_ℂ‖ₑ ∂ν ≤
        ENNReal.ofReal ((8 * ((n : ℝ) + 1) * B * Y / δ) ^ (20 * (n + 1) ^ 2) * Real.sqrt (hs X)) * ν (ball ε' δ)

def Analysis : Prop := VolR ∧ Decay ∧ IntR ∧ HInt ∧ DUp ∧ Lip

def incl (e : Fin n ⊕ Unit ≃ Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin n) ℂ :=
  Matrix.of fun a b => if a = e (Sum.inl b) then 1 else 0

def BigProj : Prop := ForPairs fun {n} ε lam ε' _ B e H H' _ _ _ _ _ _ π σ _ =>
  ∀ i : H' →L[ℂ] H, (∀ x, ‖i x‖ = ‖x‖) → (∀ h : UJ ε', ∀ x, i (σ (um h) x) = π (emb e (um h)) (i x)) →
    (∀ j : H' →L[ℂ] H, (∀ h : UJ ε', ∀ x, j (σ (um h) x) = π (emb e (um h)) (j x)) → ∃ c : ℂ, j = c • i) →
    ∀ v ∈ lowKSub ε lam π, ‖v‖ = 1 → ∃ g₀ : UJ ε, hs (um g₀) ≤ (8 * ((n : ℝ) + 1) * B) ^ (20 * (n + 1)) ∧
      Real.exp (-(100 * ((n : ℝ) + 1) ^ 3 * Real.log (8 * (n + 1) * B))) ≤ ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖

end Analysis

end GlobalTheory.CompanionTheory.PairingAnalysis

end
