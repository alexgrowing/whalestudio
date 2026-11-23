import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.IsHWSmooth

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

variable {n : ℕ}

def IsHMap {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (j : H' →L[ℂ] H) : Prop :=
  ∀ h : UJ ε', ∀ x, j (σ (um h) x) = π (emb e (um h)) (j x)

structure Gp (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ)
    (e : Fin n ⊕ Unit ≃ Fin (n + 1)) : Prop where
  fits : Fits ε ε' e
  two : 2 ≤ n
  neg : ∃ a, ε a = false
  le : (univ.filter fun a => ε a = false).card ≤ (univ.filter fun a => ε a = true).card
  hc : Formalism.QuantumDeterminants.IsHCParam lam
  hc' : Formalism.QuantumDeterminants.IsHCParam mu
  gap : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((n : ℝ) + 1) ^ 3)
  gap' : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((n : ℝ) + 1) ^ 3)

def OccAt (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ)
    (e : Fin n ⊕ Unit ≃ Fin (n + 1)) : Prop :=
  ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsDS ε lam π → IsDS ε' mu σ → ∃ j : H' →L[ℂ] H, j ≠ 0 ∧ IsHMap ε' e π σ j

def OccSome (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ)
    (e : Fin n ⊕ Unit ≃ Fin (n + 1)) : Prop :=
  ∃ (H H' : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
    (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsDS ε lam π ∧ IsDS ε' mu σ ∧ ∃ j : H' →L[ℂ] H, j ≠ 0 ∧ IsHMap ε' e π σ j

def ForGp (Q : ∀ {n : ℕ}, (Fin (n + 1) → Bool) → (Fin (n + 1) → ℝ) → (Fin n → Bool) → (Fin n → ℝ) →
    (Fin n ⊕ Unit ≃ Fin (n + 1)) → Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ)
    (e : Fin n ⊕ Unit ≃ Fin (n + 1)), Gp ε lam ε' mu e → Q ε lam ε' mu e

def Occ : Prop := ForGp fun ε lam ε' mu e => HeWord ε lam ε' mu → OccAt ε lam ε' mu e

def Models : Prop := ForGp fun ε lam ε' mu e => OccSome ε lam ε' mu e ↔ OccAt ε lam ε' mu e

def SchurK {m : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ε : Fin m → Bool)
    (σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)) (ν : Measure (UJ ε)) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ v w v' w' : K, Integrable (fun g : UJ ε => ⟪w, σ (um g) v⟫_ℂ * conj ⟪w', σ (um g) v'⟫_ℂ) ν ∧
    ∫ g : UJ ε, ⟪w, σ (um g) v⟫_ℂ * conj ⟪w', σ (um g) v'⟫_ℂ ∂ν = κ * (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ)

def ForMod (Q : ∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (_ : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (_ : Fin n → ℝ)
    (_ : Fin n ⊕ Unit ≃ Fin (n + 1)) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'],
    (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) → (Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) →
    Measure (UJ ε') → Prop) : Prop :=
  ForGp fun {n} ε lam ε' mu e => ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (ν : Measure (UJ ε')), ν.IsHaarMeasure → IsDS ε lam π → IsDS ε' mu σ → Q ε lam ε' mu e π σ ν

def OfInt : Prop := ForMod fun _ _ ε' mu e H H' _ _ _ _ _ _ π σ ν =>
  ∀ w ∈ lowKSub ε' mu σ, ‖w‖ = 1 → ∀ a b : H,
    ∫ h : UJ ε', conj ⟪w, σ (um h) w⟫_ℂ * ⟪b, π (emb e (um h)) a⟫_ℂ ∂ν ≠ 0 → ∃ j : H' →L[ℂ] H, j ≠ 0 ∧ IsHMap ε' e π σ j

def Seed : Prop := ForMod fun ε _ ε' mu e H H' _ _ _ _ _ _ π σ ν =>
  (∃ j : H' →L[ℂ] H, j ≠ 0 ∧ IsHMap ε' e π σ j) → ∀ κ : ℝ, SchurK ε' σ ν κ → ∀ w ∈ lowKSub ε' mu σ, ‖w‖ = 1 →
    Integrable (fun h : UJ ε' => ⟪w, σ (um h) w⟫_ℂ) ν ∧
    ∃ (i : H' →L[ℂ] H) (η : H), (∀ x, ‖i x‖ = ‖x‖) ∧ IsHMap ε' e π σ i ∧ η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π ∧
      ⟪η, i w⟫_ℂ ≠ 0 ∧ ∀ a : H, ∫ h : UJ ε', conj ⟪w, σ (um h) w⟫_ℂ * ⟪η, π (emb e (um h)) a⟫_ℂ ∂ν =
        κ * (⟪η, i w⟫_ℂ * ⟪i w, a⟫_ℂ)

def StepL : Prop := ForGp fun ε lam ε' mu e => ∀ s, Gp ε (lam - Pi.single s 1) ε' mu e → (∀ j, lam s - 1 / 2 ≠ mu j) →
  OccAt ε lam ε' mu e → OccAt ε (lam - Pi.single s 1) ε' mu e

def StepM : Prop := ForGp fun ε lam ε' mu e => ∀ j, Gp ε lam ε' (mu - Pi.single j 1) e → (∀ s, mu j - 1 / 2 ≠ lam s) →
  OccAt ε lam ε' mu e → OccAt ε lam ε' (mu - Pi.single j 1) e

def Base : Prop := ForGp fun {n} ε lam ε' mu e => HeWord ε lam ε' mu → ∃ a : Fin (n + 1) ⊕ Fin n → ℕ,
  (∀ x y, Sum.elim lam mu x ≤ Sum.elim lam mu y → a x ≤ a y) ∧
    OccAt ε (lam + fun i => (a (Sum.inl i) : ℝ)) ε' (mu + fun j => (a (Sum.inr j) : ℝ)) e

def DecEx2 : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)), (∃ a, ε a = false) → (∃ a, ε a = true) →
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam π → Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3) →
    ∃ X : Dec ε lam π, (∀ s, s ∈ X.S ↔ Formalism.QuantumDeterminants.IsHCParam (lam - Pi.single s 1)) ∧
      ∀ s, X.κ s = (lam s : ℂ) + ((m : ℂ) - 1) / 2

def dg {m : ℕ} (d : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun a => ((d a : ℝ) : ℂ)

def blk0 (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0)

def Frame : Prop :=
  ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ)
    (e : Fin n ⊕ Unit ≃ Fin (n + 1)), Fits ε ε' e → Function.Injective (Sum.elim d d') → HeWord ε d ε' d' →
    ∃ g : UJ ε, (∀ Y, trace (dg d * (um g⁻¹ * blk0 e Y * um g)) = trace (dg d' * Y)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ h : UJ ε', hs (um h - 1) ≤ C * hs (emb e (um h)) *
        hs (dg d - (um g⁻¹ * emb e (um h⁻¹) * um g) * dg d * (um g⁻¹ * emb e (um h) * um g))

def HWEx : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)), 2 ≤ m → Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3) →
    ∃ w ∈ lowKSub ε lam σ, ReciprocityTheory.ChartRestriction.DS.Lap.Base.IsHWSmooth ε σ lam w

def Conc : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (d Λ₀ : Fin m → ℝ) (k : ℕ), 2 ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
    ∀ (lam : Fin m → ℝ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)) (w : K), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
      Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3) → w ∈ lowKSub ε lam σ →
      ReciprocityTheory.ChartRestriction.DS.Lap.Base.IsHWSmooth ε σ lam w → ReciprocityTheory.ChartRestriction.DS.lowK ε lam = t • d + Λ₀ →
      ∀ x : UJ ε, (t * hs (dg d - um x⁻¹ * dg d * um x)) ^ k * ‖⟪w, σ (um x) w⟫_ℂ‖ ^ 2 ≤ C * hs (um x) ^ (2 * k)

end PositivityTheory.RgHe
