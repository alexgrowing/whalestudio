import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.PeriodIntegrals.DSInfCharCap
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace PositivityTheory.UnitaryDecomposition

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

def Out (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (B : ℝ)
    (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (ν : Measure (UJ ε')) : Prop :=
  ∃ (v : H) (P : H →L[ℂ] H') (w : H') (κ Y : ℝ), ‖v‖ = 1 ∧ Intertw ε' e π σ P ∧ P v ≠ 0 ∧ w = (‖P v‖⁻¹ : ℂ) • P v ∧
    0 < κ ∧ 1 ≤ Y ∧ Real.log Y ≤ 100 * ((n : ℝ) + 1) ^ 2 * Real.log (8 * (n + 1) * B) ∧
    Real.exp (-(1000 * ((n : ℝ) + 1) ^ 4 * Real.log (8 * (n + 1) * B))) ≤ ‖P v‖ ∧
    (∀ g : UJ ε, ‖⟪v, π (um g) v⟫_ℂ‖ ≤
      Real.exp (1000 * ((n : ℝ) + 1) ^ 4 * Real.log (8 * (n + 1) * B)) * hs (um g) ^ (-(3 * ((n : ℝ) + 1) ^ 2))) ∧
    Integrable (fun g : UJ ε => ⟪v, π (um g) v⟫_ℂ) (muG ε) ∧
    (∀ a b : H', Integrable (fun h : UJ ε' => conj ⟪v, π (emb e (um h)) v⟫_ℂ * ⟪b, σ (um h) a⟫_ℂ) ν ∧
      ∫ h : UJ ε', conj ⟪v, π (emb e (um h)) v⟫_ℂ * ⟪b, σ (um h) a⟫_ℂ ∂ν = κ * (⟪b, w⟫_ℂ * ⟪w, a⟫_ℂ)) ∧
    (∀ g : UJ ε, ∫⁻ h : UJ ε', ‖⟪v, π (um g * emb e (um h)) v⟫_ℂ‖ₑ ∂ν ≤
      ENNReal.ofReal (κ * Real.exp (1000 * ((n : ℝ) + 1) ^ 4 * Real.log (8 * (n + 1) * B)) *
        colSq (um g) (zi e) ^ (-((2 * ((n : ℝ) + 1) + 5) / 2)))) ∧
    Formalism.L2.Theta.SmoothVec {X | inG ε' X} σ w ∧
    ∀ (S : ℕ) (W : List (Matrix (Fin n) (Fin n) ℂ)), W.length ≤ S → (∀ X ∈ W, inG ε' X ∧ hs X ≤ 1) →
      ‖W.foldr (Formalism.L2.Theta.dRep σ) w‖ ≤ (8 * Real.sqrt (n + 1) * (B + S) * Y) ^ W.length / ‖P v‖

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

def RealPlace : Prop := ForPairs fun ε lam ε' mu B e _ _ _ _ _ _ _ _ π σ ν => HeWord ε lam ε' mu → Out ε ε' e B π σ ν

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

section Tens

variable {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def actT (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → H) : Fin m → H :=
  fun c => ∑ d, g⁻¹ d c • π g (x d)

def formT (ε : Fin m → Bool) (y x : Fin m → H) : ℂ := ∑ l, (if ε l then 1 else -1) * ⟪y l, x l⟫_ℂ

def casT (ε : Fin m → Bool) (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (x : Fin m → H) : Fin m → H :=
  fun c => ∑ l, dsigC ε π (Matrix.single c l 1) (x l)

def SmT (ε : Fin m → Bool) (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) : Set (Fin m → H) :=
  {x | ∀ l, x l ∈ PI.PhMeasCore.smoothVecs (Jm ε) π}

structure Dec (ε : Fin m → Bool) (lam : Fin m → ℝ) (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) : Type 1 where
  S : Finset (Fin m)
  Hs : Fin m → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  πs : ∀ s, Matrix (Fin m) (Fin m) ℂ → (Hs s →L[ℂ] Hs s)
  ds : ∀ s ∈ S, Formalism.QuantumDeterminants.IsHCParam (lam - Pi.single s 1) ∧ IsDS ε (lam - Pi.single s 1) (πs s)
  p : Fin m → (Fin m → H) → Fin m → H
  pr : ∀ s, (Fin m → H) → Hs s
  c : Fin m → ℂ
  κ : Fin m → ℂ
  p_sm : ∀ s ∈ S, ∀ x ∈ SmT ε π, p s x ∈ SmT ε π
  sum : ∀ x ∈ SmT ε π, ∑ s ∈ S, p s x = x
  p_act : ∀ s ∈ S, ∀ g : UJ ε, ∀ x ∈ SmT ε π, p s (actT π (um g) x) = actT π (um g) (p s x)
  pr_act : ∀ s ∈ S, ∀ g : UJ ε, ∀ x ∈ SmT ε π, pr s (actT π (um g) x) = πs s (um g) (pr s x)
  form : ∀ s ∈ S, ∀ x ∈ SmT ε π, ∀ y ∈ SmT ε π, formT ε y (p s x) = c s * ⟪pr s y, pr s x⟫_ℂ
  cas : ∀ s ∈ S, ∀ x ∈ SmT ε π, casT ε π (p s x) = κ s • p s x
  κ_inj : Set.InjOn κ S

attribute [instance] Dec.nH Dec.iH Dec.cH

end Tens

def DecEx : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)), (∃ a, ε a = false) →
    (univ.filter fun a => ε a = false).card ≤ (univ.filter fun a => ε a = true).card →
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam π → Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3) → Nonempty (Dec ε lam π)

def Comat : Prop := ForPairs fun {n} ε lam ε' _ B e H H' _ _ _ _ _ _ π σ _ => ∀ (X : Dec ε lam π), ∀ s ∈ X.S,
  (∀ v ∈ lowKSub ε lam π, ∀ l c, ‖X.p s (Pi.single l v) c‖ ≤ (8 * ((n : ℝ) + 1) * B) ^ (4 * (n + 1)) * ‖v‖) ∧
  ∃ γ : ℂ, ‖γ‖ ≤ (8 * ((n : ℝ) + 1) * B) ^ (n + 1) ∧ ∀ P : H →L[ℂ] H', Intertw ε' e π σ P →
    ∀ η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π, P (X.p s (Pi.single (zi e) η) (zi e)) = γ • P η

end PositivityTheory.UnitaryDecomposition
