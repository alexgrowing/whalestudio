import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinMulti

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal

variable {n : ℕ}

abbrev Mat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

def embH (e : Option (Fin n) ≃ Fin (n + 1)) (h : Mat n) : Mat (n + 1) :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => h i j
    | none, none => 1
    | _, _ => 0

def embL (e : Option (Fin n) ≃ Fin (n + 1)) (X : Mat n) : Mat (n + 1) :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => X i j
    | _, _ => 0

def Signs (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) : Prop :=
  ε (e none) = true ∧ ∀ i, ε (e (some i)) = ε' i

def hsn {m : ℕ} (g : Mat m) : ℝ := Real.sqrt (∑ a, ∑ b, ‖g a b‖ ^ 2)

def colLen (e : Option (Fin n) ≃ Fin (n + 1)) (g : Mat (n + 1)) : ℝ := Real.sqrt (∑ a, ‖g a (e none)‖ ^ 2)

def Interlaced (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ) : Prop :=
  ∀ x y : Fin (n + 1) ⊕ Fin n, Sum.elim lam mu y < Sum.elim lam mu x →
    (∀ z, ¬ (Sum.elim lam mu y < Sum.elim lam mu z ∧ Sum.elim lam mu z < Sum.elim lam mu x)) →
      (Sum.elim ε ε' x = Sum.elim ε ε' y ↔ x.isLeft ≠ y.isLeft)

section Reps

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

def IsHMap (e : Option (Fin n) ≃ Fin (n + 1)) (ε' : Fin n → Bool) (π : Mat (n + 1) → (H →L[ℂ] H)) (σ : Mat n → (H' →L[ℂ] H'))
    (j : H' →L[ℂ] H) : Prop := ∀ h ∈ UJset ε', ∀ w, j (σ h w) = π (embH e h) (j w)

def IsProj (e : Option (Fin n) ≃ Fin (n + 1)) (ε' : Fin n → Bool) (π : Mat (n + 1) → (H →L[ℂ] H)) (σ : Mat n → (H' →L[ℂ] H'))
    (j : H' →L[ℂ] H) (P : H →L[ℂ] H') : Prop :=
  IsHMap e ε' π σ j ∧ (∀ w, ‖j w‖ = ‖w‖) ∧ (∀ v w, ⟪j w, v⟫_ℂ = ⟪w, P v⟫_ℂ) ∧ ∀ j', IsHMap e ε' π σ j' → ∃ c : ℂ, j' = c • j

end Reps

structure Par (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ)
    (B : ℝ) : Prop where

  signs : Signs e ε ε'

  three_le : 3 ≤ n

  hlam : IsHCParam lam

  hmu : IsHCParam mu

  word : Interlaced ε lam ε' mu

  word' : ∀ s, Interlaced ε (lam - Pi.single s 1) ε' mu

  wide : ∀ a c, a < c → 2 ≤ lam a - lam c

  wide' : ∀ a c, a < c → 2 ≤ mu a - mu c

  gap : GapAtLeast ε lam (1000 * ((n : ℝ) + 1) ^ 3)

  gap' : GapAtLeast ε' mu (1000 * ((n : ℝ) + 1) ^ 3)

  neg : ∃ i, ε' i = false

  pos : (univ.filter fun i => ε' i = false).card ≤ (univ.filter fun i => ε' i = true).card

  bound : (∀ a, |lam a| ≤ B) ∧ ∀ i, |mu i| ≤ B

def ForPair (Q : ∀ (n : ℕ) (_ : Option (Fin n) ≃ Fin (n + 1)) (_ : Fin (n + 1) → Bool) (_ : Fin (n + 1) → ℝ) (_ : Fin n → Bool)
    (_ : Fin n → ℝ) (_ : ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'],
    (Mat (n + 1) → (H →L[ℂ] H)) → (Mat n → (H' →L[ℂ] H')) → Prop) : Prop :=
  ∀ (n : ℕ) (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ)
    (B : ℝ), Par e ε lam ε' mu B → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
      [InnerProductSpace ℂ H'] (π : Mat (n + 1) → (H →L[ℂ] H)) (σ : Mat n → (H' →L[ℂ] H')), IsDS ε lam π → IsDS ε' mu σ →
      Q n e ε lam ε' mu B H H' π σ

def big (C : ℝ) (n : ℕ) (B : ℝ) : ℝ := Real.exp (C * ((n : ℝ) + 1) ^ 4 * Real.log (8 * ((n : ℝ) + 1) * B))

def nbh {m : ℕ} (ε : Fin m → Bool) (δ : ℝ) : Set (UJ ε) := {g | hsn (umat g - 1) ≤ δ}

def Moment : Prop := ∃ C : ℝ, 0 < C ∧ ForPair fun n e ε lam ε' mu B _ _ _ _ _ _ π σ => ∀ j P, IsProj e ε' π σ j P →
  ∀ v₀ w₀, IsLowUnit ε lam π v₀ → IsLowUnit ε' mu σ w₀ →
    ∫⁻ g, ENNReal.ofReal (colLen e (umat g⁻¹) ^ 2 * ‖⟪j w₀, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂muG ε ≤
      ENNReal.ofReal ((8 * ((n : ℝ) + 1) * B) ^ (C * ((n : ℝ) + 1))) * ∫⁻ g, ENNReal.ofReal (‖⟪j w₀, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂muG ε

def LargeProj : Prop := ∃ C : ℝ, 0 < C ∧ ForPair fun n e ε lam ε' _ B _ _ _ _ _ _ π σ => ∀ j P, IsProj e ε' π σ j P →
  ∀ v₀, IsLowUnit ε lam π v₀ → ∀ d, IsFdeg (muG ε') σ d → ∃ g₀ ∈ UJset ε, hsn g₀ ≤ (8 * ((n : ℝ) + 1) * B) ^ (C * ((n : ℝ) + 1)) ∧
    ((muG ε') (nbh ε' (1 / 4))).toReal ≤ big C n B * (‖P (π g₀ v₀)‖ ^ 2 / d)

def RealInput : Prop := ∃ C : ℝ, 0 < C ∧ ForPair fun n e ε lam ε' _ B H H' _ _ _ _ π σ =>
  ∃ (v₀ v : H) (g₀ : Mat (n + 1)) (w' : H') (c : ℝ), IsLowUnit ε lam π v₀ ∧ g₀ ∈ UJset ε ∧ v = π g₀ v₀ ∧
    SmV (lieOf (Jm ε)) π v ∧ SmV (lieOf (Jm ε')) σ w' ∧ ‖w'‖ = 1 ∧ 0 < c ∧
    (∀ a b : H', ∫ h, star ⟪v, π (embH e (umat h)) v⟫_ℂ * ⟪b, σ (umat h) a⟫_ℂ ∂muG ε' = (c : ℂ) * (⟪w', a⟫_ℂ * ⟪b, w'⟫_ℂ)) ∧
    (∀ g ∈ UJset ε, Integrable (fun h => ⟪v, π (g * embH e (umat h)) v⟫_ℂ) (muG ε') ∧
      ∫ h, ‖⟪v, π (g * embH e (umat h)) v⟫_ℂ‖ ∂muG ε' ≤ c * big C n B * colLen e g ^ (-(2 * (n : ℝ) + 7))) ∧
    (∀ X ∈ lieOf (Jm ε'), hsn X ≤ 1 → Integrable (fun h => ⟪dR π (embL e X) v, π (embH e (umat h)) v⟫_ℂ) (muG ε') ∧
      ∫ h, ‖⟪dR π (embL e X) v, π (embH e (umat h)) v⟫_ℂ‖ ∂muG ε' ≤ c * big C n B) ∧
    ∃ A : ℝ, ∀ g ∈ UJset ε, ‖⟪v, π g v⟫_ℂ‖ ≤ A * hsn g ^ (-(20 * ((n : ℝ) + 1) ^ 2))

theorem embH_one (e : Option (Fin n) ≃ Fin (n + 1)) : embH e 1 = 1 := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embH, Matrix.one_apply]

example : Interlaced (n := 1) ![true, false] ![5 / 2, 1 / 2] ![false] ![0] := by
  intro x y h h'
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;> simp at h ⊢ <;> try linarith
  have := h' (Sum.inl 1)
  norm_num at this

def ProjExists : Prop := ForPair fun _ e _ _ ε' _ _ _ _ _ _ _ _ π σ => ∃ j P, IsProj e ε' π σ j P

theorem embH_mul (e : Option (Fin n) ≃ Fin (n + 1)) (h h' : Mat n) : embH e (h * h') = embH e h * embH e h' := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases a <;> cases b <;> simp [embH, Matrix.mul_apply]

def eEx : Option (Fin 3) ≃ Fin 4 where
  toFun := fun o => match o with | none => 0 | some i => ![2, 3, 1] i
  invFun := ![none, some 2, some 0, some 1]
  left_inv := by decide
  right_inv := by decide

end GlobalTheory.SepReal

end
