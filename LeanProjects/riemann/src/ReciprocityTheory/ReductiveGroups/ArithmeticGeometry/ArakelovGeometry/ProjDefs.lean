import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo Polynomial

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

structure IsProjFrame (x : κ → Ω) (e : Fin (D + 1) → κ) : Prop where
  inj : Function.Injective e
  free : coordIdeal ℤ (x ∘ e) = ⊥
  integral : ∀ i, IsIntegral (coneRing ℤ (x ∘ e)) (C (x i) * X : Polynomial Ω)

structure IsRatProjFrame (x : κ → Ω) (e : Fin (D + 1) → κ) : Prop where
  inj : Function.Injective e
  free : coordIdeal ℤ (x ∘ e) = ⊥
  integral : ∀ i, IsIntegral (coneRing ℚ (x ∘ e)) (C (x i) * X : Polynomial Ω)

def fnField (x : κ → Ω) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ {t | ∃ i j, t = x i / x j}

def projDeg (x : κ → Ω) (e : Fin (D + 1) → κ) : ℕ :=
  IntermediateField.relfinrank (fnField (x ∘ e)) (fnField x)

open Classical in

def scaleOff (e : Fin (D + 1) → κ) (m : ℕ) (x : κ → Ω) : κ → Ω :=
  fun i => if i ∈ Set.range e then x i else (m : Ω) * x i

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
