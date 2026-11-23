import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K]

def cor : Fin 2 → Fin 3 := ![0, 2]

@[simp] theorem cor_zero : cor 0 = 0 := rfl

@[simp] theorem cor_one : cor 1 = 2 := rfl

theorem w_cor (i : Fin 2) : w 3 (cor i) = w 2 i := by
  fin_cases i <;> rfl

structure IsCorner (ρ : NRep F 3 K) (σ : NRep F 2 K) : Prop where
  odd : ∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0
  r : ∀ g i j, σ.r g i j = ρ.r g (cor i) (cor j)
  ψ : ∀ v i g, σ.ψ v i g = ρ.ψ v (cor i) g
  mid : ∀ v g, ρ.r (F.loc0 v g) 1 1 = ρ.ψ v 1 g

def CornerUnits (ρ : NRep F 3 K) : Prop :=
  ∀ v, ∃ g, IsUnit (ρ.r (F.loc0 v g) 1 1 - ρ.ψ v 0 g) ∧ IsUnit (ρ.r (F.loc0 v g) 1 1 - ρ.ψ v 2 g) ∧
    IsUnit ((ρ.r (F.loc0 v g) 0 0 - ρ.ψ v 1 g) * (ρ.r (F.loc0 v g) 2 2 - ρ.ψ v 1 g) -
      ρ.r (F.loc0 v g) 0 2 * ρ.r (F.loc0 v g) 2 0)

theorem mid_mul (ρ : NRep F 3 K) (h : ∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0) (g g' : F.G0) :
    ρ.r (g * g') 1 1 = ρ.r g 1 1 * ρ.r g' 1 1 := by
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, h g 1 0 (by decide), h g 1 2 (by decide)]
  simp

end UpperTheory.V.Fr
