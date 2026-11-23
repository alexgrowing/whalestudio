import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNestedLattice
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.DoubleBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockIdeal (x x' : Ix κ → Ω) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x x')

def blockLine (m : ConeMetric ℂ (Ix κ)) (k₀ : Fin 2) : HermLine (FinTwoTypeFamily κ) where
  a := Pi.single k₀ 1
  h z := m.ρ fun p : Ix κ => z ⟨k₀, p.2⟩
  pos z hz := m.pos _ fun h0 => by
    obtain ⟨i, hi⟩ := hz k₀
    exact hi (congrFun h0 ⟨(), i⟩)
  smul c z _ := by
    have e : (fun p : Ix κ => c k₀ * z ⟨k₀, p.2⟩) = c k₀ • fun p : Ix κ => z ⟨k₀, p.2⟩ := rfl
    show m.ρ (fun p : Ix κ => c k₀ * z ⟨k₀, p.2⟩) = _
    rw [e, m.smul, Finset.prod_eq_single k₀ (fun k _ hk => by simp [hk]) (by simp)]
    simp

def twoBlockList (m m' : ConeMetric ℂ (Ix κ)) (D i : ℕ) : Fin (D + 1) → HermLine (FinTwoTypeFamily κ) :=
  fun j => if (j : ℕ) < i then blockLine m 0 else blockLine m' 1

def twoBlockCoeff (I : AllFam) (x x' : Ix κ → Ω) (m m' : ConeMetric ℂ (Ix κ)) (D i : ℕ) : ℝ :=
  I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (twoBlockList m m' D i) -
    I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (twoBlockList m m' D (i + 1))

def twoBlockStep (x x' : Ix κ → Ω) (a b : ℕ) : ℝ :=
  Real.log ((sec ℤ x (a + 1) * sec ℤ x' b).toAddSubgroup.relIndex (sec ℤ x a * sec ℤ x' (b + 1)).toAddSubgroup)

theorem twoBlockList_zero (m m' : ConeMetric ℂ (Ix κ)) (D : ℕ) :
    twoBlockList m m' D 0 = fun _ => blockLine m' 1 := by
  funext j
  simp [twoBlockList]

theorem twoBlockList_last (m m' : ConeMetric ℂ (Ix κ)) (D : ℕ) :
    twoBlockList m m' D (D + 1) = fun _ => blockLine m 0 := by
  funext j
  simp [twoBlockList, j.2]

theorem sum_twoBlockCoeff (I : AllFam) (x x' : Ix κ → Ω) (m m' : ConeMetric ℂ (Ix κ)) (D : ℕ) :
    ∑ i ∈ Finset.range (D + 1), twoBlockCoeff I x x' m m' D i =
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (fun _ => blockLine m' 1) -
        I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (fun _ => blockLine m 0) := by
  unfold twoBlockCoeff
  rw [Finset.sum_range_sub', twoBlockList_zero, twoBlockList_last]

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
