import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace BranchingSupport.TensInh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

abbrev detRep (k r m : ℕ) : Rep k r where
  H := ℂ
  σ := fun g => (g.det ^ m) • ContinuousLinearMap.id ℂ ℂ

def rho2 (g : Mx k r) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, g.det]

def gam2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def dl (I c : Fin 2) : ℂ := if I = c then 1 else 0

theorem lenA_eq_lA (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a : Fin (r + 1)) :
    lenA k r z g a = Formalism.MainNotions.S.lA k r z g a := by
  classical
  let Lm : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    { toFun := fun v => WithLp.toLp 2 (g⁻¹ *ᵥ v)
      map_add' := fun v w => by simp [Matrix.mulVec_add]
      map_smul' := fun c v => by simp [Matrix.mulVec_smul] }
  let S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) := Submodule.span ℂ
    (Set.range fun b : {b : Fin r // b.val < a.val} => Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b.1))
  have hlt : ∀ b : Fin (r + 1), b < a → b.val < r :=
    fun b hb => Nat.lt_of_lt_of_le hb (Nat.le_of_lt_succ a.2)
  have hfv : ∀ (b : Fin (r + 1)) (hb : b < a),
      Formalism.QuantumDeterminants.fvec k r z b = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r ⟨b.val, hlt b hb⟩) := by
    intro b hb
    have hbr : b.val < r := hlt b hb
    simp [Formalism.QuantumDeterminants.fvec, hbr]
  have hspan : Submodule.span ℂ ((fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) :
      EuclideanSpace ℂ (Fin (2 * r + k + 1)))) '' {b | b < a}) = S.map Lm := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨_, ⟨⟨⟨b.val, hlt b hb⟩, hb⟩, rfl⟩, ?_⟩
      exact (congrArg (fun v => (WithLp.toLp 2 (g⁻¹ *ᵥ v) : EuclideanSpace ℂ (Fin (2 * r + k + 1))))
        (hfv b hb)).symm
    · rintro ⟨_, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
      refine ⟨⟨b.val, by have := b.2; omega⟩, hb, ?_⟩
      show WithLp.toLp 2 (g⁻¹ *ᵥ _) = _
      rw [hfv _ hb]
      rfl
  have hd : ∀ y, dist (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))
      (WithLp.toLp 2 (g⁻¹ *ᵥ y)) = Formalism.MainNotions.S.eucl (g⁻¹ *ᵥ (Formalism.QuantumDeterminants.fvec k r z a - y)) := by
    intro y
    rw [EuclideanSpace.dist_eq]
    simp [Formalism.MainNotions.S.eucl, Matrix.mulVec_sub, Complex.normSq_eq_norm_sq, dist_eq_norm]
  unfold lenA Formalism.MainNotions.S.lA
  rw [hspan, Metric.infDist_eq_iInf, ← sInf_range]
  congr 1
  ext t
  constructor
  · rintro ⟨⟨_, y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, hd y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨Lm y, y, hy, rfl⟩, hd y⟩

end BranchingSupport.TensInh
