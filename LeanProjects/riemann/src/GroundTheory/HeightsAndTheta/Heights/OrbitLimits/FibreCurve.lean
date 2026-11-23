import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets.FibreCurve

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

abbrev B1 : Unit → Type := fun _ => Fin 2

abbrev B2 : Fin 2 → Type := fun _ => Fin 2

section Curve

variable {Ω : Type} [Field Ω]

def pt (u : Ω) : (Σ k, B2 k) → Ω :=
  fun p => if p.1 = 0 then ![1, u] p.2 else ![1, u ^ 2] p.2

theorem pt_ne {u : Ω} (hu : u ≠ 0) (p : Σ k, B2 k) : pt u p ≠ 0 := by
  obtain ⟨k, i⟩ := p
  fin_cases k <;> fin_cases i <;> simp [pt, hu]

def eqn : MRing B2 :=
  X ⟨0, 0⟩ ^ 2 * X ⟨1, 1⟩ - X ⟨0, 1⟩ ^ 2 * X ⟨1, 0⟩

theorem X_not_mem {u : Ω} (hu : u ≠ 0) (p : Σ k, B2 k) : (X p : MRing B2) ∉ mCoordIdeal (pt u) := by
  intro hm
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X] at hm
  exact (mul_ne_zero (by simpa using pt_ne hu p) (X_ne_zero _)) hm

instance mCoordIdeal_isPrime (u : Ω) : (mCoordIdeal (pt u)).IsPrime :=
  RingHom.ker_isPrime _

theorem isMultiHomogIdeal (u : Ω) : IsMultiHomogIdeal (mCoordIdeal (pt u)) :=
  CoordinateConeArithVar.isMultiHomogIdeal _

def gen (u : Ω) : GenFibre (ι := B1) (ι' := B2) (blkV (Fin 2) 1) (mCoordIdeal (pt u)) :=
  Inter.genFibreOf _ _

theorem charZero [CharZero Ω] (u : Ω) : CharZero (gen u).Φ' := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (C (n : ℤ) : MRing B2) ∈ mCoordIdeal (pt u) := by
    rw [← (gen u).genericFibre_ker_target, RingHom.mem_ker]
    simpa using hn
  simp only [mCoordIdeal, RingHom.mem_ker, mConeMap] at hmem
  simpa using hmem

theorem x'_ne {u : Ω} (hu : u ≠ 0) (p : Σ k, B2 k) : (gen u).x' p ≠ 0 := fun h =>
  X_not_mem hu p (by rw [← (gen u).genericFibre_ker_target, RingHom.mem_ker, aeval_X]; exact h)

theorem x_ne {u : Ω} (hu : u ≠ 0) (p : Σ k, B1 k) : (gen u).x p ≠ 0 := by
  intro h
  apply x'_ne hu (blkV (Fin 2) 1 p)
  rw [(gen u).compat, h, map_zero]

def fb : FibreBlock (blkOf 1) := ⟨0, by rintro ⟨_, h⟩; simp [blkOf] at h⟩

def chart : ∀ k : FibreBlock (blkOf 1), fibreIdx B2 (blkOf 1) k := fun _ => (0 : Fin 2)

def fibrePoly (u : Ω) : MRingOver (gen u).Φ (fibreIdx B2 (blkOf 1)) :=
  C ((gen u).x ⟨(), 1⟩) * X ⟨fb, (0 : Fin 2)⟩ ^ 2 - C ((gen u).x ⟨(), 0⟩) * X ⟨fb, (1 : Fin 2)⟩ ^ 2

end Curve

end GroundTheory.Heights₂.Heights.Targets.FibreCurve
