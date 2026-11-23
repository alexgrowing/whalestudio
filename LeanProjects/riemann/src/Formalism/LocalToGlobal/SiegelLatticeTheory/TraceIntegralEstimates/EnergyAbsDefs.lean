import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def yv (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) (e : V) : HH :=
  ∫ z, ∫ s in Ω, ⟪W (s⁻¹ * z), e⟫_ℂ • σ (s⁻¹ * z) w ∂μS ∂ν

def Yop (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) : V →L[ℂ] HH :=
  ∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ V i)).smulRight (yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i))

theorem Yop_apply (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) (e : V) :
    Yop μS ν σ w W Ω e =
      ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i) := by
  simp only [Yop, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem Yop_apply_basis (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G)
    (j : Fin (Module.finrank ℂ V)) :
    Yop μS ν σ w W Ω (stdOrthonormalBasis ℂ V j) = yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V j) := by
  rw [Yop_apply, Finset.sum_eq_single j]
  · rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ V).orthonormal]; simp
  · intro i _ hij
    rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ V).orthonormal, if_neg hij, zero_smul]
  · intro h; exact absurd (Finset.mem_univ j) h

end Formalism.L2.S.Pv.EnergyAbs
