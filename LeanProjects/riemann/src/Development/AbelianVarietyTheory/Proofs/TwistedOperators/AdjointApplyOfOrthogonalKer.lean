import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.PhaseBreaksTargetParts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemilinearInjectiveOfIndep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftJointEigenspaceIntoOnePartStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqZeroOfMemRangeAdjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerConjFormsEqCsumAt

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem adjoint_apply_of_orthogonal_ker {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {u : H} {l : ℂ}
    (hu : u ∈ (LinearMap.ker T)ᗮ) (h : T (LinearMap.adjoint T (T u)) = l • T u) : LinearMap.adjoint T (T u) = l • u := by
  have hk : LinearMap.adjoint T (T u) - l • u ∈ LinearMap.ker T := by
    rw [LinearMap.mem_ker, map_sub, map_smul, h, sub_self]
  have hr : LinearMap.adjoint T (T u) ∈ (LinearMap.ker T)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk'
    rw [LinearMap.adjoint_inner_right, LinearMap.mem_ker.mp hk', inner_zero_left]
  have ho : LinearMap.adjoint T (T u) - l • u ∈ (LinearMap.ker T)ᗮ :=
    Submodule.sub_mem _ hr (Submodule.smul_mem _ l hu)
  have hz := Submodule.inner_right_of_mem_orthogonal hk ho
  rwa [inner_self_eq_zero, sub_eq_zero] at hz

theorem inner_apply_of_adjoint_eq {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {u : H} {l : ℝ}
    (h : LinearMap.adjoint T (T u) = (l : ℂ) • u) (w : H) : ⟪T u, T w⟫_ℂ = (l : ℂ) * ⟪u, w⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_left, h, inner_smul_left, Complex.conj_ofReal]

theorem conj_csumAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) :
    starRingEnd ℂ (GlobalTheory.LiftLower.csumAt S ((starRingEnd ℂ).comp σ) f g) = GlobalTheory.LiftLower.csumAt S σ f g := by
  unfold GlobalTheory.LiftLower.csumAt
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, RingHom.comp_apply, map_sum, map_mul,
    Complex.star_def, Complex.conj_conj]

end GlobalTheory.ConjScalar
