import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormOfParts
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsThetaFnAndNeZeroOfIsFn
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEqMulCanonicalThetaOfSignMultiplier
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.VolumeFundamentalDomainPeriodLattice
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SetIntegralPeriodLatticeEqVolumeMulCube

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem keyIn_normal_form_and_archimedean_constant :
    ThetaUnifAV → ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
      u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
      IsAddFundamentalDomain u.Λ Fd volume →
      nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
      nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
      ∃ (u' : HolUnif x.P.A x.P.L x.P.g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
        τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧
        (∀ z, z ∈ u'.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
        u'.IsRig x.rig ∧ c ≠ 0 ∧ u'.IsFn x.th (fun z => c * thetaChar τ a b z) ∧ M.det ≠ 0 ∧
        (∀ i, u'.IsDiff ((2 * Real.pi * Complex.I)⁻¹ • M i) (x.v i)) ∧
        ‖M.det ^ 4 / c ^ 8‖ * nth ^ 4 * nη ^ 2 = (2 * Real.pi) ^ (2 * x.P.g) :=
  KeyNormalForm.normal_form_of_parts unimodular_and_tangent_of_isAH isDiff_sum_smul_of_isLieComb
    isThetaFn_and_ne_zero_of_isFn exists_eq_mul_canonical_theta_of_sign_multiplier
    volume_fundamentalDomain_periodLattice setIntegral_periodLattice_eq_volume_mul_cube

end GlobalTheory
