import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EigenTensorFullLeftSupport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroupStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorEigenDiagonalThetaOrderTwoStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaTensorNeZeroStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddTensor

theorem full_left_support : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S), (2 : F) ≠ 0 → ∀ (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∀ π : EA P p 2 →ₗ[F] EA P p 2, TensorProduct.map π (LinearMap.id : EA P p 2 →ₗ[F] EA P p 2) (∑ i, TensorProduct.tmul F (t i) (t' i)) = 0 → π = 0 := by
  intro h1 h2 S _ P F _ _ p h2F th n t t' hadd hth
  choose Φ hΦ hΦu _ using GlobalTheory.ThetaLin.main S P F p 2
  refine GlobalTheory.eigenTensor_full_left_support F (EA P p 2) (EA P p 2)
    {θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p) // θ.pt ^ 2 = 1}
    (fun θ => (Φ θ.1 : EA P p 2 →ₗ[F] EA P p 2)) (fun θ => Φ θ.1) ?_ _
    (GlobalTheory.T.additionFormula_tensor_ne_zero S P F p th n t t' hadd hth) ?_
  · intro U hU
    refine (GlobalTheory.T.abelian_sections_irreducible_theta_group h1 h2 S P F p 2 (by exact_mod_cast h2F)).2 U ?_
    intro θ hθ v v' hvv' hv
    have e : v' = Φ θ v := hΦu θ v.sec v'.sec hvv'
    rw [e]
    exact hU ⟨θ, hθ⟩ v hv
  · intro θ
    obtain ⟨r, hr⟩ := GlobalTheory.T.additionTensor_eigen_diagonal_theta_order_two h1.globalFns S P F p th n t t' (fun i => Φ θ.1 (t i)) (fun i => Φ θ.1 (t' i))
      hadd θ.1 θ.2 (fun i => ⟨hΦ θ.1 (t i), hΦ θ.1 (t' i)⟩)
    refine ⟨r, Eq.trans ?_ hr⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => TensorProduct.map_tmul _ _ _ _

end GlobalTheory.AddTensor
