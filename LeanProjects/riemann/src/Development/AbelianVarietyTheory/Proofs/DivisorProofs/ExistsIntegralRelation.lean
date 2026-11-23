import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralConeRingOfForallValuationSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentsOfConeIntegralEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioMemValuationSubringAtGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemRelationOfGenericPointStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.SecIntegral

theorem exists_integral_relation : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∃ (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F), (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) * S.powVal x.1 th ^ (k : ℕ) = 0 := by
  intro F _ S hS r e u th hcov
  have hI : AlgebraicGeometry.IsIntegral S.Y := hS.isIntegral
  have hη : IsGenericPoint (genericPoint S.Y) Set.univ := by
    simpa using genericPoint_spec S.Y
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_integral_relation_C_mul_X_pow_of_valuationSubring F (S.Y.residueField (genericPoint S.Y)) (S.baseHom (resPt (genericPoint S.Y))) r e
    (fun i => S.val (resPt (genericPoint S.Y)) (S.comb (u i))) (S.powVal (resPt (genericPoint S.Y)) th)
    (GlobalTheory.T.exists_ratio_mem_valuationSubring_at_generic_point F S hS r e u th hcov _ hη)
  obtain ⟨a, ha, h0⟩ := GlobalTheory.T.homogeneous_components_of_cone_integral_equation _ _ _ r e m _ _ b hb
  exact ⟨m, a, ha, GlobalTheory.T.linearSystem_relation_of_generic_point F S hI r e u th _ hη m a ha h0⟩

end GlobalTheory.SecIntegral
