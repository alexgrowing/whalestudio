import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTestModelBaseChangeCompletedLocStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsConstantCompletedLocalRingClosedPoiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointNormPsiCoordinateExpNegQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExistStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVectorStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceValuesIntegralTorsionBoundShortestVecStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormTorsionSumShortestVectorEqStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightZeroSectionUnitIntegralTorsionPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTestMatch
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∃ (τ : S.Test p y₀) (ε : D.toPre.X ≃+ τ.X), (∀ α s, PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ = Real.exp (-τ.q (ε α))) ∧ ∀ a α, yy a = QuotientAddGroup.mk α ↔ τ.yy a = QuotientAddGroup.mk (ε α) := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi
  obtain ⟨yy, hyy⟩ := GlobalTheory.T.torsionLabels_constant_completedLocalRing_closedPoint o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
  refine ⟨yy, ?_⟩
  intro p _ y ev hCen hev y₀ hAt
  obtain ⟨u, ε₀, hbc⟩ := GlobalTheory.T.exists_uniformisedTestModel_baseChange_completedLocal o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
    p y ev hCen hev y₀ hAt
  have hint : ∀ a : o', ‖y₀ (algebraMap o' S.R a)‖ ≤ 1 := by
    intro a
    rw [hAt]
    exact hCen.norm_val_le_one ((M.O x).algebraMap_mem a)
  have hL := GlobalTheory.firstFiveLaws.1
  have hL2 := GlobalTheory.firstFiveLaws.2.1
  have hT := GlobalTheory.ZH.uTors_closed
  obtain ⟨l⟩ := GlobalTheory.T.uniformisedModel_torsionLabels_exist hL hL2 hT o' Ω S ρ p y₀ u hint
  obtain ⟨τ, e, hq, hy⟩ := exists_test_match o' Ω S ρ p y₀ u l
    (GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL2 hT o' Ω S ρ p y₀ u l hint) (GlobalTheory.T.unitThetaConstants_generate_integralTorsion hL hL2 hT o' Ω S ρ p y₀ u l hint)
    (GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hT o' Ω S ρ p y₀ u l hint) (GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq hL hL2 hT o' Ω S ρ p y₀ u l hint)
    (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hT o' Ω S ρ p y₀ u l hint)
  refine ⟨τ, ε₀.trans e.symm, ?_, ?_⟩
  · intro α s hs
    rw [GlobalTheory.T.classicalPoint_norm_psi_coordinate_exp_neg_quadratic o' Ω S ρ M U₀ EE FinalForm R G gm D A U p y₀ ev u ε₀ hbc l α s hs, AddEquiv.trans_apply, hq,
      AddEquiv.apply_symm_apply]
  · intro a α
    rw [hyy p y ev hCen hev y₀ hAt u ε₀ hbc l a α, AddEquiv.trans_apply, hy, AddEquiv.apply_symm_apply]

end GlobalTheory.Poinc.TestAtPt
