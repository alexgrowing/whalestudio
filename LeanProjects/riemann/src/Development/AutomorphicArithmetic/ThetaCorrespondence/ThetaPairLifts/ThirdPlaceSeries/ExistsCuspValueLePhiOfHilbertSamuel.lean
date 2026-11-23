import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspValueLePhiOfHilbertSamuel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JetsOfConstantSection
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JetNumUbStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumbersAtPointStatement

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp
set_option maxHeartbeats 2000000 in
theorem exists_cusp_value_le_phi_of_hilbertSamuel_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ w : space TF.X Z Y.U la, evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 ∧ (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) ≤ φT / 2500 := by
  intro h1 h2 h3 h4
  refine ((((_root_.GlobalTheory.T.jets_constant_section_eq_alt h1 h2 h3 h4).and (_root_.GlobalTheory.T.jetNum_thA_ub h3)).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt h3)).and ((_root_.GlobalTheory.T.jetNum_nCol_lenT_bounds_of_quo h3).and h3)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C, hC, x0, hJ⟩, ⟨C1, hC1, x1, hN⟩⟩, ⟨C2, hC2, x2, hA⟩⟩, ⟨⟨C3, hC3, x3, hB⟩, ⟨C4, hC4, x4, hS⟩⟩⟩ := h
  refine ⟨C, hC, max (max x0 x1) (max x2 (max x3 x4)), fun x hx' hle ι p hp i hi Y hY Z TF la hla y hy T io y' g φT hg hφT hpt => ?_⟩
  have l0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have l1 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have l2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have l3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hle
  have l4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hle
  obtain ⟨-, -, hfin, hquo, -⟩ := hA x hx' l2 ι p hp i hi
  obtain ⟨⟨u1, hu1⟩, -⟩ := (hS x hx' l4 ι p hp i).2.2.2.2.2.2 hi
  have hnum : GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) (1 / 2500) := by
    rcases hla with rfl | hla
    · have := (hB x hx' l3 ι p hp i hi u1 hu1).1
      rwa [hquo u1 hu1] at this
    · rw [Set.mem_singleton_iff] at hla
      subst hla
      exact hN x hx' l1 ι p hp i hi
  obtain ⟨f, hf0, hfb⟩ := hJ x hx' l0 ι p hp i hi Y hY Z TF la hla (1 / 2500) hnum y hy T io y' g φT hg hφT hpt
  have hE : Extends TF.X Z Y.U la := GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace (Fm.D x ι) p.T.toCore ((i : ℕ) + 1) Y _ _ hY.1 hfin Z TF la
  refine ⟨hE.equiv f, ?_⟩
  have e : ofSpace TF.X Z Y.U la (hE.equiv f) = f := hE.equiv.symm_apply_apply f
  rw [e]
  refine ⟨hf0, ?_⟩
  rw [div_eq_mul_one_div, mul_comm]
  exact hfb
end GlobalTheory.HSApp
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_cusp_value_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ w : space TF.X Z Y.U la, evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 ∧ (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) ≤ φT / 2500 := by
  first | exact @_root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel_alt | exact _root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel_alt | (intros; apply _root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel_alt <;> assumption)
end
end
