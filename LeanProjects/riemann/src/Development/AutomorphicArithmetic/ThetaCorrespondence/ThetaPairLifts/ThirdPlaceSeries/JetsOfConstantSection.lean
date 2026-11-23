import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.JetsOfConstantSection
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsCuspWithThetaJetValueLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundaryValuationTwistInvariant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftGapsStatement

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
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.JetsCst.jets_of_constant_section_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f : Cusp Z Y.U la, evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 ∧ (vV T.V (evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂))) : ℝ) ≤ cst * φT := by
  intro hP hD hS hF
  have hA := _root_.GlobalTheory.T.theta_jet_cusp_value_bound_alt hP hD hS hF
  have hB := _root_.GlobalTheory.T.cuspOn_boundary_valuation_of_four_dvd hP hD hS hF
  have hG := _root_.GlobalTheory.T.weight_antitone_boundary' hS
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at hA hB hG ⊢
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and hA hB) hG) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, hC1, x1, h1⟩, ⟨C2, hC2, x2, h2⟩⟩, ⟨C3, hC3, x3, h3⟩⟩
  refine ⟨0, le_rfl, max x1 (max x2 x3), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have a := h1 x hx ((le_max_left _ _).trans hle) ι p hp i hi Y hY
  have b := h2 x hx ((le_max_left _ _).trans ((le_max_right _ _).trans hle)) ι p hp i hi Y hY
  have c := h3 x hx ((le_max_right _ _).trans ((le_max_right _ _).trans hle)) ι p hp i hi Y hY
  intro Z TF la hla cst hJ y hy T io y' g φT hg hφ hfac
  obtain ⟨f, hf, hne, hv⟩ := a Z TF la hla cst hJ y hy T io y' g φT hg hφ hfac
  obtain ⟨hp1, hgap⟩ := c
  obtain ⟨hanti, hgp⟩ := hgap la hla
  have hb : ∀ τ j, |(la τ j : ℝ)| ≤ ∑ τ', ∑ j', |(la τ' j' : ℝ)| := fun τ j =>
    (Finset.single_le_sum (f := fun j' => |(la τ j' : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun τ' => ∑ j', |(la τ' j' : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have hev : Even (GlobalTheory.RefSum.nCol (dat p i)) := by
    obtain ⟨k, hk⟩ := GlobalTheory.RefSum.eight_dvd_nCol (Dw := dat p i)
    exact ⟨4 * k, by omega⟩
  have hw := (GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)) _ hp1 hev hanti hgp hb).2.1
  rw [hw] at hf
  have h4 : (4 : ℤ) ∣ ((GlobalTheory.RefSum.nCol (dat p i) / 2 : ℕ) : ℤ) := by
    obtain ⟨k, hk⟩ := GlobalTheory.RefSum.eight_dvd_nCol (Dw := dat p i)
    exact ⟨k, by rw [hk]; omega⟩
  obtain ⟨f', hne', hv'⟩ := b Z TF la _ _ h4 f hf y T io y' g hg hfac hne
  exact ⟨f', hne', by rw [hv']; exact hv⟩
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
theorem _root_.GlobalTheory.T.jets_constant_section_eq_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f : Cusp Z Y.U la, evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 ∧ (vV T.V (evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂))) : ℝ) ≤ cst * φT := by
  first | exact @_root_.GlobalTheory.JetsCst.jets_of_constant_section_alt | exact _root_.GlobalTheory.JetsCst.jets_of_constant_section_alt | (intros; apply _root_.GlobalTheory.JetsCst.jets_of_constant_section_alt <;> assumption)
end
end
