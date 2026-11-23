import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsNonzeroSectionWeightBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentredPointPhiPositive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN

set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaSteep
section Tau
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open GlobalTheory.ThetaConst
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
end Tau
section Key
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal GlobalTheory.ShFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Key
section Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.HSApp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
end Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 2000000 in
theorem exists_theta_section_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))) ⊤, θ ≠ 0 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ f ∈ space TF.X Z Y.U (la - ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))), ((common₀ TF.X Z).addChart (add_sub_cancel ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i)) la)).mul θ f ∈ space TF.X Z Y.U la) ∧ ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ (j : (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).ι) (hj : y ∈ (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).U j) (m : ℤ), ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → 8 * φ / 625 ≤ (m : ℝ) := by
  intro h1 h2 h3 h4
  refine (((_root_.GlobalTheory.T.exists_phi_pos_of_centred_off_U0 h1 h2 h3 h4).and h4).and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C, hC, x0, hx0⟩, ⟨C₁, -, x1, hx1⟩⟩, ⟨C₂, -, x2, hx2⟩⟩ := h
  refine ⟨C, hC, max x0 (max x1 x2), fun x hx hle ι p hp i hi Y hY Z TF => ?_⟩
  have l0 : x0 ≤ x := (le_max_left _ _).trans hle
  have l1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have l2 : x2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  have hdeg := hx0 x hx l0 ι p hp i hi Y hY Z TF
  have hfl := hx1 x hx l1 ι p hp i hi Y hY
  have hnum := hx2 x hx l2 ι p hp i
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  have hM : 5 ^ 4 ∣ Y.d.l₂.M := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    exact Dvd.dvd.mul_left ((pow_dvd_pow_of_dvd (by norm_num) 4).trans (pow_dvd_pow 15 (four_le_expL hnum.big.2.1))) _
  have hf : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by
    have := hnum.f8
    have := hnum.deg
    omega
  obtain ⟨θ, hθ, hb⟩ := _root_.GlobalTheory.ThetaSteep.exists_section_of_theta_datum Z h1 hL hM TF (fun τ => (hfl Z τ).1.some) hdeg
  exact ⟨θ, hθ, fun la _ f hf' => vanBd_le_space _ _ _ Y _ _ hY.1 hf Z TF la
    (mul_mem_vanBd TF.X Z _ θ ((GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY.1 hf Z TF _).space_le hf')),
    fun y _ ν hν φ hφ j hj m hm => hb y ν hν φ hφ j hj m hm⟩
end GlobalTheory.ThetaSteep
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
theorem _root_.GlobalTheory.T.exists_nonzero_section_weight_bound_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))) ⊤, θ ≠ 0 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ f ∈ space TF.X Z Y.U (la - ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))), ((common₀ TF.X Z).addChart (add_sub_cancel ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i)) la)).mul θ f ∈ space TF.X Z Y.U la) ∧ ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ (j : (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).ι) (hj : y ∈ (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).U j) (m : ℤ), ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → 8 * φ / 625 ≤ (m : ℝ) := by
  first | exact @_root_.GlobalTheory.ThetaSteep.exists_theta_section_alt_alt | exact _root_.GlobalTheory.ThetaSteep.exists_theta_section_alt_alt | (intros; apply _root_.GlobalTheory.ThetaSteep.exists_theta_section_alt_alt <;> assumption)
end
end
