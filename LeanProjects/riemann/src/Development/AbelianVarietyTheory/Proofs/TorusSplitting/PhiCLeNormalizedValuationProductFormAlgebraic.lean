import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRing
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FiniteExtensionRamificationEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodFormStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.IntegralThetaSectionExistsAndBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PhiCSmulPullStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulPhiLeValuationProductFormStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.LogbNormUniformizerNormalisationStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem phiC_le_normalized_valuation_local_model_base_change (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (O : Type) [CommRing O]
    (β₀ : O →+* c.F) (Y : Model Xo c β₀) (hB : PointsOfFlagModel.BaseAt la β₀) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
    (y : IntFr Xo c T io) (C : SCF (Formalism.MainNotions.WeightAlgebra.resCh la)) (Pc : PointsOfFlagModel.PtC Y C) (hO : OverLa la T.V io e)
    (hAlg : T.FinRes) (eF : T.Fr →+* ↥C.S) (heF : eF.comp io = Pc.fK)
    (hle : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (hlt : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (hy : letI := io.toAlgebra; Pc.y ≫ pullback.fst _ _ = spMap eF ≫ y.1.x)
    (cj : E → E) (hcj : ∀ a, cj a = IsCMField.complexConj E a) :
    ∃ (A : DatAt Y Pc) (bA : Formalism.MainNotions.ModuliIntegralCharts.SymB cj A.Ylat), (∀ a b, (bA : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = A.beta a b) ∧
      ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ)
        (xs : J → Fin n → LatMod Dw (R ^ 4)) (f : Rul Xo c), GlobalTheory.EtaAn.Spans xs → IsEtaRule Xo c R cf xs f →
        ((((Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 *
          (Formalism.BasicNotions.eWL c.F la * Formalism.MainNotions.ModuliIntegralCharts.phiC cj bA) : ℝ)) : EReal) ≤ nval T.V e (evI y f) := by
  letI := io.toAlgebra
  obtain ⟨G, ⟨I⟩⟩ := (GlobalTheory.T.integralThetaSection_exists_and_baseChange E H Dw l Xo c).1 T io y
  obtain ⟨T', φ, G', m, hφi, hφf, -, -, U, hU, hUt⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G I.t' I.m2 y.1.x I.m1 hAlg
  obtain ⟨i, ρ, hρ, hi, hiv, hf⟩ := GlobalTheory.T.exists_injective_intO_embedding_of_norm_lt_one T T' φ hφi hφf
  obtain ⟨f, hfi, hfφ, hfm⟩ := hf _ C eF hle hlt
  obtain ⟨A, e', hA⟩ := GlobalTheory.T.degeneration_data_at_model_point_of_uniformisation E H Dw l Xo c O β₀ Y la hB
    T io e hO y.1.x y.1.s G I y.1.x_over T' φ G' m U hU hUt _ C Pc eF f heF hy hfφ hfm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  obtain ⟨Q, β, hQ, hQ0, -, hβQ, hβ⟩ := GlobalTheory.T.valuationForm_psi_balanced_symmetric_periodForm E H T'.V G' U ϖ hϖ cj hcj
  have hf1 : ∀ a, ‖((intO ↥C.S).subtype.comp f) a‖ ≤ 1 := fun a => (f a).2
  have hfi' : Function.Injective ((intO ↥C.S).subtype.comp f) :=
    (intO ↥C.S).subtype_injective.comp hfi
  have hO' := hO.bc i hρ hiv
  obtain ⟨hun, hew⟩ := GlobalTheory.T.logb_norm_uniformizer_normalisation c.F la T' (i.comp io) (ρ * e) hO' ϖ hϖ C _ hf1
  set t : ℝ := -Real.logb (Formalism.MainNotions.WeightAlgebra.resCh la) ‖((intO ↥C.S).subtype.comp f) ϖ‖ with ht
  have hρe : (0 : ℝ) < ((ρ * e : ℕ) : ℝ) := by exact_mod_cast hO'.1
  have hew' : (0 : ℝ) < (Formalism.BasicNotions.eWL c.F la : ℝ) := by exact_mod_cast hew
  have ht0 : 0 ≤ t := by
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) (mul_pos hρe hew')
    linarith
  obtain ⟨bA, hbA, hφ⟩ := GlobalTheory.T.exists_symB_phiC_eq_mul_of_pullback E cj A.Ylat U.D.toPre.X e' β t ht0
  refine ⟨A, bA, fun a b => ?_, ?_⟩
  · rw [hbA, hA, hβ _ _ _ hfi' hf1]
  intro R hR hR1 J _ n cf xs g hsp hg
  letI : Algebra c.F T'.Fr := (i.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T.Fr T'.Fr ψ y.1
  obtain ⟨I'⟩ := (GlobalTheory.T.integralThetaSection_exists_and_baseChange E H Dw l Xo c).2 T.V T'.V φ ψ y.1 y' G G' m I hi hy'
  have hval := (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c R hR J n cf xs g hg T.Fr y.1 y.2.1).2
    T'.Fr ψ y' hy'
  by_cases h0 : evI y g = 0
  · rw [h0, nval_zero]; exact le_top
  have h0' : i (evI y g) ≠ 0 := (map_ne_zero i).2 h0
  have hpt := GlobalTheory.T.card_mul_phi_le_valuation_productForm E H Dw l Xo c T'.V y' G' I' U ϖ hϖ Q hQ hQ0 cj hcj β hβQ R hR hR1 J n cf xs
    (i (evI y g)) hsp hval h0'
  rw [← nval_bc (V' := T'.V) i hρ hiv e, nval_of_ne h0', EReal.coe_le_coe_iff, le_div_iff₀ hρe, hφ]
  refine le_trans (le_of_eq ?_) hpt
  calc _ = (Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β *
        (t * (((ρ * e : ℕ) : ℝ) * Formalism.BasicNotions.eWL c.F la)) := by ring
    _ = _ := by rw [hun, _root_.mul_one]

theorem phiC_le_nval_of_lies :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (z : PointsOfFlagModel.Pt Tw .yy), OverLa la T.V io e → y.IsAlg → LiesOverBaseChange la Tw T io y z → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∃ (A : DatAt (Tw.Y z.1) z.2.2.1) (bA : Formalism.MainNotions.ModuliIntegralCharts.SymB cj A.Ylat), (∀ a b, (bA : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = A.beta a b) ∧ ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (f : Rul Xo c), GlobalTheory.EtaAn.Spans xs → IsEtaRule Xo c R cf xs f → ((((Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * (Formalism.BasicNotions.eWL c.F la * Formalism.MainNotions.ModuliIntegralCharts.phiC cj bA) : ℝ)) : EReal) ≤ nval T.V e (evI y f) := by
  intro E _ _ _ H Dw l Xo c la Tw hTw T io e y z hO hAlg hL cj hcj
  have hv : z.1.1 = la := congrArg Subtype.val hL.1
  have hB : PointsOfFlagModel.BaseAt la (Tw.β z.1) := by
    have h := (hTw.1 z.1).1
    rwa [hv] at h
  refine hL.2.elim fun eF h => ?_
  exact phiC_le_normalized_valuation_local_model_base_change E H Dw l Xo c la _ (Tw.β z.1) (Tw.Y z.1) hB T io e y z.2.1 z.2.2.1
    hO hAlg eF h.1 h.2.1 h.2.2.1 h.2.2.2.1 cj hcj

end GlobalTheory.EtaVal
