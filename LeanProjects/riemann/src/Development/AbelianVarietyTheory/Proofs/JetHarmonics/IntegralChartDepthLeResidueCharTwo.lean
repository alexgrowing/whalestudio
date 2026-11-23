import Mathlib
import Development.AutomorphicArithmetic.CMTraceForms.Places
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr
import Development.AutomorphicArithmetic.CMTraceForms.CmDatumSplitPlacesConjStable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartColengthBoundPrimeTwoStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartDepthLeOfCharacterFlagsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeDirectionsEigenbasisValuedIntegersStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyClosedValuedExtensionOfCDVRStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFlagCharactersLeadingMinorsColengthStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersLeadingMinorsGeHodgeTateStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HodgeTateInclusionIntegralChartStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRingStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem sum_log_div_log_le_of_rpow_le_prod {ι : Type} (S : Finset ι) (x : ι → ℝ) (r B : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (hx : ∀ i ∈ S, x i ≠ 0) (h : r ^ B ≤ ∏ i ∈ S, x i) :
    ∑ i ∈ S, Real.log (x i) / Real.log r ≤ B := by
  have hl : Real.log r < 0 := Real.log_neg hr0 hr1
  have h1 := Real.log_le_log (Real.rpow_pos_of_pos hr0 B) h
  rw [Real.log_rpow hr0, Real.log_prod hx] at h1
  rw [← Finset.sum_div, div_le_iff_of_neg hl]
  exact h1

theorem nuLocC_le_over_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), y.IsAlg → ¬ IsUnit ((p : ℕ) : T.V) → UpperTheory.Depth.SplitAt H.d p → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuLocC Ch e k a n ≤ (((vV T.V ((p : ℕ) : T.Fr) : ℝ) / (e : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  intro p _ hAv hHT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch hy h2 hsp f vd hvd htp e k n a he hdom hn Ap hAp haA
  classical
  obtain ⟨X⟩ := GlobalTheory.T.nonempty_closedValuedExtensionOfCDVR T p h2
  obtain ⟨τT, -, hty, -⟩ := GlobalTheory.T.exists_cmType_embeddings_into_valuation_ring E H l c T io p X
  obtain ⟨hw0, happ⟩ := UpperTheory.cmDatum_splitPlaces_conj_stable p Fact.out E H hsp X.C X.v X.O X.ints X.nonunit.out
  obtain ⟨xs, hxs, hprod⟩ := GlobalTheory.T.integralChart_colength_bound_prime_two p hAv E H Dw l Xo c T io y Ch X hy f vd htp
  obtain ⟨N, u, hu, hspan⟩ := GlobalTheory.T.hodgeTate_inclusion_integralChart p hHT E H Dw l Xo c T io y Ch X hy
  have h2C : algebraMap X.O X.C ((p : ℕ) : X.O) = ((p : ℕ) : X.C) := map_natCast _ _
  have h2C0 : ((p : ℕ) : X.C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h2O0 : ((p : ℕ) : X.O) ≠ 0 := fun h => h2C0 (by rw [← h2C, h, map_zero])
  have hr0 : (0 : ℝ) < (X.v ((p : ℕ) : X.C) : ℝ) := by
    have : X.v ((p : ℕ) : X.C) ≠ 0 := (Valuation.ne_zero_iff _).2 h2C0
    exact_mod_cast pos_iff_ne_zero.2 this
  have hr1 : (X.v ((p : ℕ) : X.C) : ℝ) < 1 := by
    have hle : X.v ((p : ℕ) : X.C) ≤ 1 := by rw [← h2C]; exact X.ints.map_le_one _
    have hne : X.v ((p : ℕ) : X.C) ≠ 1 := fun h =>
      X.nonunit.out (X.ints.isUnit_iff_valuation_eq_one.2 (by rw [h2C]; exact h))
    exact_mod_cast lt_of_le_of_ne hle hne
  set r : ℝ := (X.v ((p : ℕ) : X.C) : ℝ) with hr
  have hlog : Real.log r < 0 := Real.log_neg hr0 hr1
  have hxs0 : ∀ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.1 (lt_of_lt_of_le (Real.rpow_pos_of_pos hr0 _) hprod).ne'
  have hxs0' : ∀ τ, InPsi H τ → xs τ ≠ 0 := fun τ hτ h =>
    hxs0 τ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hτ⟩) (by rw [h]; rfl)
  let len : (E →+* ℂ) → ℝ := fun τ => if InPsi H τ then Real.log (xs τ) / Real.log r else (Dw.q : ℝ)
  have hlen0 : ∀ τ, 0 ≤ len τ := by
    intro τ
    by_cases hτ : InPsi H τ
    · simp only [len, if_pos hτ]
      have h1 := (GlobalTheory.T.exists_flag_characters_leading_minors_colength X.C X.v X.O X.ints _ _ _ _ _ (hxs τ hτ) (hxs0' τ hτ)).1
      exact div_nonneg_of_nonpos (Real.log_nonpos (xs τ).2 (by exact_mod_cast h1)) hlog.le
    · simp only [len, if_neg hτ]
      exact Nat.cast_nonneg _
  have key := GlobalTheory.T.chartDepth_le_of_characterFlags E H Dw l Xo c T io y Ch p X _ hty (fun τ => ⟨H.w0, hw0 _⟩)
    (fun x hx => by
      obtain ⟨M, hM, hM'⟩ := happ x hx
      exact ⟨M, hM, fun τ => hM' _⟩) e k n a he hdom hn len hlen0 (by
      intro τ
      by_cases hτ : InPsi H τ
      · obtain ⟨-, χ, hχ, hχ'⟩ := GlobalTheory.T.exists_flag_characters_leading_minors_colength X.C X.v X.O X.ints _ _ _ _ _ (hxs τ hτ) (hxs0' τ hτ)
        refine ⟨χ, hχ, fun i => ?_⟩
        have hpos : (0 : ℝ) < xs τ := by exact_mod_cast pos_iff_ne_zero.2 (hxs0' τ hτ)
        have : r ^ len τ = xs τ := by
          simp only [len, if_pos hτ]
          rw [Real.rpow_def_of_pos hr0, mul_div_cancel₀ _ hlog.ne, Real.exp_log hpos]
        rw [← hr, this]
        exact_mod_cast hχ' i
      · obtain ⟨χ, hχ, hχ'⟩ := GlobalTheory.T.exists_characters_leading_minors_valuation_ge X.C X.v X.O X.ints _ _ N _ _
          (GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers E H Dw l Xo c T io y Ch p X _ hty τ).2 u hu ((p : ℕ) : X.O) h2O0
          (hspan _ (by
            rw [h2C]
            have hle : X.v ((p : ℕ) : X.C) ≤ 1 := by exact_mod_cast hr1.le
            exact pow_le_of_le_one zero_le hle (by have := (Fact.out : p.Prime).two_le; omega)))
        refine ⟨χ, hχ, fun i => ?_⟩
        have hm : Dw.mult τ = Dw.q := if_neg hτ
        have : r ^ len τ = ((X.v (algebraMap X.O X.C ((p : ℕ) : X.O)) ^ Dw.mult τ : NNReal) : ℝ) := by
          simp only [len, if_neg hτ]
          rw [Real.rpow_natCast, h2C, hm, NNReal.coe_pow]
        rw [← hr, this]
        exact_mod_cast hχ' i)
  refine key.trans (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left ?_ ?_))
  · rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ => InPsi H τ)]
    refine add_le_add ?_ (le_of_eq ?_)
    · have hsum := sum_log_div_log_le_of_rpow_le_prod _ (fun τ => (xs τ : ℝ)) r _ hr0 hr1 hxs0 hprod
      refine le_trans ?_ (mul_le_mul_of_nonneg_right hsum hAp)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun τ hτ => ?_
      have hτ' : InPsi H τ := (Finset.mem_filter.1 hτ).2
      have h0 := hlen0 τ
      simp only [len, if_pos hτ'] at h0 ⊢
      exact mul_le_mul_of_nonneg_left (haA τ hτ') h0
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      have hτ' : ¬ InPsi H τ := (Finset.mem_filter.1 hτ).2
      simp only [len, if_neg hτ']
  · have h0 := GlobalTheory.vV_algebraMap_nonneg_dvr T ((p : ℕ) : T.V)
    rw [map_natCast] at h0
    exact div_nonneg (by exact_mod_cast h0) (Nat.cast_nonneg _)

end GlobalTheory.CharDepth
