import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicProbabilityEqNormalisedFundamentalSets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSet
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.BergLower

open MeasureTheory ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem le_div_of_mean {β a I v S m J N : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hS0 : S ≠ 0) (hv : v ≠ ⊤)
    (hI : v = 0 → I = 0) (hβ : β * I ≤ a * v) (hJ : J * S = I) (hm : v ≤ m * S) (hN : N ≤ m⁻¹ * J) :
    β ≤ a / N := by
  rw [ENNReal.le_div_iff_mul_le (Or.inr ha0) (Or.inr hat)]
  by_cases h0 : v = 0
  · have hJ0 : J = 0 := by
      rw [hI h0] at hJ
      exact (mul_eq_zero.1 hJ).resolve_right hS0
    rw [hJ0, mul_zero, nonpos_iff_eq_zero] at hN
    simp [hN]
  · have h1 : N * v ≤ I := by
      calc N * v ≤ (m⁻¹ * J) * (m * S) := by gcongr
        _ = (m⁻¹ * m) * (J * S) := by ring
        _ ≤ 1 * I := by
          rw [hJ]
          gcongr
          exact ENNReal.inv_mul_le_one m
        _ = I := one_mul _
    have h2 : β * N * v ≤ a * v := by
      rw [mul_assoc]
      exact le_trans (by gcongr) hβ
    exact (ENNReal.mul_le_mul_iff_left h0 hv).1 h2

theorem pnorm_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  unfold Data.pnorm
  exact mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _)

theorem le_bergOn : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ D.R.r) ∈ framesOn (U σ) Z → ∀ β : ENNReal, (∀ (x0 : Frame ((U σ).X y.1).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((U σ).X y.1)))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U σ).X y.1) x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet ((U σ).X y.1) x0 FF → ∃ P ∈ ((U σ).X y.1).SS (modelWt (U σ) G y.1), P y.2.1 ≠ 0 ∧ β * ∫⁻ z in FF, ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X y.1) x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0) ≤ ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P y.2.1 ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0 FF) → β ≤ bergOn (U σ) (D.sp.W j) (dict σ) Z G y := by
  intro D j H Dw l Xo c U dict hL σ hσ G Z y hy β hβ
  classical
  have hU : IsUnf (U σ) := hL.unf σ hσ
  obtain ⟨Kf, th, hr, -, -, hDU, -⟩ := hL.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := Formalism.L2.Pj.dict_dom_of hDU
  have hex : ∀ (X : Data D.host.E D.R.r), ∃ x0, IsOrth X x0 ∧ ∃ FF, IsFundSet X x0 FF := fun X => by
    choose P _ hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ, GlobalTheory.MetricWeightTest.exists_fundSet_orth X (fun τ => hG τ)⟩
  choose x0 hx0 FF hFF using fun k => hex ((U σ).X k)
  obtain ⟨P, hP, hPy, hle⟩ := hβ (x0 y.1) (FF y.1) (hx0 _) (hFF _)
  set la := modelWt (U σ) G with hla
  obtain ⟨hS0, hST, hI⟩ := GlobalTheory.LevGeo.adelicProb_mul_volFund D j H Dw l Xo c U dict hL σ hσ x0 FF
    (fun k => ⟨hx0 k, hFF k⟩)
  set Q : Frame ((U σ).X y.1).Ψ D.R.r → ℂ := ((U σ).X y.1).dom.indicator P with hQ
  have hQP : ∀ x ∈ ((U σ).X y.1).dom, ((U σ).X y.1).pnorm (la y.1) Q x = ((U σ).X y.1).pnorm (la y.1) P x :=
    fun x hx => by unfold Data.pnorm; rw [hQ, Set.indicator_of_mem hx]
  have hQS : Q ∈ ((U σ).X y.1).SS (la y.1) :=
    (GlobalTheory.DomCongr.bddSec_cusp_congr D.host.E D.R.r _ _ P Q (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hP
  set P' : Formalism.L2.Pj.FDSec (U σ).X := Function.update (fun _ => 0) y.1 Q with hP'
  have hP'y : P' y.1 = Q := Function.update_self _ _ _
  have hP'n : ∀ k, k ≠ y.1 → P' k = 0 := fun k hk => Function.update_of_ne hk _ _
  have hP'S : ∀ k, P' k ∈ ((U σ).X k).SS (la k) := fun k => by
    by_cases hk : k = y.1
    · subst hk; rw [hP'y]; exact hQS
    · rw [hP'n k hk]
      exact (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds (E := D.host.E) D.R.r ((U σ).X k) (la k) (la k) 0).1.1
  have hP'0 : ∀ k, ∀ x ∉ ((U σ).X k).dom, P' k x = 0 := fun k x hx => by
    by_cases hk : k = y.1
    · subst hk; rw [hP'y]; exact Set.indicator_of_notMem hx _
    · rw [hP'n k hk]; rfl
  have hP'm : P' ∈ Formalism.L2.Pj.holSub (U σ).X la := Formalism.L2.Pj.holCusp_mem_holSub _ _ hP'S
  have hsf : ∀ k, ((U σ).X k).IsSec (la k) (P' k) := fun k => (hP'S k).1.1
  have hJ := hI (fun k x => ENNReal.ofReal (((U σ).X k).pnorm (la k) (P' k) x ^ 2))
    (fun k => ENNReal.measurable_ofReal.comp ((GlobalTheory.PeterssonCompare.measurable_pnorm _ _
      (hsf k).1.continuousOn (hP'0 k)).pow_const 2))
    (fun k γ hγ x hx => by simp only [GlobalTheory.PeterssonCompare.pnorm_lact _ (hsf k) hγ hx])
    (fun k b hb x hx => by simp only [FrameDegreeData.pnorm_rmul _ _ _ (hsf k).2.1 x hx b hb])
  rw [Finset.sum_eq_single y.1 (f := fun k => ∫⁻ z in FF k, ENNReal.ofReal (((U σ).X k).pnorm (la k) (P' k)
      (cpt ((U σ).X k) (x0 k) z) ^ 2) ∂(muF ((U σ).X k) (x0 k)))
      (fun k _ hk => by simp [hP'n k hk, Formalism.L2.Pj.pnorm_zero])
    (fun h => absurd (Finset.mem_univ _) h), hP'y,
    setLIntegral_congr_fun (hFF y.1).1 (g := fun z => ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) P
      (cpt ((U σ).X y.1) (x0 y.1) z) ^ 2)) (fun z hz => by simp only [hQP _ ((hFF y.1).2.1 hz)])] at hJ
  have hM := hI (fun k _ => if k = y.1 then 1 else 0) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
  rw [Finset.sum_eq_single y.1 (f := fun k => ∫⁻ z in FF k, (if k = y.1 then (1 : ℝ≥0∞) else 0)
      ∂(muF ((U σ).X k) (x0 k))) (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl, setLIntegral_one] at hM
  set Cl := classesOver (D.sp.W j) (dict σ) (framesOn (U σ) Z) with hCl
  have hm : ∫⁻ q : AutQ (D.sp.W j), (if (dict σ q.out).1 = y.1 then (1 : ℝ≥0∞) else 0) ∂(muQ1 (D.sp.W j)) ≤
      muQ1 (D.sp.W j) Cl := by
    refine le_trans (lintegral_mono fun q => ?_) (lintegral_indicator_one_le Cl)
    split_ifs with hq
    · have : q ∈ Cl := by
        have h1 := hdom q.out
        show dict σ q.out ∈ framesOn (U σ) Z
        generalize dict σ q.out = z at hq h1
        obtain ⟨k, x⟩ := z
        obtain rfl : k = y.1 := hq
        exact GlobalTheory.FramesUnion.framesOn_of_mem D.host.E H Dw l Xo c D.R.r U σ hU Z _ _ x h1 hy
      simp [this]
    · exact zero_le
  have hN : petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P' ^ 2 ≤ (muQ1 (D.sp.W j) Cl)⁻¹ *
      ∫⁻ q : AutQ (D.sp.W j), ENNReal.ofReal (((U σ).X (dict σ q.out).1).pnorm (la (dict σ q.out).1)
        (P' (dict σ q.out).1) (dict σ q.out).2 ^ 2) ∂(muQ1 (D.sp.W j)) := by
    have e : petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P' ^ 2 =
        ∫⁻ q : AutQ (D.sp.W j), ‖ptN la P' (dict σ q.out)‖ₑ ^ 2 ∂(muOn (U σ) (D.sp.W j) (dict σ) Z) := by
      have := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (μ := muOn (U σ) (D.sp.W j) (dict σ) Z)
        (f := fun q : AutQ (D.sp.W j) => ptN la P' (dict σ q.out)) two_ne_zero
      simpa [petE] using this
    rw [e]
    show ∫⁻ q, _ ∂((muQ1 (D.sp.W j) Cl)⁻¹ • (muQ1 (D.sp.W j)).restrict Cl) ≤ _
    rw [lintegral_smul_measure, smul_eq_mul]
    refine mul_le_mul_right
      (le_trans (lintegral_mono' Measure.restrict_le_self le_rfl) (le_of_eq (lintegral_congr fun q => ?_))) _
    rw [Real.enorm_eq_ofReal (ptN_nonneg _ _ _), ← ENNReal.ofReal_pow (ptN_nonneg _ _ _)]
    rfl
  have hpos := pnorm_pos ((U σ).X y.1) (la y.1) y.2.2 hPy
  have hpt : ENNReal.ofReal (ptN la P' ⟨y.1, y.2.1⟩) ^ 2 =
      ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) P y.2.1 ^ 2) := by
    rw [ENNReal.ofReal_pow hpos.le]
    show ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) (P' y.1) y.2.1) ^ 2 = _
    rw [hP'y, hQP _ y.2.2]
  refine le_trans ?_ (le_iSup₂_of_le (f := fun P (_ : P ∈ Formalism.L2.Pj.holSub (U σ).X la) =>
    ENNReal.ofReal (ptN la P ⟨y.1, y.2.1⟩) ^ 2 /
      petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P ^ 2) P' hP'm le_rfl)
  rw [hpt]
  refine le_div_of_mean (ENNReal.ofReal_pos.2 (pow_pos hpos 2)).ne' ENNReal.ofReal_ne_top hS0
    (ne_top_of_le_ne_top hST (Finset.single_le_sum (f := fun k => muF ((U σ).X k) (x0 k) (FF k))
      (fun _ _ => zero_le) (Finset.mem_univ y.1)))
    (fun h => setLIntegral_measure_zero _ _ h) hle hJ ?_ hN
  rw [← hM]
  gcongr

end GlobalTheory.BergLower
