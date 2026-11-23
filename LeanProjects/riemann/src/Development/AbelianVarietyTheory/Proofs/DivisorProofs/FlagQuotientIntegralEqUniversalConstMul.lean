import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDiscreteArithGroupImageRealUnitary
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarIntegralEqUnitriangularChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTransportHermitianFrameRealUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTransportHermitianFrameChartMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBorelInvariantTestFunctionFrameChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainSaturatedFundamentalSetFramesStatement

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem haarChart_exists (X : Data E r) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ HaarChart X c := GlobalTheory.T.exists_haarIntegral_eq_unitriangularChart X

theorem haar_trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (hp : X.p0 = X'.p0) (φ : Frame X'.Ψ r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ (trF X X' e (frameOf X g)) ∂haarR X = ∫⁻ g, φ (frameOf X' g) ∂haarR X' := GlobalTheory.T.lintegral_transportHermitianFrame_realUnitary X X' e hp φ hφ

theorem muF_trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (hp : X.p0 = X'.p0) (φ : Frame X'.Ψ r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ z, φ (trF X X' e (cpt X (baseFr X) z)) ∂muF X (baseFr X) =
      ∫⁻ z, φ (cpt X' (baseFr X') z) ∂muF X' (baseFr X') := GlobalTheory.T.lintegral_transportHermitianFrame_chartMeasure X X' e hp φ hφ

theorem test_exists (X : Data E r) : ∃ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ ∧
    (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧
    ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ 0 ∧ ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ ⊤ :=
  GlobalTheory.T.exists_borelInvariant_testFunction_frameChart X

theorem isFundamentalDomain_sat (X : Data E r) {c : ℝ≥0∞} (hc : HaarChart X c) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) (Λ : Subgroup (RealGrp X))
    (hΛ : ∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) :
    IsFundamentalDomain Λ (frameOf X ⁻¹' GlobalTheory.Unfold.satFrames X x0 FF) (haarR X) := GlobalTheory.T.isFundamentalDomain_saturated_fundamentalSet_frames X hc ho hF Λ hΛ

theorem trF_rmul {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (y b : Frame X.Ψ r) :
    trF X X' e (rmul y b) = rmul (trF X X' e y) (fun τ' => b (e.symm τ')) := by
  funext τ'
  show (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * (mat y (e.symm τ') * mat b (e.symm τ')) :
      Matrix (Fin r) (Fin r) ℂ) =
    mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat y (e.symm τ') * mat b (e.symm τ')
  simp only [Matrix.mul_assoc]

theorem continuous_trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) : Continuous (trF X X' e) := by
  refine continuous_pi fun τ' => ?_
  have hM : Continuous fun y : Frame X.Ψ r => mat y (e.symm τ') := continuous_apply _
  exact continuous_const.matrix_mul hM

theorem trF_mem_dom {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (hp : X.p0 = X'.p0) {y : Frame X.Ψ r} (hy : y ∈ X.dom) : trF X X' e y ∈ X'.dom := by
  intro τ'
  set τ := e.symm τ'
  have hb := GlobalTheory.PeterssonCompare.det_baseFr X τ
  have hb' := GlobalTheory.PeterssonCompare.det_baseFr X' τ'
  set M : Matrix (Fin r) (Fin r) ℂ := (mat (baseFr X) τ)⁻¹ * mat y τ
  have hy' : mat y τ = mat (baseFr X) τ * M := (Matrix.mul_nonsing_inv_cancel_left _ _ hb.isUnit).symm
  have ht : mat (trF X X' e y) τ' = mat (baseFr X') τ' * M := by
    show mat (baseFr X') τ' * (mat (baseFr X) τ)⁻¹ * mat y τ = mat (baseFr X') τ' * ((mat (baseFr X) τ)⁻¹ * mat y τ)
    rw [Matrix.mul_assoc]
  have hg : gram τ'.1 X'.Gm (mat (trF X X' e y) τ') = gram τ.1 X.Gm (mat y τ) := by
    rw [ht, hy', FrameDegreeData.gram_mul, FrameDegreeData.gram_mul, baseFr_mem X τ, baseFr_mem X' τ', hp]
  refine ⟨?_, fun i => ?_⟩
  · rw [ht, Matrix.det_mul]
    refine mul_ne_zero hb' ?_
    intro h0
    apply (hy τ).1
    rw [hy', Matrix.det_mul, h0, mul_zero]
  · have := (hy τ).2 i
    unfold dmin at this ⊢
    rw [hg, ← hp]
    exact this

theorem haarChart_unique {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (hp : X.p0 = X'.p0) (hn : X.Ψ.card = X'.Ψ.card) {c c' : ℝ≥0∞} (hc : HaarChart X c) (hc' : HaarChart X' c') :
    c = c' := by
  have e : X.Ψ ≃ X'.Ψ := Fintype.equivOfCardEq (by simpa using hn)
  obtain ⟨φ, hφm, hφB, h0, htop⟩ := test_exists X'
  have hm : Measurable (fun y => φ (trF X X' e y)) := hφm.comp (continuous_trF X X' e).measurable
  have hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (trF X X' e (rmul x b)) = φ (trF X X' e x) := by
    intro x hx b hb
    rw [trF_rmul]
    exact hφB _ (trF_mem_dom X X' e hp hx) _ fun τ' => hb (e.symm τ')
  have h1 := hc _ hm hB
  rw [haar_trF X X' e hp φ hφm, hc' φ hφm hφB, muF_trF X X' e hp φ hφm] at h1
  exact ((ENNReal.mul_left_inj h0 htop).1 h1).symm

theorem countable_image (X : Data E r) {Λ : Subgroup (RealGrp X)}
    (hΛ : ∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) : Countable Λ := by
  haveI := FundSetPf.countable_GL (E := E) (r := r)
  choose f hf using fun s : Λ => (hΛ s.1).1 s.2
  refine Function.Injective.countable (f := f) fun s t h => Subtype.ext ?_
  apply GlobalTheory.PeterssonCompare.frameOf_injective X
  rw [← (hf s).2, ← (hf t).2, h]

theorem quotInt_eq_of_haarChart (X : Data E r) {c : ℝ≥0∞} (hc : HaarChart X c) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) {Φ : Frame X.Ψ r → ℝ≥0∞}
    (hΦ : Measurable Φ) (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x)
    (hB : ∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) :
    quotInt X Φ = c * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  classical
  obtain ⟨Λ, hΛ, -⟩ := GlobalTheory.ArithImage.exists_discrete_image E r X
  haveI := countable_image X hΛ
  set S := GlobalTheory.Unfold.satFrames X x0 FF
  have hS : MeasurableSet S := GlobalTheory.Unfold.measurableSet_satFrames X ho hF.1 hF.2.1
  rw [GlobalTheory.PeterssonCompare.quotInt_eq X hΛ (isFundamentalDomain_sat X hc ho hF Λ hΛ) hΓ]
  have hpre : MeasurableSet (frameOf X ⁻¹' S) := GlobalTheory.PeterssonCompare.measurable_frameOf X hS
  rw [← lintegral_indicator hpre]
  have e1 : (frameOf X ⁻¹' S).indicator (fun g => Φ (frameOf X g)) = fun g => S.indicator Φ (frameOf X g) := by
    funext g; by_cases h : frameOf X g ∈ S <;> simp [h]
  have hIB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, S.indicator Φ (rmul x b) = S.indicator Φ x := by
    intro x hx b hb
    rw [Set.indicator_apply, Set.indicator_apply, GlobalTheory.Unfold.rmul_mem_satFrames_iff X x0 FF x hb, hB b hb x hx]
  have hbo : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
  rw [e1, hc _ (hΦ.indicator hS) hIB,
    GlobalTheory.FrameMeasureClosed.measInv_holds r X (baseFr X) x0 hbo ho _ (hΦ.indicator hS) hIB,
    ← lintegral_indicator hF.1]
  congr 1
  refine lintegral_congr fun z => ?_
  rw [Set.indicator_apply, Set.indicator_apply, GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho]

end

end GlobalTheory.FlagQuotHaar

open GlobalTheory.FlagQuotHaar in
theorem GlobalTheory.FlagQuotHaar.quotInt_eq_const_mul : ∀ (r p0 n : ℕ), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : Data E r), X.p0 = p0 → X.Ψ.card = n → ∀ (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (Φ : Frame X.Ψ r → ℝ≥0∞), IsOrth X x0 → IsFundSet X x0 FF → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt X Φ = κ * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  intro r p0 n
  by_cases h : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (X : Data E r),
      X.p0 = p0 ∧ X.Ψ.card = n
  · obtain ⟨E₁, _, _, _, X₁, hp₁, hn₁⟩ := h
    obtain ⟨c₁, h0, htop, hc₁⟩ := haarChart_exists X₁
    refine ⟨c₁, h0, htop, fun E _ _ _ X hp hn x0 FF Φ ho hF hΦ hΓ hB => ?_⟩
    obtain ⟨c, -, -, hc⟩ := haarChart_exists X
    rw [quotInt_eq_of_haarChart X hc ho hF hΦ hΓ hB,
      haarChart_unique X X₁ (hp.trans hp₁.symm) (hn.trans hn₁.symm) hc hc₁]
  · refine ⟨1, one_ne_zero, ENNReal.one_ne_top, fun E _ _ _ X hp hn => ?_⟩
    exact absurd ⟨E, inferInstance, inferInstance, inferInstance, X, hp, hn⟩ h
