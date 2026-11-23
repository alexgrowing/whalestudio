import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueIntegrable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureIntegralFormula
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotMeasureEqSmul

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

section Abstract

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem meanC_thetaS_of_lintegral (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin n → Fin M → E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (hm : Measurable Φ)
    (hfin : ∫⁻ h in 𝓕, ∑' x : S, ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (x : Fin n → Fin M → E)))‖ₑ ∂μ < ⊤) :
    meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  have ha : ∀ X, Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ X := fun X =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have hsum : ∑' X : S, ∫⁻ h in 𝓕, ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1))‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum (f := fun (X : S) h => ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1))‖ₑ)
      fun X => (hm.enorm.comp (ha _)).aemeasurable]
    exact hfin.ne
  have hint : Integrable Φ (Measure.sum fun X : S =>
      (μ.restrict 𝓕).map fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    change ∫⁻ X, ‖Φ X‖ₑ ∂_ < ⊤
    rw [lintegral_sum_measure]
    simp only [lintegral_map hm.enorm (ha _)]
    exact hsum.lt_top
  rw [thetaMeas, integral_smul_measure, integral_sum_measure hint, meanC, ENNReal.toReal_inv]
  simp only [integral_map (ha _).aemeasurable hm.aestronglyMeasurable]
  exact congrArg _ (integral_tsum (fun X => (hm.comp (ha _)).aestronglyMeasurable) hsum)

end Abstract

end GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

variable {D : D7}

def colsOf {m r : ℕ} (X : Fin r → Fin m → D.host.E) : Matrix (Fin m) (Fin r) D.host.E :=
  Matrix.of fun i a => X a i

theorem gramQ_colsOf (V : HSp D) {r : ℕ} (X : Fin r → Fin V.rank → D.host.E) :
    gramQ V (colsOf X) = HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X := by
  refine Matrix.ext fun a b => ?_
  change ∑ i, D.sp.cm.sig (X a i) * ∑ j, V.gram i j * X b j =
    ∑ i, ∑ j, D.sp.cm.sig (X a i) * V.gram i j * X b j
  simp only [Finset.mul_sum, mul_assoc]

theorem rank_eq_of_gramQ (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E)
    (h : (gramQ V x).det ≠ 0) : x.rank = r := by
  refine le_antisymm (Matrix.rank_le_width x) ?_
  have h1 : (gramQ V x).rank = r := by
    have := Matrix.rank_of_isUnit (gramQ V x) ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h))
    simpa using this
  have h2 : gramQ V x = ((x.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * HSpace.gram V) * x := by
    rw [gramQ, Matrix.mul_assoc]
  calc r = (gramQ V x).rank := h1.symm
    _ ≤ x.rank := by
      rw [h2]
      exact Matrix.rank_mul_le_right _ _

def fibEquiv (V : HSp D) {r : ℕ} (β : HermE D r) (hβ : β.1.det ≠ 0) :
    {X : Fin r → Fin V.rank → D.host.E | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} where
  toFun X := ⟨colsOf X.1, rank_eq_of_gramQ V _ (by rw [gramQ_colsOf, X.2]; exact hβ),
    (gramQ_colsOf V X.1).trans X.2⟩
  invFun x := ⟨fun a i => x.1 i a, (gramQ_colsOf V _).symm.trans x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tupOf_actW (V : HSp D) {r : ℕ} (h : GA D V) (X : Fin r → Fin V.rank → D.host.E) :
    tupOf (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h⁻¹ (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) X)) =
      HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((colsOf X).map (incA D)) := by
  ext i a
  rfl

theorem average_eq_meanC (V : HSp D) (ν μH : Measure (GA D V)) (hν : ν.IsHaarMeasure) (hμ : μH.IsHaarMeasure)
    (𝓕 : Set (GA D V)) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) :
    ⨍ q, descend (GQ V) f q ∂autMeasure V ν = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 f := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  obtain ⟨h0, h1, -⟩ := GlobalTheory.Published.SiegelOneVector.normalise D.sp.cm.sig V.gram (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND V) μH 𝓕 hμ h𝓕
  have e := Measure.isMulLeftInvariant_eq_smul μH ν
  set c := Measure.haarScalarFactor μH ν
  have e1 : autMeasure V μH = (c : ENNReal) • autMeasure V ν := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have e2 : μH 𝓕 = c * autMeasure V ν Set.univ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]
    exact congrArg (fun m : Measure (AutQ V) => m Set.univ) e1
  have hc0 : ((c : ℝ≥0∞)).toReal ≠ 0 := by
    intro h
    have : (c : ℝ≥0∞) = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
      · exact h
      · exact absurd h ENNReal.coe_ne_top
    rw [this, zero_mul] at e2
    exact h0 e2
  have e3 : ∫ g in 𝓕, f g ∂μH = (c : ℝ≥0∞).toReal • ∫ q, descend (GQ V) f q ∂autMeasure V ν := by
    have h3 := GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕 (descend (GQ V) f)
    simp only [hf.descend_mk] at h3
    rw [← h3]
    change ∫ q, descend (GQ V) f q ∂autMeasure V μH = _
    rw [e1, integral_smul_measure]
  rw [average_eq, HeckeCharacterZeroLocus.SiegelWeilU.meanC, e3, e2, ENNReal.toReal_mul, smul_smul, Measure.real,
    mul_inv, mul_comm ((c : ℝ≥0∞).toReal)⁻¹, mul_assoc, inv_mul_cancel₀ hc0, mul_one]

theorem setLIntegral_absTheta_lt_top (V : HSp D) (ν μH : Measure (GA D V)) (hν : ν.IsHaarMeasure)
    (hμ : μH.IsHaarMeasure) (𝓕 : Set (GA D V)) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) {r : ℕ}
    (φ : Mx D V.rank r → ℂ) (habs : GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤) :
    ∫⁻ h in 𝓕, GlobalTheory.SiegelFormula.absTheta V φ h ∂μH < ⊤ := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have e := Measure.isMulLeftInvariant_eq_smul μH ν
  set c := Measure.haarScalarFactor μH ν
  have e1 : autMeasure V μH = (c : ENNReal) • autMeasure V ν := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have hL := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have h3 := GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure h𝓕 (descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ))
  simp only [hL.descend_mk] at h3
  rw [← h3]
  change ∫⁻ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q ∂autMeasure V μH < ⊤
  rw [e1, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top habs

set_option maxHeartbeats 1000000 in

theorem ifrB_eq_thetaPartD : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
    ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
    ∀ (μH : Measure (GA D V)) (𝓕 : Set (GA D V)), μH.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μH →
    ∀ β : HermE D r, β.1.det ≠ 0 → IfrB V ν φ β = thetaPartD V μH 𝓕 φ β := by
  intro D r V θ hθ ν hν φ hφ habs μH 𝓕 hμ h𝓕 β hβ
  have hcm := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable D.host.F
  haveI := lcA
  haveI := scA
  haveI := t2A
  obtain ⟨-, -, sc, -, -, -, -, borelK, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring D.host.F D.host.E D.sp.cm.sig hcm (AF D.host.F)
  haveI := sc
  haveI := borelK r V.rank
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hL := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
    (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hI := average_eq_meanC V ν μH hν hμ 𝓕 h𝓕 _ hL
  let Φ : (Fin r → Fin V.rank → AE D) → ℂ := fun X => φ (tupOf X)
  have hΦc : Continuous Φ := hcont.comp (continuous_matrix fun i a =>
    (continuous_apply i).comp (continuous_apply a))
  have hΦm : Measurable Φ := hΦc.measurable
  let S : Set (Fin r → Fin V.rank → D.host.E) :=
    {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1}
  have hfin : ∫⁻ h in 𝓕, ∑' x : S, ‖Φ (GlobalTheory.CompanionTheory.SW.actW (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig V.gram h⁻¹
      (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) (x : Fin r → Fin V.rank → D.host.E)))‖ₑ ∂μH < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun h => ?_)
      (setLIntegral_absTheta_lt_top V ν μH hν hμ 𝓕 h𝓕 φ habs)
    have hinj : Function.Injective fun X : S => colsOf X.1 := fun X Y e =>
      Subtype.ext (funext fun a => funext fun i => congrFun (congrFun e i) a)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_))
      (ENNReal.tsum_comp_le_tsum_of_injective hinj fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V h ξ)‖ₑ)
    exact congrArg (fun y => ‖φ y‖ₑ) (tupOf_actW V h X.1)
  have hS : HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram Φ S =
      fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V h x.1) := by
    funext h
    refine (tsum_congr fun X => ?_).trans ((fibEquiv V β hβ).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    exact congrArg φ (tupOf_actW V h X.1)
  have key := meanC_thetaS_of_lintegral D.sp.cm.sig hcm V.gram hJ μH 𝓕 S Φ hΦm hfin
  rw [hS] at key
  exact hI.trans key

end GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

end
