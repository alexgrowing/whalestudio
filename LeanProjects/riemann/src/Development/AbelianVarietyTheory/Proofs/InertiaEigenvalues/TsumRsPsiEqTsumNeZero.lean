import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableInfMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnAbsDetRpowLeOneFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformUniformRapidDecayFamilyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOneStatement

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot Topology GroundTheory.Automorphic.GJMatrix

namespace GlobalTheory.RSThetaLow

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def rsHat (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (g : GA E a) (y : Fin a → Ad E) : ℂ :=
  adelicFourierPi E (rsPsi ℓ φ φ' Φ J η g) y

omit [IsTotallyComplex E] in
variable (E a) in

def lowSet : Set (GA E a) := {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}

omit [IsTotallyComplex E] in
theorem continuous_absDet : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
  continuous_subtype_val.comp (continuous_ideleModule.comp GeneralLinearGroup.continuous_det)

omit [IsTotallyComplex E] in
theorem absDet_invT (g : GA E a) : (ideleModule E (GeneralLinearGroup.det (invT a (Ad E) g)) : ℝ) =
    (ideleModule E (GeneralLinearGroup.det g) : ℝ)⁻¹ := by
  have h : GeneralLinearGroup.det (invT a (Ad E) g) = GeneralLinearGroup.det g⁻¹ := Units.ext (det_transpose _)
  rw [h, map_inv, map_inv]
  rfl

variable {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)

theorem rsPsi_zero (φ φ' : GA E a → ℂ) (hs : tsupport Φ ⊆ rowSet E ℓ) (g : GA E a) : rsPsi ℓ φ φ' Φ J η g 0 = 0 := by
  have h : Φ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h => hs h (Classical.arbitrary _) rfl
  have e : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  simp only [rsPsi, thetaFn, rsInf, e, h, mul_zero, zero_mul]

theorem rsPsi_mem (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    rsPsi ℓ F.1 F'.1 Φ J η g ∈ schwartzBruhatPi E (Fin a) :=
  thetaFn_mem ((isTest_rsInf F F' hΦ g).2.1.toSchwartzMap (isTest_rsInf F F' hΦ g).1) J η

theorem rsHat_eq (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a) (y : Fin a → Ad E) :
    rsHat ℓ F.1 F'.1 Φ J η g y =
      infFourier (rsInf ℓ F.1 F'.1 Φ g) (fun i => pInf E (y i)) * (finiteAdelicChar E (∑ i, η i * pFin E (y i)) : ℂ) *
        (latt a (traceDualIdeal E J)).indicator 1 (fun i => pFin E (y i)) *
        ((finiteMeasurePi E (latt a J)).toReal : ℂ) :=
  adelicFourierPi_thetaFn ((isTest_rsInf F F' hΦ g).2.1.toSchwartzMap (isTest_rsInf F F' hΦ g).1) J η y

theorem stronglyMeasurable_rsHat {F F' : Sm E a} (h : Continuous F.1) (h' : Continuous F'.1)
    (hΦ : IsTest (rowSet E ℓ) Φ) {y : GA E a → Fin a → Ad E} (hy : Continuous y) :
    StronglyMeasurable fun g => rsHat ℓ F.1 F'.1 Φ J η g (y g) := by
  simp only [rsHat_eq J η F F' hΦ]
  have h1 : ∀ i, Continuous fun g => pInf E (y g i) := fun i =>
    continuous_pInf.comp ((continuous_apply i).comp hy)
  have h2 : ∀ i, Continuous fun g => pFin E (y g i) := fun i =>
    (continuous_snd : Continuous (pFin E)).comp ((continuous_apply i).comp hy)
  have h3 : Continuous ((latt a (traceDualIdeal E J)).indicator (1 : (Fin a → Af E) → ℂ)) :=
    (IsClopen.continuous_indicator ⟨isClosed_latt _, isOpen_latt _⟩ continuous_const)
  haveI : SFinite (infMeasure E a) := by unfold infMeasure; infer_instance
  have h4 : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ F.1 F'.1 Φ p.1 p.2 *
      (Real.fourierChar (-∑ i, ∑ w, 2 * (p.2 i w * pInf E (y p.1 i) w).re) : ℂ) := by
    refine (continuous_rsInf h h' hΦ.1.continuous hΦ.2.2).mul (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (Continuous.neg (continuous_finset_sum _ fun i _ =>
        continuous_finset_sum _ fun w _ => continuous_const.mul (Complex.continuous_re.comp (Continuous.mul ?_ ?_))))))
    · fun_prop
    · exact (continuous_apply w).comp ((h1 i).comp continuous_fst)
  refine ((h4.stronglyMeasurable.integral_prod_right'.mul (Continuous.stronglyMeasurable ?_)).mul
    (h3.comp (continuous_pi h2)).stronglyMeasurable).mul stronglyMeasurable_const
  exact continuous_subtype_val.comp (continuous_finiteAdelicChar.comp
    (continuous_finset_sum _ fun i _ => continuous_const.mul (h2 i)))

theorem exists_norm_rsHat_le {ι : Type} {S S' : Submodule ℂ (Sm E a)} {g : ι → GA E a} {w : ι → ℝ}
    (hL : ∀ X, ∀ F ∈ S, lie E a X F ∈ S) (hL' : ∀ X, ∀ F ∈ S', lie E a X F ∈ S')
    (hS : ∀ F ∈ S, ∀ C₀ : Set (GA E a), IsCompact C₀ → ∃ C : ℝ, ∀ i, ∀ c ∈ C₀, ‖F.1 (g i * c)‖ ≤ C * w i)
    (hS' : ∀ F ∈ S', ∃ C : ℝ, ∀ x, ‖F.1 x‖ ≤ C) {F F' : Sm E a} (hF : F ∈ S) (hF' : F' ∈ S')
    (hΦ : IsTest (rowSet E ℓ) Φ) (M : ℕ) : ∃ C : ℝ, ∀ i y,
      ‖rsHat ℓ F.1 F'.1 Φ J η (g i) y‖ * (1 + ‖fun j => pInf E (y j)‖) ^ M ≤ C * w i := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.fourierTransform_uniformRapidDecay_family E a ι w (famSpan ℓ S S' g) (famSpan_bound hS hS')
    (fun f hf => (famSpan_fderiv hL hL' f hf).2) M _ (Submodule.subset_span ⟨F, hF, F', hF', Φ, hΦ, rfl⟩)
  refine ⟨(finiteMeasurePi E (latt a J)).toReal * C, fun i y => ?_⟩
  have h1 := hC i fun j => pInf E (y j)
  have h2 : ‖(latt a (traceDualIdeal E J)).indicator (1 : (Fin a → Af E) → ℂ) fun i => pFin E (y i)‖ ≤ 1 :=
    (norm_indicator_le_norm_self _ _).trans (by simp)
  rw [rsHat_eq J η F F' hΦ, norm_mul, norm_mul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_comm _ (ENNReal.toReal _), mul_assoc, mul_assoc _ C]
  refine mul_le_mul_of_nonneg_left (le_trans ?_ h1) ENNReal.toReal_nonneg
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) h2) (by positivity)

variable {π π' : CuspSub E a} {φ φ' : Sm E a}

theorem exists_norm_rsHat_le_const (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ withSmoothings π)
    (hφ' : φ' ∈ withSmoothings π') (hΦ : IsTest (rowSet E ℓ) Φ) :
    ∃ C : ℝ, ∀ g y, ‖rsHat ℓ φ.1 φ'.1 Φ J η g y‖ ≤ C := by
  obtain ⟨C, h⟩ := exists_norm_rsHat_le J η (g := id) (w := fun _ => 1) (fun X _ => lie_mem_withSmoothings X)
    (fun X _ => lie_mem_withSmoothings X)
    (fun F hF _ _ => (continuous_bounded hπ hF).2.imp fun C h _ _ _ => (h _).trans_eq (mul_one _).symm)
    (fun F hF => (continuous_bounded hπ' hF).2) hφ hφ' hΦ 0
  exact ⟨C, fun g y => by simpa using h g y⟩

theorem exists_tsum_norm_rsHat_le (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ withSmoothings π)
    (hφ' : φ' ∈ withSmoothings π') (hΦ : IsTest (rowSet E ℓ) Φ) (K : ℕ) : ∃ C : ℝ, ∀ g ∈ lowSet E a,
      ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖rsHat ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖ ≤
        C * (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ K := by
  set N := K + Module.finrank ℝ (Fin a → Cinf E) with hN
  have had : 1 ≤ a * Module.finrank ℚ E := Nat.mul_pos ℓ.pos Module.finrank_pos
  obtain ⟨M, C₁, h₁⟩ := GlobalTheory.T.summable_nonzeroRationalVector_le_shortestVector E a (traceDualIdeal E J) (a * Module.finrank ℚ E * N)
    ((Nat.le_add_left _ K).trans (Nat.le_mul_of_pos_left _ had))
  obtain ⟨C₂, h₂⟩ := exists_norm_rsHat_le J η
    (ι := {p : GA E a × (Fin a → E) // p.2 ≠ 0 ∧
      (fun i => pFin E (((fun j => algebraMap E (Ad E) (p.2 j)) ᵥ* p.1.val) i)) ∈ latt a (traceDualIdeal E J)})
    (g := fun p => invT a (Ad E) p.1.1)
    (w := fun p => (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (p.1.2 j)) ᵥ* p.1.1.val) i)‖ ^
      (a * Module.finrank ℚ E) / (ideleModule E (GeneralLinearGroup.det p.1.1) : ℝ)) ^ N)
    (fun X _ => lie_mem_withSmoothings X) (fun X _ => lie_mem_withSmoothings X)
    (fun F hF C₀ hC₀ => (decays_invT hπ hF _ (isCompact_latt _) _ (hC₀.image continuous_invT) N).imp
      fun C h p c hc => by simpa only [map_mul, invT_invT] using h p.1.1 _ ⟨c, hc, rfl⟩ p.1.2 p.2.1 p.2.2)
    (fun F hF => (continuous_bounded hπ' hF).2) hφ hφ' hΦ M
  refine ⟨|C₁| * |C₂|, fun g hg => ?_⟩
  set δ : ℝ := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδ0 : 0 < δ := (ideleModule E _).2
  have h := (h₁ (invT a (Ad E) g) (|C₂| * δ ^ N)
    (fun ξ => rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)) (by positivity)
    (fun ξ hξ => by
      rw [rsHat_eq J η φ φ' hΦ]
      exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (Set.indicator_of_notMem hξ _)) _)
    (fun ξ ξ' h0 hξ' => by
      have h3 := h₂ ⟨(invT a (Ad E) g, ξ'), h0, hξ'⟩ ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)
      simp only [invT_invT, absDet_invT, ← hδ, div_inv_eq_mul, mul_pow, ← pow_mul] at h3
      refine h3.trans ?_
      rw [mul_assoc |C₂|, mul_comm (δ ^ N)]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))).2
  refine h.trans ?_
  rw [mul_assoc]
  refine mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hδ0.le hg (Nat.le_add_right _ _)) (abs_nonneg _)) (by positivity) (abs_nonneg _)

theorem poisson_rsPsi (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    Summable (fun ξ : Fin a → E => ‖rsPsi ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)‖) ∧
    Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} =>
      ‖rsHat ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖) ∧
    ∑' ξ : Fin a → E, rsPsi ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) =
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ)⁻¹ * (rsHat ℓ F.1 F'.1 Φ J η g 0 +
        ∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
          rsHat ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) := by
  obtain ⟨h1, h2, h3⟩ := poisson_vecMul g (rsPsi_mem J η F F' hΦ g)
  refine ⟨h1, h2.subtype _, h3.trans ?_⟩
  rw [Complex.ofReal_inv, ← h2.of_norm.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton 0 fun ξ : Fin a → E =>
    adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)]
  have e : (fun j => algebraMap E (Ad E) ((0 : Fin a → E) j)) = 0 := funext fun _ => map_zero _
  rw [e, zero_vecMul]
  rfl

theorem tsum_rsPsi_eq_tsum_ne_zero (φ φ' : GA E a → ℂ) (hs : tsupport Φ ⊆ rowSet E ℓ) (g : GA E a) :
    ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) =
      ∑' ξ : Fin a → E, rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := by
  refine tsum_subtype_eq_of_support_subset (s := {ξ | ξ ≠ 0})
    (f := fun ξ : Fin a → E => rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) ?_
  rintro ξ hξ rfl
  have e : (fun j => algebraMap E (Ad E) ((0 : Fin a → E) j)) = 0 := funext fun _ => map_zero _
  exact hξ (by simp only [e, zero_vecMul, rsPsi_zero J η φ φ' hs])

def partA (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ lowSet E a, rsHat ℓ φ φ' Φ J η g 0 * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ

def partB (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ lowSet E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
    rsHat ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ

variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}

theorem integrableOn_partA (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ withSmoothings π)
    (hφ' : φ' ∈ withSmoothings π') (hΦ : IsTest (rowSet E ℓ) Φ) (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
    {s : ℂ} (hs : 1 < s.re) : IntegrableOn (fun g => rsHat ℓ φ.1 φ'.1 Φ J η g 0 *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1)) (𝓕 ∩ lowSet E a) μ := by
  obtain ⟨C, hC⟩ := exists_norm_rsHat_le_const J η hπ hπ' hφ hφ' hΦ
  refine ((GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain E a ℓ.pos μ 𝓕 h𝓕 (s.re - 1) (by linarith)).const_mul C).mono'
    ((stronglyMeasurable_rsHat J η (continuous_bounded hπ hφ).1 (continuous_bounded hπ' hφ').1 hΦ
      continuous_const).aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp continuous_absDet.measurable).pow_const _).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.sub_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (hC g 0) (Real.rpow_nonneg (ideleModule E _).2.le _)

theorem partB_entire (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ withSmoothings π)
    (hφ' : φ' ∈ withSmoothings π') (hΦ : IsTest (rowSet E ℓ) Φ) (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) :
    (∀ x : ℝ, IntegrableOn (fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1)) (𝓕 ∩ lowSet E a) μ) ∧
    (∀ s : ℂ, IntegrableOn (fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1)) (𝓕 ∩ lowSet E a) μ) ∧
    Differentiable ℂ (partB ℓ φ.1 φ'.1 Φ J η μ 𝓕) := by
  haveI : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hm : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, AEStronglyMeasurable (fun g : GA E a =>
      rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) (μ.restrict (𝓕 ∩ lowSet E a)) :=
    fun ξ => (stronglyMeasurable_rsHat J η (continuous_bounded hπ hφ).1 (continuous_bounded hπ' hφ').1 hΦ
      (continuous_const.matrix_vecMul Units.continuous_coe_inv.matrix_transpose)).aestronglyMeasurable
  have hlow : ∀ᵐ g ∂μ.restrict (𝓕 ∩ lowSet E a), g ∈ lowSet E a :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right
      (ae_restrict_mem (isClosed_le continuous_absDet continuous_const).measurableSet)
  have hδ := hlow.mono (q := fun g => 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧
    (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) fun g hg => ⟨(ideleModule E _).2, hg⟩
  have hi := GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain E a ℓ.pos μ 𝓕 h𝓕 1 one_pos
  simp only [Real.rpow_one] at hi
  have hb := exists_tsum_norm_rsHat_le J η hπ hπ' hφ hφ' hΦ
  have h1 := GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one _ _ _ _ continuous_absDet.measurable hδ hi (AEStronglyMeasurable.tsum hm) fun K =>
    (hb K).imp fun C h => hlow.mono fun g hg =>
      (norm_tsum_le_tsum_norm (poisson_rsPsi J η φ φ' hΦ g).2.1).trans (h g hg)
  have h2 := GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one _ _ _ _ continuous_absDet.measurable hδ hi
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (AEStronglyMeasurable.tsum fun ξ => (hm ξ).norm)) fun K =>
    (hb K).imp fun C h => hlow.mono fun g hg => by
      rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
      exact h g hg
  refine ⟨fun x => ((h2.1 ((x - 1 : ℝ) : ℂ)).norm).congr (.of_forall fun g => ?_), fun s => h1.1 _,
    h1.2.comp (differentiable_id.sub_const 1)⟩
  simp only [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.ofReal_re]
  rw [Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]

theorem integral_low_eq (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ withSmoothings π)
    (hφ' : φ' ∈ withSmoothings π') (hΦ : IsTest (rowSet E ℓ) Φ) (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun g => (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s) (𝓕 ∩ lowSet E a) μ ∧
    ∫ g in 𝓕 ∩ lowSet E a, (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ =
      partA ℓ φ.1 φ'.1 Φ J η μ 𝓕 s + partB ℓ φ.1 φ'.1 Φ J η μ 𝓕 s := by
  have hA := integrableOn_partA J η hπ hπ' hφ hφ' hΦ h𝓕 hs
  have hB := (partB_entire J η hπ hπ' hφ hφ' hΦ h𝓕).2.1 s
  have e : ∀ g : GA E a, (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s =
      rsHat ℓ φ.1 φ'.1 Φ J η g 0 * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) +
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
        rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) := fun g => by
    rw [(poisson_rsPsi J η φ φ' hΦ g).2.2, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.2 (ideleModule E _).2.ne'),
      Complex.cpow_one]
    ring
  simp only [e]
  exact ⟨hA.add hB, integral_add hA hB⟩

end GlobalTheory.RSThetaLow
