import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace WeightCoefficients

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

def HS (m : ℕ) : Set (GA E k) := {h | ∃ γ u, IsMir m γ ∧ UU (m + 1) u ∧ h = ratGL E k γ * u}

def rhoB (m : ℕ) : Measure (GA E k) :=
  Measure.map (fun x : UnipotentBlockColumnIndex k m m → Ad E => (blkU x : GA E k))
    ((vecMeasure E (UnipotentBlockColumnIndex k m m)).restrict (vecDomain E (UnipotentBlockColumnIndex k m m)))

def rhoA (m : ℕ) : Measure (GA E k) := Measure.sum fun ξ : RowT E k m => Measure.dirac (ratGL E k (gam ξ))

def bA (m : ℕ) (β : GA E k → ℝ≥0∞) (g : GA E k) : ℝ≥0∞ := ∑' ξ : RowT E k m, β ((ratGL E k (gam ξ))⁻¹ * g)

theorem meas_blkU (m : ℕ) : Measurable (fun x : UnipotentBlockColumnIndex k m m → Ad E => (blkU x : GA E k)) :=
  (continuous_posU (isNil_blk k m m)).measurable

theorem measI {ν : Measure (GA E k)} [SFinite ν] {β : GA E k → ℝ≥0∞} (hβ : Measurable β) (g : GA E k) :
    Measurable fun r : GA E k => ∫⁻ h, β (r⁻¹ * h * g) ∂ν :=
  (hβ.comp (((measurable_fst.inv).mul measurable_snd).mul_const g)).lintegral_prod_right'

theorem wtB (hN3 : N3) (hN4b : OneMoreAdelicColumn) {m : ℕ} (hmk : m < k) {β : GA E k → ℝ≥0∞} (hβ : IsWt (nuP E k m) β)
    (g : GA E k) : ∫⁻ h, β (h * g) ∂nuB E k m = 1 := by
  have hB := (hN3 E k).2.1 m hmk.le
  have hP := (hN3 E k).1 m hmk
  haveI := hP.1
  have hinvB : ∫⁻ h, β (h * g) ∂nuB E k m = ∫⁻ h, β (h⁻¹ * g) ∂nuB E k m := by
    conv_lhs => rw [← hB.2.1]
    exact lintegral_map (f := fun h => β (h * g)) (hβ.1.comp (measurable_mul_const g)) measurable_inv
  rw [hinvB, hN4b E k m hmk (fun h => β (h⁻¹ * g)) (hβ.1.comp (measurable_inv.mul_const g))]
  have : ∀ x : UnipotentBlockColumnIndex k m m → Ad E, ∫⁻ h, β (((blkU x : GA E k)⁻¹ * h)⁻¹ * g) ∂nuP E k m = 1 := by
    intro x
    have e : ∀ h : GA E k, ((blkU x : GA E k)⁻¹ * h)⁻¹ * g = h⁻¹ * (blkU x * g) := by intro h; group
    simp_rw [e]
    conv_lhs => rw [← hP.2.1]
    refine (lintegral_map (μ := nuP E k m) (f := fun h => β (h⁻¹ * (blkU x * g)))
      (hβ.1.comp (measurable_inv.mul_const _)) measurable_inv).trans ?_
    simp only [inv_inv]
    exact hβ.2 _
  calc _ = ∫⁻ x in vecDomain E (UnipotentBlockColumnIndex k m m), (1 : ℝ≥0∞) ∂vecMeasure E (UnipotentBlockColumnIndex k m m) := lintegral_congr fun x => this x
    _ = 1 := by rw [setLIntegral_const, vecMeasure_vecDomain, one_mul]

theorem wtA (hN0 : N0) (hN3 : N3) (hN4a : CosetIntegralParabolic) (hN4b : OneMoreAdelicColumn) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m < k)
    {β : GA E k → ℝ≥0∞} (hβ : IsWt (nuP E k m) β) : IsWt (nuP E k (m - 1)) (bA m β) := by
  haveI : Countable (RowT E k m) := (hN0 E k m hm1 hmk.le).2.2.2.2.2.2.1
  refine ⟨Measurable.ennreal_tsum fun ξ => hβ.1.comp (measurable_const_mul _), fun g => ?_⟩
  have := hN4a E k m hm1 hmk.le (fun h => β (h * g)) (hβ.1.comp (measurable_mul_const g))
  rw [wtB hN3 hN4b hmk hβ g] at this
  rw [this]
  simp only [bA]
  rw [lintegral_tsum (f := fun ξ h => β ((ratGL E k (gam ξ))⁻¹ * (h * g)))
    fun ξ => ((hβ.1.comp (measurable_const_mul _)).comp (measurable_mul_const g)).aemeasurable]
  simp only [mul_assoc]

theorem hypB (hN3 : N3) (hN4b : OneMoreAdelicColumn) {m : ℕ} (hmk : m < k) {β : GA E k → ℝ≥0∞} (hβ : IsWt (nuP E k m) β)
    (g : GA E k) : ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k m ∂rhoB m = 1 := by
  haveI := ((hN3 E k).1 m hmk).1
  rw [rhoB, lintegral_map (measI hβ.1 g) (meas_blkU m)]
  exact (hN4b E k m hmk _ (hβ.1.comp (measurable_mul_const g))).symm.trans (wtB hN3 hN4b hmk hβ g)

theorem hypA (hN0 : N0) (hN3 : N3) (hN4a : CosetIntegralParabolic) (hN4b : OneMoreAdelicColumn) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m < k)
    {β : GA E k → ℝ≥0∞} (hβ : IsWt (nuP E k m) β) (g : GA E k) :
    ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k (m - 1) ∂rhoA m = 1 := by
  haveI := ((hN3 E k).1 (m - 1) (by omega)).1
  rw [rhoA, lintegral_sum_measure]
  refine (tsum_congr fun ξ => lintegral_dirac' _ (measI hβ.1 g)).trans ?_
  exact (hN4a E k m hm1 hmk.le _ (hβ.1.comp (measurable_mul_const g))).symm.trans (wtB hN3 hN4b hmk hβ g)

theorem lintegral_rhoB {m : ℕ} {Φ : GA E k → ℝ≥0∞} (hΦ : Measurable Φ) (g : GA E k) :
    ∫⁻ r, Φ (r * g) ∂rhoB m = ∫⁻ x in vecDomain E (UnipotentBlockColumnIndex k m m), Φ (blkU x * g) ∂vecMeasure E (UnipotentBlockColumnIndex k m m) :=
  lintegral_map (hΦ.comp (measurable_mul_const g)) (meas_blkU m)

theorem integral_rhoB {m : ℕ} {Φ : GA E k → ℂ} (hΦ : Continuous Φ) (g : GA E k) :
    ∫ r, Φ (r * g) ∂rhoB m = ∫ x in vecDomain E (UnipotentBlockColumnIndex k m m), Φ (blkU x * g) ∂vecMeasure E (UnipotentBlockColumnIndex k m m) :=
  integral_map (meas_blkU m).aemeasurable (hΦ.comp (continuous_mul_right g)).aestronglyMeasurable

theorem lintegral_rhoA {m : ℕ} {Φ : GA E k → ℝ≥0∞} (hΦ : Measurable Φ) (g : GA E k) :
    ∫⁻ r, Φ (r * g) ∂rhoA m = ∑' ξ : RowT E k m, Φ (ratGL E k (gam ξ) * g) := by
  rw [rhoA, lintegral_sum_measure]
  exact tsum_congr fun ξ => lintegral_dirac' _ (hΦ.comp (measurable_mul_const g))

theorem integral_rhoA {m : ℕ} {Φ : GA E k → ℂ} (hΦ : Continuous Φ) (g : GA E k)
    (hs : Summable fun ξ : RowT E k m => Φ (ratGL E k (gam ξ) * g)) :
    ∫ r, Φ (r * g) ∂rhoA m = ∑' ξ : RowT E k m, Φ (ratGL E k (gam ξ) * g) := by
  have hc : Continuous fun r => Φ (r * g) := hΦ.comp (continuous_mul_right g)
  have hn := summable_norm_iff.2 hs
  have hint : Integrable (fun r => Φ (r * g)) (rhoA m) := by
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral, rhoA, lintegral_sum_measure]
    rw [tsum_congr fun ξ => lintegral_dirac' _ (hc.measurable.enorm)]
    simp only [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hn]
    exact ENNReal.ofReal_lt_top
  rw [rhoA, integral_sum_measure hint]
  exact tsum_congr fun ξ => integral_dirac' _ _ hc.stronglyMeasurable

variable {ψ : AddChar (Ad E) ℂ}

theorem inv_sq (hP2 : P2) (hψ : StdPsi ψ) {n : ℕ} {f : GA E k → ℂ} (hf : Pre ψ n f) :
    ∀ h ∈ HS (k := k) n, ∀ g, ‖f (h * g)‖ₑ ^ 2 = ‖f g‖ₑ ^ 2 := by
  rintro h ⟨γ, u, hγ, hu, rfl⟩ g
  have hn : ‖psN ψ u‖ₑ = 1 := by rw [← ofReal_norm_eq_enorm, (hP2 E k ψ hψ).2.1 u, ENNReal.ofReal_one]
  rw [mul_assoc, hf.left γ hγ, (hP2 E k ψ hψ).1 n f hf u hu g, enorm_mul, hn, one_mul]

theorem inv_prod (hP2 : P2) (hψ : StdPsi ψ) {n : ℕ} {f φ : GA E k → ℂ} (hf : Pre ψ n f) (hφ : Pre ψ n φ) :
    ∀ h ∈ HS (k := k) n, ∀ g, f (h * g) * conj (φ (h * g)) = f g * conj (φ g) := by
  rintro h ⟨γ, u, hγ, hu, rfl⟩ g
  have hn : ‖psN ψ u‖ = 1 := (hP2 E k ψ hψ).2.1 u
  rw [mul_assoc, hf.left γ hγ, hφ.left γ hγ, (hP2 E k ψ hψ).1 n f hf u hu g, (hP2 E k ψ hψ).1 n φ hφ u hu g, map_mul]
  calc psN ψ u * f g * (conj (psN ψ u) * conj (φ g)) = (psN ψ u * conj (psN ψ u)) * (f g * conj (φ g)) := by ring
    _ = f g * conj (φ g) := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp

theorem int_mul {ν : Measure (GA E k)} {f φ : GA E k → ℂ} (hf : Continuous f) (hφ : Continuous φ)
    (h1 : ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν < ∞) (h2 : ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν < ∞) :
    Integrable (fun g => f g * conj (φ g)) ν := by
  have hF : Integrable (fun g => ‖f g‖ ^ 2 + ‖φ g‖ ^ 2) ν := by
    refine Integrable.add ⟨(hf.norm.pow 2).aestronglyMeasurable, ?_⟩ ⟨(hφ.norm.pow 2).aestronglyMeasurable, ?_⟩
    · simpa only [HasFiniteIntegral, enorm_pow, enorm_norm] using h1
    · simpa only [HasFiniteIntegral, enorm_pow, enorm_norm] using h2
  refine hF.mono' (hf.mul (Complex.continuous_conj.comp hφ)).aestronglyMeasurable (ae_of_all _ fun g => ?_)
  rw [norm_mul, Complex.norm_conj]
  nlinarith [norm_nonneg (f g), norm_nonneg (φ g), sq_nonneg (‖f g‖ - ‖φ g‖)]

theorem parseval_gen (hP0 : P0) (hψ : StdPsi ψ) {m : ℕ} {f φ : GA E k → ℂ} (hf : Pre ψ m f) (hφ : Pre ψ m φ)
    (g : GA E k) :
    HasSum (fun ξ : UnipotentBlockColumnIndex k m m → E => coefF ψ m ξ f g * conj (coefF ψ m ξ φ g))
      (∫ x in vecDomain E (UnipotentBlockColumnIndex k m m), f (blkU x * g) * conj (φ (blkU x * g)) ∂vecMeasure E (UnipotentBlockColumnIndex k m m)) := by
  have hl : ∀ {F : GA E k → ℂ}, Pre ψ m F → ∀ (c : UnipotentBlockColumnIndex k m m → E) g, F (ratGL E k (blkU c) * g) = F g :=
    fun hF c g => hF.left _ (isMir_blkU c) g
  obtain ⟨h1, h2, -⟩ := hP0 E ψ hψ (UnipotentBlockColumnIndex k m m)
  have H := h2 _ _ (per_blk hf.cont (hl hf) g) (per_blk hφ.cont (hl hφ) g)
  have hp := per_blk (r := m) (m := m) (f := fun g => f g * conj (φ g))
    (hf.cont.mul (Complex.continuous_conj.comp hφ.cont)) (fun c g => by simp only [hl hf, hl hφ]) g
  rw [h1 _ hp] at H
  exact H

theorem coef_zero {m : ℕ} (hm1 : 1 ≤ m) {φ : GA E k → ℂ} (hφ : Good ψ m φ) (g : GA E k) : coefF ψ m 0 φ g = 0 := by
  have := hφ.van m (by omega) le_rfl g
  rw [← this]
  unfold coefF
  congr 1
  ext x
  simp [dot]

theorem row_eq (hP1 : P1) (hψ : StdPsi ψ) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m < k) {f : GA E k → ℂ} (hf : Pre ψ m f)
    (e : RowT E k m ≃ {ξ : UnipotentBlockColumnIndex k m m → E // ξ ≠ 0}) (he : ∀ ξ t, (e ξ).1 t = ξ.1 t.1.1) (ξ : RowT E k m) (g : GA E k) :
    colT ψ m f (ratGL E k (gam ξ) * g) = coefF ψ m (e ξ).1 f g := by
  rw [← (hP1 E k ψ hψ m hm1 hmk f hf).2.1]
  congr 1
  exact (funext (he ξ)).symm

theorem parseval (hP0 : P0) (hP1 : P1) (hψ : StdPsi ψ) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m < k) {f φ : GA E k → ℂ}
    (hf : Pre ψ m f) (hφ : Good ψ m φ) (hφp : Pre ψ m φ) (g : GA E k) :
    HasSum (fun ξ : RowT E k m => colT ψ m f (ratGL E k (gam ξ) * g) * conj (colT ψ m φ (ratGL E k (gam ξ) * g)))
      (∫ x in vecDomain E (UnipotentBlockColumnIndex k m m), f (blkU x * g) * conj (φ (blkU x * g)) ∂vecMeasure E (UnipotentBlockColumnIndex k m m)) := by
  have H := parseval_gen hP0 hψ hf hφp g
  obtain ⟨-, -, -, e, he⟩ := hP1 E k ψ hψ m hm1 hmk f hf
  have hs : Function.support (fun ξ : UnipotentBlockColumnIndex k m m → E => coefF ψ m ξ f g * conj (coefF ψ m ξ φ g)) ⊆ {ξ | ξ ≠ 0} := by
    intro ξ hξ
    rintro rfl
    exact hξ (by simp [coef_zero hm1 hφ g])
  rw [← hasSum_subtype_iff_of_support_subset hs] at H
  have H2 := (Equiv.hasSum_iff e (f := fun ξ : {ξ : UnipotentBlockColumnIndex k m m → E // ξ ≠ 0} =>
    coefF ψ m ξ.1 f g * conj (coefF ψ m ξ.1 φ g))).2 H
  convert H2 using 2 with ξ
  simp only [Function.comp_apply, row_eq hP1 hψ hm1 hmk hf e he, row_eq hP1 hψ hm1 hmk hφp e he]

theorem bessel (hP0 : P0) (hP1 : P1) (hψ : StdPsi ψ) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m < k) {f : GA E k → ℂ}
    (hf : Pre ψ m f) (g : GA E k) :
    ∑' ξ : RowT E k m, ‖colT ψ m f (ratGL E k (gam ξ) * g)‖ₑ ^ 2 ≤
      ∫⁻ x in vecDomain E (UnipotentBlockColumnIndex k m m), ‖f (blkU x * g)‖ₑ ^ 2 ∂vecMeasure E (UnipotentBlockColumnIndex k m m) := by
  by_cases hI : ∫⁻ x in vecDomain E (UnipotentBlockColumnIndex k m m), ‖f (blkU x * g)‖ₑ ^ 2 ∂vecMeasure E (UnipotentBlockColumnIndex k m m) = ∞
  · rw [hI]; exact le_top
  have hc : Continuous fun x : UnipotentBlockColumnIndex k m m → Ad E => f (blkU x * g) :=
    hf.cont.comp ((continuous_posU (isNil_blk k m m)).mul continuous_const)
  have hI2 : Integrable (fun x => ‖f (blkU x * g)‖ ^ 2)
      ((vecMeasure E (UnipotentBlockColumnIndex k m m)).restrict (vecDomain E (UnipotentBlockColumnIndex k m m))) := by
    refine ⟨(hc.norm.pow 2).aestronglyMeasurable, ?_⟩
    simpa only [HasFiniteIntegral, enorm_pow, enorm_norm] using lt_top_iff_ne_top.2 hI
  have H := parseval_gen hP0 hψ hf hf g
  obtain ⟨-, -, -, e, he⟩ := hP1 E k ψ hψ m hm1 hmk f hf
  have hre : (∫ x in vecDomain E (UnipotentBlockColumnIndex k m m), f (blkU x * g) * conj (f (blkU x * g)) ∂vecMeasure E (UnipotentBlockColumnIndex k m m)) =
      ((∫ x in vecDomain E (UnipotentBlockColumnIndex k m m), ‖f (blkU x * g)‖ ^ 2 ∂vecMeasure E (UnipotentBlockColumnIndex k m m) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    ext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hre] at H
  have Hr := Complex.hasSum_re H
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re] at Hr
  have hlin : ∫⁻ x in vecDomain E (UnipotentBlockColumnIndex k m m), ‖f (blkU x * g)‖ₑ ^ 2 ∂vecMeasure E (UnipotentBlockColumnIndex k m m) =
      ENNReal.ofReal (∫ x in vecDomain E (UnipotentBlockColumnIndex k m m), ‖f (blkU x * g)‖ ^ 2 ∂vecMeasure E (UnipotentBlockColumnIndex k m m)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hI2 (ae_of_all _ fun _ => by positivity)]
    congr 1
    ext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hlin, ← Hr.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) Hr.summable]
  calc ∑' ξ : RowT E k m, ‖colT ψ m f (ratGL E k (gam ξ) * g)‖ₑ ^ 2
      = ∑' ξ : RowT E k m, ENNReal.ofReal (‖coefF ψ m (e ξ).1 f g‖ ^ 2) := by
        refine tsum_congr fun ξ => ?_
        rw [row_eq hP1 hψ hm1 hmk hf e he, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (Subtype.val_injective.comp e.injective)
        (fun ξ : UnipotentBlockColumnIndex k m m → E => ENNReal.ofReal (‖coefF ψ m ξ f g‖ ^ 2))

theorem sf_B (m : ℕ) : SFinite (rhoB (E := E) (k := k) m) := by unfold rhoB; infer_instance

theorem sf_A (m : ℕ) [Countable (RowT E k m)] : SFinite (rhoA (E := E) (k := k) m) := by unfold rhoA; infer_instance

end WeightCoefficients

theorem twistedGeometricSide_unfolding : Q1 → Q2 → N0 → N3 → CosetIntegralParabolic → OneMoreAdelicColumn → P0 → P1 → P2 → U1 := by
  intro hQ1 hQ2 hN0 hN3 hN4a hN4b hP0 hP1 hP2
  intro E _ _ _ k μ _ ψ hψ m hm1 hmk β hβ
  haveI : Countable (RowT E k m) := (hN0 E k m hm1 hmk.le).2.2.2.2.2.2.1
  have hPm := (hN3 E k).1 m hmk
  have hPm1 := (hN3 E k).1 (m - 1) (by omega)
  haveI := hPm.1
  haveI := hPm1.1
  haveI := WeightCoefficients.sf_A (E := E) (k := k) m
  haveI := WeightCoefficients.sf_B (E := E) (k := k) m
  have hwA := WeightCoefficients.wtA hN0 hN3 hN4a hN4b hm1 hmk hβ
  have hA : ∀ f, Pre ψ m f → ∫⁻ g, ‖colT ψ m f g‖ₑ ^ 2 ∂μ.withDensity (WeightCoefficients.bA m β) ≤
      ∫⁻ g, ‖f g‖ₑ ^ 2 ∂μ.withDensity β := by
    intro f hf
    have hcf : Pre ψ (m - 1) (colT ψ m f) := (hP1 E k ψ hψ m hm1 hmk f hf).1
    rw [hQ1 (GA E k) μ (nuP E k (m - 1)) (WeightCoefficients.rhoA m) (WeightCoefficients.HS (m - 1)) (WeightCoefficients.bA m β) β hPm1.2.1 hPm1.2.2 hwA hβ.1
        (WeightCoefficients.hypA hN0 hN3 hN4a hN4b hm1 hmk hβ) (fun g => ‖colT ψ m f g‖ₑ ^ 2)
        (hcf.cont.measurable.enorm.pow_const 2) (WeightCoefficients.inv_sq hP2 hψ hcf),
      hQ1 (GA E k) μ (nuP E k m) (WeightCoefficients.rhoB m) (WeightCoefficients.HS m) β β hPm.2.1 hPm.2.2 hβ hβ.1
        (WeightCoefficients.hypB hN3 hN4b hmk hβ) (fun g => ‖f g‖ₑ ^ 2) (hf.cont.measurable.enorm.pow_const 2) (WeightCoefficients.inv_sq hP2 hψ hf)]
    refine lintegral_mono fun g => ?_
    rw [WeightCoefficients.lintegral_rhoA (hcf.cont.measurable.enorm.pow_const 2),
      WeightCoefficients.lintegral_rhoB (hf.cont.measurable.enorm.pow_const 2)]
    exact WeightCoefficients.bessel hP0 hP1 hψ hm1 hmk hf g
  refine ⟨WeightCoefficients.bA m β, hwA, hA, ?_⟩
  intro f φ hf hφ hf2 hφ2
  have hφp : Pre ψ m φ := (hP2 E k ψ hψ).2.2.2.2.2.1 m φ hφ
  have hcf : Pre ψ (m - 1) (colT ψ m f) := (hP1 E k ψ hψ m hm1 hmk f hf).1
  have hcφ : Pre ψ (m - 1) (colT ψ m φ) := (hP1 E k ψ hψ m hm1 hmk φ hφp).1
  have c1 : Continuous fun g => f g * conj (φ g) := hf.cont.mul (Complex.continuous_conj.comp hφp.cont)
  have c2 : Continuous fun g => colT ψ m f g * conj (colT ψ m φ g) :=
    hcf.cont.mul (Complex.continuous_conj.comp hcφ.cont)
  have hb := (hQ2 (GA E k) μ (nuP E k m) (WeightCoefficients.rhoB m) (WeightCoefficients.HS m) β β hPm.2.1 hPm.2.2 hβ hβ.1
    (WeightCoefficients.hypB hN3 hN4b hmk hβ) (fun g => f g * conj (φ g)) c1.measurable (WeightCoefficients.inv_prod hP2 hψ hf hφp)
    (WeightCoefficients.int_mul hf.cont hφp.cont hf2 hφ2)).2
  have ha := (hQ2 (GA E k) μ (nuP E k (m - 1)) (WeightCoefficients.rhoA m) (WeightCoefficients.HS (m - 1)) (WeightCoefficients.bA m β) β hPm1.2.1 hPm1.2.2 hwA
    hβ.1 (WeightCoefficients.hypA hN0 hN3 hN4a hN4b hm1 hmk hβ) (fun g => colT ψ m f g * conj (colT ψ m φ g)) c2.measurable
    (WeightCoefficients.inv_prod hP2 hψ hcf hcφ)
    (WeightCoefficients.int_mul hcf.cont hcφ.cont ((hA f hf).trans_lt hf2) ((hA φ hφp).trans_lt hφ2))).2
  rw [hb, ha]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  have H := WeightCoefficients.parseval hP0 hP1 hψ hm1 hmk hf hφ hφp g
  exact (WeightCoefficients.integral_rhoB c1 g).trans (H.tsum_eq.symm.trans (WeightCoefficients.integral_rhoA c2 g H.summable).symm)

end PositivityTheory.AdelicQuotientData

end
