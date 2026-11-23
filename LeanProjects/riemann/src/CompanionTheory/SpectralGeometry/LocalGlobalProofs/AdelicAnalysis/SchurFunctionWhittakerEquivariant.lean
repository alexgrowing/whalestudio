import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DenominatorPowerSummableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierCoefficientGrowthBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOperatorIntegralInvarianceStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesSelfDualStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PositiveDefiniteDensityStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.Dens

variable {F : Type} [Field F] [NumberField F]

lemma oh_add {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x + y ∈ Oh F :=
  fun v => add_mem (hx v) (hy v)

lemma oh_neg {x : A F} (hx : x ∈ Oh F) : -x ∈ Oh F :=
  fun v => neg_mem (hx v)

lemma oh_mul {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F :=
  fun v => mul_mem (hx v) (hy v)

lemma oh_alg (r : 𝓞 F) : algebraMap F (A F) (r : F) ∈ Oh F :=
  (((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1) (r : F)).2 ⟨r, rfl⟩

lemma nat_cast_eq (n : ℕ) : (n : A F) = algebraMap F (A F) (n : F) := (map_natCast _ n).symm

lemma oh_nat (n : ℕ) : (n : A F) ∈ Oh F := by
  have h : (((n : 𝓞 F)) : F) = (n : F) := by simp
  rw [nat_cast_eq, ← h]
  exact oh_alg _

lemma nat_inv_mul {N : ℕ} (hN : 0 < N) : algebraMap F (A F) (1 / (N : F)) * (N : A F) = 1 := by
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  rw [nat_cast_eq, ← map_mul, one_div, inv_mul_cancel₀ hN', map_one]

lemma setS_isOpen (a : ℕ) : IsOpen {x : A F | (a : A F) * x ∈ Oh F} :=
  ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.1).preimage (continuous_const.mul continuous_id)

lemma setS_isCompact {a : ℕ} (ha : 0 < a) : IsCompact {x : A F | (a : A F) * x ∈ Oh F} := by
  have hc : IsCompact ((fun x : A F => algebraMap F (A F) (1 / (a : F)) * x) '' Oh F) :=
    ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.1).image (continuous_const.mul continuous_id)
  convert hc using 1
  ext y
  constructor
  · intro hy
    exact ⟨(a : A F) * y, hy, by
      show algebraMap F (A F) (1 / (a : F)) * ((a : A F) * y) = y
      rw [← mul_assoc, nat_inv_mul ha, one_mul]⟩
  · rintro ⟨x, hx, rfl⟩
    show (a : A F) * _ ∈ Oh F
    rw [← mul_assoc, mul_comm (a : A F), nat_inv_mul ha, one_mul]
    exact hx

lemma setL_eq (ι : Type) (a : ℕ) : {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} =
    Set.pi Set.univ fun _ => {x : A F | (a : A F) * x ∈ Oh F} := by
  ext x; simp

lemma setL_isCompact (ι : Type) {a : ℕ} (ha : 0 < a) :
    IsCompact {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := by
  rw [setL_eq]
  exact isCompact_univ_pi fun _ => setS_isCompact ha

lemma setL_isOpen (ι : Type) [Fintype ι] (a : ℕ) :
    IsOpen {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := by
  rw [setL_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ => setS_isOpen a

lemma indL_SB (ι : Type) [Fintype ι] {a : ℕ} (ha : 0 < a) :
    SB (indL a : (ι → A F) → ℂ) := by
  haveI : T2Space (A F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.1
  have hK := setL_isCompact (F := F) ι ha
  have hO := setL_isOpen (F := F) ι a
  refine ⟨?_, ?_⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}
    · refine ⟨_, hO, hx, fun y hy => ?_⟩
      simp only [indL]
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · refine ⟨_, hK.isClosed.isOpen_compl, hx, fun y hy => ?_⟩
      simp only [indL]
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · refine HasCompactSupport.intro hK fun x hx => ?_
    simp only [indL]
    exact Set.indicator_of_notMem hx _

def Hs (F : Type) [Field F] [NumberField F] (N : ℕ) : Set (A F) := {x | ∃ y ∈ Oh F, x = (N : A F) * y}

lemma hs_add {N : ℕ} {x y : A F} (hx : x ∈ Hs F N) (hy : y ∈ Hs F N) : x + y ∈ Hs F N := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  exact ⟨u + w, oh_add hu hw, by ring⟩

lemma hs_neg {N : ℕ} {x : A F} (hx : x ∈ Hs F N) : -x ∈ Hs F N := by
  obtain ⟨u, hu, rfl⟩ := hx
  exact ⟨-u, oh_neg hu, by ring⟩

lemma hs_zero (N : ℕ) : (0 : A F) ∈ Hs F N :=
  ⟨0, fun v => zero_mem _, by ring⟩

lemma hs_alg (N : ℕ) (r : 𝓞 F) : algebraMap F (A F) ((N : F) * (r : F)) ∈ Hs F N :=
  ⟨_, oh_alg r, by rw [map_mul, nat_cast_eq]⟩

lemma hs_sub_oh {N : ℕ} {x : A F} (hx : x ∈ Hs F N) : x ∈ Oh F := by
  obtain ⟨u, hu, rfl⟩ := hx
  exact oh_mul (oh_nat N) hu

lemma hs_isOpen {N : ℕ} (hN : 0 < N) : IsOpen (Hs F N) :=
  (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.2.2.2 N hN

lemma hs_alg_iff {N : ℕ} (hN : 0 < N) {c : F} (h : algebraMap F (A F) c ∈ Hs F N) :
    ∃ r : 𝓞 F, c = (N : F) * (r : F) := by
  obtain ⟨u, hu, he⟩ := h
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : algebraMap F (A F) (c / (N : F)) = u := by
    have : c / (N : F) = (1 / (N : F)) * c := by field_simp
    rw [this, map_mul, he, ← mul_assoc, nat_inv_mul hN, one_mul]
  have h3 : algebraMap F (A F) (c / (N : F)) ∈ Oh F := h2 ▸ hu
  obtain ⟨r, hr⟩ := ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 _).1 h3
  exact ⟨r, by rw [hr]; field_simp⟩

def congN (F : Type) [Field F] [NumberField F] (N : ℕ) : Setoid F where
  r b b' := ∃ r : 𝓞 F, b - b' = (N : F) * (r : F)
  iseqv :=
    { refl := fun b => ⟨0, by simp⟩
      symm := by
        rintro b b' ⟨r, hr⟩
        exact ⟨-r, by push_cast; rw [mul_neg, ← hr]; ring⟩
      trans := by
        rintro b b' b'' ⟨r, hr⟩ ⟨t, ht⟩
        exact ⟨r + t, by push_cast; rw [mul_add, ← hr, ← ht]; ring⟩ }

theorem integrable_of_periodic [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F))
    (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1) (f : A F → ℂ) {N : ℕ} (hN : 0 < N)
    (hper : ∀ x ∈ Oh F, ∀ y, f (y + (N : A F) * x) = f y) {C : ℝ} {M : ℕ} (hM : 3 ≤ M)
    (hdec : ∀ b : F, ‖f (algebraMap F (A F) b)‖ ≤ C * ((den b : ℝ) ^ M)⁻¹) : Integrable f lf := by
  haveI := hlf
  haveI : SecondCountableTopology (A F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.1
  have hdense : DenseRange (algebraMap F (A F)) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.1
  have hHo : IsOpen (Hs F N) := hs_isOpen hN
  let st := congN F N
  let s : Set F := Set.range (fun q : Quotient st => q.out)
  have hs : ∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b' := by
    rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ h
    have : q = q' := Quotient.out_equiv_out.1 h
    rw [this]
  have hsum := ((GlobalTheory.T.denominator_power_summable F M hM N hN).2.2 s hs)
  have hden0 := (GlobalTheory.T.denominator_power_summable F M hM N hN).2.1
  have hscount : Countable s := by
    have hc := hsum.countable_support
    have : Function.support (fun b : s => ((den (b : F) : ℝ) ^ M)⁻¹) = Set.univ := by
      ext b
      have := hden0 b
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      positivity
    rw [this] at hc
    exact Set.countable_univ_iff.1 hc
  let T : s → Set (A F) := fun b => {y | y - algebraMap F (A F) (b : F) ∈ Hs F N}
  have hTo : ∀ b, IsOpen (T b) := fun b => hHo.preimage (continuous_id.sub continuous_const)
  have hTd : Pairwise (Function.onFun Disjoint T) := by
    intro b b' hne
    refine Set.disjoint_left.2 fun y hy hy' => hne (Subtype.ext ?_)
    have h : algebraMap F (A F) ((b : F) - (b' : F)) ∈ Hs F N := by
      have := hs_add hy' (hs_neg hy)
      convert this using 1
      rw [map_sub]; ring
    exact hs _ b.2 _ b'.2 (hs_alg_iff hN h)
  have hTc : ⋃ b, T b = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    have hW : IsOpen {z : A F | z - y ∈ Hs F N} := hHo.preimage (continuous_id.sub continuous_const)
    obtain ⟨b', hb'⟩ := hdense.exists_mem_open hW ⟨y, by simpa using hs_zero N⟩
    let q : Quotient st := Quotient.mk st b'
    obtain ⟨r, hr⟩ : st.r q.out b' := Quotient.mk_out (s := st) b'
    refine Set.mem_iUnion.2 ⟨⟨q.out, q, rfl⟩, ?_⟩
    have h2 : algebraMap F (A F) ((N : F) * (r : F)) ∈ Hs F N := hs_alg N r
    show y - algebraMap F (A F) q.out ∈ Hs F N
    have h3 : q.out = b' + (N : F) * (r : F) := by rw [← hr]; ring
    have h4 := hs_neg (hs_add hb' h2)
    convert h4 using 1
    rw [h3, map_add]; ring
  have hconst : ∀ b : s, ∀ y ∈ T b, f y = f (algebraMap F (A F) (b : F)) := by
    intro b y hy
    obtain ⟨u, hu, he⟩ := hy
    have : y = algebraMap F (A F) (b : F) + (N : A F) * u := by rw [← he]; ring
    rw [this, hper u hu]
  have hcont : Continuous f := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun y => ?_)
    refine ⟨{z | z - y ∈ Hs F N}, hHo.preimage (continuous_id.sub continuous_const), by simpa using hs_zero N, ?_⟩
    intro z hz
    obtain ⟨u, hu, he⟩ := hz
    have : z = y + (N : A F) * u := by rw [← he]; ring
    rw [this, hper u hu]
  have hmeasT : ∀ b, lf (T b) ≤ 1 := by
    intro b
    have : lf (T b) = lf (Hs F N) := by
      have := measure_preimage_add_right lf (-algebraMap F (A F) (b : F)) (Hs F N)
      rw [← this]
      congr 1
      ext y
      simp [T, sub_eq_add_neg]
    rw [this, ← h1]
    exact measure_mono fun x hx => hs_sub_oh hx
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hnn : ∀ b : s, 0 ≤ C * ((den (b : F) : ℝ) ^ M)⁻¹ := fun b => (norm_nonneg _).trans (hdec b)
  have hb : ∫⁻ y, ‖f y‖ₑ ∂lf ≤ ENNReal.ofReal (∑' b : s, C * ((den (b : F) : ℝ) ^ M)⁻¹) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnn (hsum.mul_left C)]
    calc ∫⁻ y, ‖f y‖ₑ ∂lf = ∫⁻ y in ⋃ b, T b, ‖f y‖ₑ ∂lf := by rw [hTc, Measure.restrict_univ]
      _ = ∑' b, ∫⁻ y in T b, ‖f y‖ₑ ∂lf := lintegral_iUnion (fun b => (hTo b).measurableSet) hTd _
      _ ≤ ∑' b : s, ENNReal.ofReal (C * ((den (b : F) : ℝ) ^ M)⁻¹) := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        calc ∫⁻ y in T b, ‖f y‖ₑ ∂lf = ∫⁻ _ in T b, ‖f (algebraMap F (A F) (b : F))‖ₑ ∂lf :=
              setLIntegral_congr_fun (hTo b).measurableSet fun y hy => by rw [hconst b y hy]
          _ = ‖f (algebraMap F (A F) (b : F))‖ₑ * lf (T b) := by rw [setLIntegral_const]
          _ ≤ ‖f (algebraMap F (A F) (b : F))‖ₑ * 1 := by gcongr; exact hmeasT b
          _ ≤ ENNReal.ofReal (C * ((den (b : F) : ℝ) ^ M)⁻¹) := by
              rw [mul_one, ← ofReal_norm_eq_enorm]
              exact ENNReal.ofReal_le_ofReal (hdec b)
  exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top

theorem density_main : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ a : ℕ, 0 < a → ∃ Df : A F → ℝ, Continuous Df ∧ (∀ y, 0 ≤ Df y) ∧ (∀ U : Set (A F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i, (a : A F) * x i ∈ Oh F) ∧ qf (hf F) (Bf B) x ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df y) ∂lf) ∧ Integrable (fstar ψ (hf F) (Bf B) (muF B lf) (indL a)) lf ∧ ∀ z : A F, ∫ y, fstar ψ (hf F) (Bf B) (muF B lf) (indL a) y * ψ (-z * y) ∂lf = ((kap F ^ (2 * M - 2) * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * Df z : ℝ) : ℂ) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM a ha
  haveI := hlf
  obtain ⟨hLC, hSC, hT2, hOc, hOo, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hQ' : QSetup M B ρ P := hQ
  obtain ⟨hTR, hcard, hsym, hdet, -⟩ := hQ
  have hψc : Continuous ψ := hψ.1
  let L : Set (ι → A F) := {x | ∀ i, (a : A F) * x i ∈ Oh F}
  have hLm : MeasurableSet L := (setL_isOpen (F := F) ι a).measurableSet
  let μ0 : Measure (ι → A F) := Measure.pi fun _ => lf
  haveI : IsFiniteMeasureOnCompacts μ0 := inferInstance
  let q : (ι → A F) → A F := qf (hf F) (Bf B)
  have hqc : Continuous q := by
    refine continuous_const.mul ?_
    exact Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id)
  let m : Measure (A F) := (μ0.restrict L).map q
  have mU : ∀ U : Set (A F), MeasurableSet U → m U = μ0 {x | (∀ i, (a : A F) * x i ∈ Oh F) ∧ q x ∈ U} := by
    intro U hU
    rw [Measure.map_apply hqc.measurable hU, Measure.restrict_apply (hqc.measurable hU)]
    congr 1
    ext x
    exact and_comm
  have hLfin : μ0 L < ⊤ := (setL_isCompact (F := F) ι ha).measure_lt_top
  haveI hmfin : IsFiniteMeasure m := by
    refine ⟨?_⟩
    rw [mU _ MeasurableSet.univ]
    exact lt_of_le_of_lt (measure_mono fun x hx => hx.1) hLfin
  let s : ℝ := Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|
  have hs0 : 0 < s := by
    refine Real.sqrt_pos.2 (abs_pos.2 ?_)
    exact_mod_cast (Algebra.norm_ne_zero_iff.2 hdet)
  have hk0 : 0 < kap F := by
    refine inv_pos.2 (Real.sqrt_pos.2 (abs_pos.2 ?_))
    exact_mod_cast discr_ne_zero F
  let c : ℝ := kap F ^ Fintype.card ι * s⁻¹
  have hc0 : 0 < c := by positivity
  let fs : A F → ℂ := fstar ψ (hf F) (Bf B) (muF B lf) (indL a)
  let mh : A F → ℂ := fun y => ∫ x, ψ (x * y) ∂m
  have hfst : ∀ y, fs y = (c : ℂ) * mh y := by
    intro y
    have hcm : Continuous fun x : A F => ψ (x * y) := hψc.comp (continuous_id.mul continuous_const)
    simp only [fs, mh, fstar, muF]
    rw [integral_smul_measure, integral_map hqc.aemeasurable hcm.aestronglyMeasurable]
    rw [ENNReal.toReal_ofReal hc0.le, Complex.real_smul]
    congr 1
    rw [← integral_indicator hLm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ L
    · rw [Set.indicator_of_mem hu]
      simp only [opU, indL]
      rw [Set.indicator_of_mem hu, mul_one, mul_comm y]
    · rw [Set.indicator_of_notMem hu]
      simp only [opU, indL]
      rw [Set.indicator_of_notMem hu, mul_zero]
  have hint : Integrable fs lf := by
    obtain ⟨N, hN, hper⟩ := GlobalTheory.T.weil_operator_integral_invariance F lf hlf h1 ψ hψ ι M B ρ P hQ' (indL a) (indL_SB ι ha)
    obtain ⟨C, hC⟩ := GlobalTheory.T.fourier_coefficient_growth_bound F lf hlf h1 ψ hψ ι M B ρ P hQ' (indL a) (indL_SB ι ha)
    exact integrable_of_periodic lf hlf h1 fs hN (fun x hx y => (hper x hx).2 y) hM hC
  have hmh : mh = fun y => ((c : ℂ))⁻¹ * fs y := by
    funext y
    rw [hfst y, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hc0.ne'), one_mul]
  have hint' : Integrable mh lf := by
    rw [hmh]; exact hint.const_mul _
  have hint'' : Integrable mh (ENNReal.ofReal (kap F) • lf) :=
    hint'.smul_measure ENNReal.ofReal_ne_top
  obtain ⟨D, hDc, hD0, hDe, hDm⟩ := GlobalTheory.T.positive_definite_density (A F) (fun x y => ψ (x * y)) _
    (GlobalTheory.T.adeles_self_dual F lf hlf h1 ψ hψ) m hmfin hint''
  refine ⟨fun y => kap F * D y, continuous_const.mul hDc, fun y => mul_nonneg hk0.le (hD0 y), ?_, hint, ?_⟩
  · intro U hU
    have e1 := hDm U hU
    rw [mU U hU] at e1
    show μ0 _ = _
    rw [e1, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_mul hk0.le]
  · intro z
    have e2 := hDe z
    rw [integral_smul_measure, ENNReal.toReal_ofReal hk0.le, Complex.real_smul] at e2
    have e3 : ∫ y, fs y * ψ (-z * y) ∂lf = (c : ℂ) * ∫ y, mh y * ψ (-z * y) ∂lf := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hfst y]; ring
    show ∫ y, fs y * ψ (-z * y) ∂lf = _
    rw [e3]
    have e4 : (c : ℂ) = ((kap F ^ (2 * M - 2) * s⁻¹ * kap F * kap F : ℝ) : ℂ) := by
      have : kap F ^ (2 * M) = kap F ^ (2 * M - 2) * kap F * kap F := by
        rw [mul_assoc, ← pow_two, ← pow_add]; congr 1; omega
      simp only [c, hcard, this]
      push_cast; ring
    have e5 : (((kap F ^ (2 * M - 2) * s⁻¹ * (kap F * D z)) : ℝ) : ℂ) =
        ((kap F ^ (2 * M - 2) * s⁻¹ * kap F : ℝ) : ℂ) * (D z : ℂ) := by
      push_cast; ring
    show _ = (((kap F ^ (2 * M - 2) * s⁻¹ * (kap F * D z)) : ℝ) : ℂ)
    rw [e5, e2, e4]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SW.Core.Dens
