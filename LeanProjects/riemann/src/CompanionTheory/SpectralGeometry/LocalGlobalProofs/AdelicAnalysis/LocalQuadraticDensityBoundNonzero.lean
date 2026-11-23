import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityNearOneStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardLocalHaarPropertiesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GBall

variable {F : Type} [Field F] [NumberField F]

theorem exists_unif (v : HeightOneSpectrum (𝓞 F)) : ∃ π : Fv F v, Valued.v π = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  exact ⟨((π : v.adicCompletion F) : Fv F v), by rw [v.valuedAdicCompletion_eq_valuation', hπ]⟩

theorem le_exp_of_lt_one {a : WithZero (Multiplicative ℤ)} (h : a < 1) : a ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le
  · rw [← WithZero.exp_log ha] at h ⊢
    have h' : WithZero.log a < 0 := by
      rw [← WithZero.exp_lt_exp, WithZero.exp_zero]; exact h
    rw [WithZero.exp_le_exp]
    omega

variable {v : HeightOneSpectrum (𝓞 F)} {ι : Type} [Fintype ι]

theorem mem_int {x : Fv F v} : x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := by
  exact Iff.rfl

theorem q_int (h2 : Valued.v (2 : Fv F v) = 1) {B : Matrix ι ι (Fv F v)}
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F) {y : ι → Fv F v}
    (hy : ∀ i, y i ∈ v.adicCompletionIntegers F) :
    Valued.v ((2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y))) ≤ 1 := by
  have hmem : y ⬝ᵥ (B *ᵥ y) ∈ v.adicCompletionIntegers F := by
    simp only [dotProduct, Matrix.mulVec]
    exact sum_mem fun i _ => mul_mem (hy i) (sum_mem fun j _ => mul_mem (hB i j) (hy j))
  rw [map_mul, map_inv₀, h2, inv_one, one_mul]
  exact hmem

theorem q_smul (B : Matrix ι ι (Fv F v)) (π : Fv F v) (y : ι → Fv F v) :
    (2 : Fv F v)⁻¹ * ((fun i => π * y i) ⬝ᵥ (B *ᵥ fun i => π * y i)) =
      π * (π * ((2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)))) := by
  have hf : (fun i => π * y i) = π • y := rfl
  rw [hf, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

theorem borel_Fv : BorelSpace (Fv F v) := by
  exact ⟨rfl⟩

private theorem sigmaFinite_nnreal_smul {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    (c : ℝ≥0) : SigmaFinite ((c : ℝ≥0∞) • ν) := by
  refine ⟨⟨⟨spanningSets ν, fun _ => trivial, fun i => ?_, iUnion_spanningSets ν⟩⟩⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_spanningSets_lt_top ν i)

theorem pi_const_smul (ι : Type) [Fintype ι] {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    (c : ℝ≥0) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • ν) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => ν) := by
  haveI := sigmaFinite_nnreal_smul ν c
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

private theorem sigmaFinite_of_isStdV {lam : Measure (Fv F v)} (hstd : IsStdV v lam) :
    SigmaFinite lam := by
  haveI := borel_Fv (F := F) (v := v)
  obtain ⟨π, hπ⟩ := exists_unif v
  obtain ⟨-, hmap, -, -⟩ := GlobalTheory.T.standard_local_haar_properties F v lam hstd
  have hm := hmap π hπ
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (Fv F v)) :=
    (Valued.isOpen_valuationSubring (Fv F v)).measurableSet
  have hpk : ∀ k : ℕ, Valued.v (π ^ k) = WithZero.exp (-(k : ℤ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
      rw [pow_succ, map_mul, ihk, hπ, ← WithZero.exp_add]
      congr 1
      push_cast
      ring
  let S : ℕ → Set (Fv F v) := fun n => (fun x => π ^ n * x) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => (measurable_const_mul _) hO
  have hSfin : ∀ n, lam (S n) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ n := by
    intro n
    induction n with
    | zero =>
      show lam ((fun x => π ^ 0 * x) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) = _
      simp only [pow_zero, one_mul, Set.preimage_id', hstd.2]
    | succ n ihn =>
      have hS : S (n + 1) = (fun t => π * t) ⁻¹' S n := by
        ext x
        simp only [S, Set.mem_preimage, pow_succ, mul_assoc]
      rw [hS, ← Measure.map_apply (measurable_const_mul π) (hSmeas n), hm, Measure.smul_apply, ihn,
        smul_eq_mul, pow_succ, mul_comm]
  refine ⟨⟨⟨S, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [hSfin]
    exact ENNReal.pow_lt_top (ENNReal.natCast_lt_top _)
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
    rcases eq_or_ne x 0 with rfl | hx
    · refine ⟨0, ?_⟩
      show Valued.v (π ^ 0 * 0) ≤ 1
      rw [mul_zero, map_zero]
      exact zero_le
    · have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      show Valued.v (π ^ (WithZero.log (Valued.v x)).toNat * x) ≤ 1
      rw [map_mul, hpk, ← WithZero.exp_log hvx, ← WithZero.exp_add]
      refine (WithZero.exp_le_exp.mpr ?_).trans_eq WithZero.exp_zero
      rw [WithZero.log_exp]
      omega

theorem pi_scale {lam : Measure (Fv F v)} (hstd : IsStdV v lam) {π : Fv F v}
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) (T : Set (ι → Fv F v)) :
    (Measure.pi fun _ : ι => lam) {y | (fun i => π * y i) ∈ T} =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ Fintype.card ι * (Measure.pi fun _ : ι => lam) T := by
  haveI := borel_Fv (F := F) (v := v)
  haveI := sigmaFinite_of_isStdV hstd
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  obtain ⟨-, hmap, -, -⟩ := GlobalTheory.T.standard_local_haar_properties F v lam hstd
  have hm := hmap π hπ
  have hN : (Ideal.absNorm v.asIdeal : ℝ≥0∞) = ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.coe_natCast _).symm
  let e : (ι → Fv F v) ≃ᵐ (ι → Fv F v) :=
    MeasurableEquiv.piCongrRight (fun _ : ι => MeasurableEquiv.mulLeft₀ π hπ0)
  have hpre : {y : ι → Fv F v | (fun i => π * y i) ∈ T} = e ⁻¹' T := rfl
  haveI hsf : SigmaFinite (lam.map (fun t => π * t)) := by
    rw [hm, hN]; exact sigmaFinite_nnreal_smul lam _
  have hmapPi : (Measure.pi fun _ : ι => lam).map (fun x i => π * x i) =
      Measure.pi (fun _ : ι => lam.map (fun t => π * t)) :=
    Measure.pi_map_pi (fun _ => (measurable_const_mul π).aemeasurable)
  rw [hpre, ← MeasurableEquiv.map_apply]
  have he : (⇑e : (ι → Fv F v) → ι → Fv F v) = fun x i => π * x i := rfl
  rw [he, hmapPi, hm, hN, pi_const_smul ι lam, Measure.smul_apply, smul_eq_mul]

theorem lam_scale {lam : Measure (Fv F v)} (hstd : IsStdV v lam) {π : Fv F v}
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) {A : Set (Fv F v)} (hA : MeasurableSet A) :
    MeasurableSet {z | π * (π * z) ∈ A} ∧
    lam {z | π * (π * z) ∈ A} = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ 2 * lam A := by
  haveI := borel_Fv (F := F) (v := v)
  have hmeas : Measurable (fun z : Fv F v => π * (π * z)) :=
    (measurable_const_mul π).comp (measurable_const_mul π)
  refine ⟨hmeas hA, ?_⟩
  obtain ⟨-, hmap, -, -⟩ := GlobalTheory.T.standard_local_haar_properties F v lam hstd
  have hm := hmap π hπ
  have h1 : (lam.map (fun t => π * t)).map (fun t => π * t) A = lam {z | π * (π * z) ∈ A} := by
    rw [Measure.map_map (measurable_const_mul π) (measurable_const_mul π), Measure.map_apply ((measurable_const_mul π).comp (measurable_const_mul π)) hA]
    rfl
  rw [← h1, hm, Measure.map_smul, hm, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, sq]

theorem isOpen_unit_sphere : IsOpen {x : Fv F v | Valued.v x = 1} := by
  obtain ⟨π, hπ⟩ := exists_unif v
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hO : IsOpen {x : Fv F v | Valued.v x ≤ 1} := Valued.isOpen_valuationSubring (Fv F v)
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(fun y => π⁻¹ * (y - x)) ⁻¹' {x : Fv F v | Valued.v x ≤ 1}, ?_, ?_, ?_⟩
  · intro y hy
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy hx ⊢
    have h1 : Valued.v (y - x) < Valued.v x := by
      have he : y - x = π * (π⁻¹ * (y - x)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hπ0, one_mul]
      rw [he, map_mul, hπ, hx]
      calc WithZero.exp (-1 : ℤ) * Valued.v (π⁻¹ * (y - x)) ≤ WithZero.exp (-1 : ℤ) * 1 :=
            mul_le_mul_of_nonneg_left hy zero_le
        _ < 1 := by
          rw [mul_one]
          exact (WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)).trans_eq WithZero.exp_zero
    rw [← hx]
    exact Valuation.map_eq_of_sub_lt _ h1
  · exact hO.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  · simp only [Set.mem_preimage, Set.mem_setOf_eq, sub_self, mul_zero, map_zero]
    exact zero_le

theorem meas_prim : MeasurableSet {x : ι → Fv F v | ∃ i, Valued.v (x i) = 1} := by
  haveI := borel_Fv (F := F) (v := v)
  have he : {x : ι → Fv F v | ∃ i, Valued.v (x i) = 1} =
      ⋃ i, (fun x : ι → Fv F v => x i) ⁻¹' {z | Valued.v z = 1} := by
    ext x; simp
  rw [he]
  exact MeasurableSet.iUnion fun i => isOpen_unit_sphere.measurableSet.preimage (measurable_pi_apply i)

theorem val_inv {π : Fv F v} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    Valued.v π⁻¹ = WithZero.exp (1 : ℤ) := by
  rw [map_inv₀, hπ, ← WithZero.exp_neg, neg_neg]

theorem pi_ne_zero {π : Fv F v} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) : π ≠ 0 := by
  intro h0
  rw [h0, map_zero] at hπ
  exact WithZero.exp_ne_zero hπ.symm

theorem div_int {π : Fv F v} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) {a : Fv F v}
    (h1 : Valued.v a ≤ 1) (h2 : Valued.v a ≠ 1) : Valued.v (π⁻¹ * a) ≤ 1 := by
  have hlt : Valued.v a < 1 := lt_of_le_of_ne h1 h2
  have hle := le_exp_of_lt_one hlt
  rw [map_mul, val_inv hπ]
  calc WithZero.exp (1 : ℤ) * Valued.v a ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) :=
        mul_le_mul_of_nonneg_left hle zero_le
    _ = 1 := by rw [← WithZero.exp_add]; simp

theorem pi_mul_lt {π : Fv F v} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) {a : Fv F v}
    (h1 : Valued.v a ≤ 1) : Valued.v (π * a) < 1 := by
  rw [map_mul, hπ]
  calc WithZero.exp (-1 : ℤ) * Valued.v a ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul_of_nonneg_left h1 zero_le
    _ < 1 := by
      rw [mul_one]
      exact (WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)).trans_eq WithZero.exp_zero

theorem val_pp {π : Fv F v} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) (a : Fv F v) :
    Valued.v (π * (π * a)) = WithZero.exp (-2 : ℤ) * Valued.v a := by
  rw [map_mul, map_mul, hπ, ← mul_assoc, ← WithZero.exp_add]
  norm_num

theorem q_nonprim (h2 : Valued.v (2 : Fv F v) = 1) {B : Matrix ι ι (Fv F v)}
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F) {π : Fv F v}
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) {x : ι → Fv F v}
    (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) (hnp : ¬ ∃ i, Valued.v (x i) = 1) :
    Valued.v ((2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x))) ≤ WithZero.exp (-2 : ℤ) := by
  have hlt : ∀ i, Valued.v (x i) ≠ 1 := fun i h => hnp ⟨i, h⟩
  obtain ⟨y, hy, rfl⟩ : ∃ y : ι → Fv F v, (∀ i, y i ∈ v.adicCompletionIntegers F) ∧
      x = fun i => π * y i :=
    ⟨fun i => π⁻¹ * x i, fun i => div_int hπ (hx i) (hlt i), by
      funext i; rw [← mul_assoc, mul_inv_cancel₀ (pi_ne_zero hπ), one_mul]⟩
  rw [q_smul, val_pp hπ]
  calc WithZero.exp (-2 : ℤ) * Valued.v ((2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)))
      ≤ WithZero.exp (-2 : ℤ) * 1 := mul_le_mul_of_nonneg_left (q_int h2 hB hy) zero_le
    _ = WithZero.exp (-2 : ℤ) := mul_one _

theorem bound_step {q : ℝ} {M : ℕ} (hq : 2 ≤ q) (hM : 3 ≤ M) {Dp D' : ℝ}
    (hD' : |D' - 1| ≤ 2 / q ^ (M - 1))
    (hDp : |Dp - 1| ≤ 1 / q ^ (M - 1) + 1 / q ^ (2 * M - 1)) :
    |Dp + q ^ 2 / q ^ (2 * M) * D' - 1| ≤ 2 / q ^ (M - 1) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 3 := ⟨M - 3, by omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e2 : 2 * (k + 3) - 1 = 2 * (k + 2) + 1 := by omega
  have e3 : 2 * (k + 3) = 2 * (k + 2) + 2 := by omega
  rw [e1] at hD' hDp ⊢
  rw [e2] at hDp
  rw [e3]
  have f1 : q ^ (2 * (k + 2) + 1) = (q ^ (k + 2)) ^ 2 * q := by rw [pow_succ, pow_mul']
  have f2 : q ^ (2 * (k + 2) + 2) = (q ^ (k + 2)) ^ 2 * q ^ 2 := by rw [pow_add, pow_mul']
  rw [f1] at hDp
  rw [f2]
  have ht4 : 4 ≤ q ^ (k + 2) := by
    have h1 : q ^ 2 ≤ q ^ (k + 2) := pow_le_pow_right₀ (by linarith) (by omega)
    nlinarith
  generalize q ^ (k + 2) = t at ht4 hD' hDp ⊢
  have htpos : 0 < t := by linarith
  have hqr : q ^ 2 / (t ^ 2 * q ^ 2) * D' = (1 / t) ^ 2 * D' := by
    field_simp
  have hf1 : 1 / (t ^ 2 * q) = (1 / t) ^ 2 * (1 / q) := by field_simp
  have hf2 : 2 / t = 2 * (1 / t) := by ring
  rw [hqr, hf2]
  rw [hf2] at hD'
  rw [hf1] at hDp
  have hu0 : 0 < 1 / t := by positivity
  have hu4 : 1 / t ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) ht4
  have hr0 : 0 < 1 / q := by positivity
  have hr2 : 1 / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq
  generalize 1 / t = u at hu0 hu4 hD' hDp ⊢
  generalize 1 / q = r at hr0 hr2 hDp
  rw [abs_le] at hD' hDp ⊢
  obtain ⟨hb1, hb2⟩ := hD'
  obtain ⟨ha1, ha2⟩ := hDp
  have p1 := mul_le_mul_of_nonneg_left hb2 (sq_nonneg u)
  have p2 := mul_le_mul_of_nonneg_left hb1 (sq_nonneg u)
  have p3 := mul_le_mul_of_nonneg_left hr2 (sq_nonneg u)
  have p4 := mul_le_mul_of_nonneg_left hu4 hu0.le
  have p5 := mul_le_mul_of_nonneg_left hu4 (sq_nonneg u)
  have p6 := mul_nonneg (sq_nonneg u) hr0.le
  constructor <;> nlinarith

theorem local_quadratic_density_bound_at_level {lam : Measure (Fv F v)} (hstd : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1)
    [DecidableEq ι] (B : Matrix ι ι (Fv F v)) (hsym : B.IsSymm)
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F) (hdet : Valued.v B.det = 1)
    (M : ℕ) (hc : Fintype.card ι = 2 * M) (hM : 3 ≤ M) (n : ℕ) :
    ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 → WithZero.exp (-(n : ℤ)) ≤ Valued.v s →
      ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) ∧
        ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < Valued.v s} →
          (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
            (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  haveI := borel_Fv (F := F) (v := v)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs hs0 hsn
  obtain ⟨π, hπ⟩ := exists_unif v
  have hπ0 : π ≠ 0 := pi_ne_zero hπ
  have hN1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hq2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    have : 2 ≤ Ideal.absNorm v.asIdeal := by omega
    exact_mod_cast this
  obtain ⟨Dp, hDpb, hP⟩ := GlobalTheory.T.local_quadratic_density_near_one F v lam hstd h2 ι B hsym hB hdet M hc (by omega) s hs
  have hvs0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).mpr hs0
  have hL : Valued.v s = WithZero.exp (WithZero.log (Valued.v s)) := (WithZero.exp_log hvs0).symm
  have hLn : -(n : ℤ) ≤ WithZero.log (Valued.v s) := by
    have h := hsn
    rw [hL, WithZero.exp_le_exp] at h
    exact h
  have hvs1 : Valued.v s ≤ 1 := hs
  have hmeasPrim : MeasurableSet {x : ι → Fv F v | ∃ i, Valued.v (x i) = 1} := meas_prim
  have hinter : ∀ A : Set (Fv F v),
      {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} ∩
        {x | ∃ i, Valued.v (x i) = 1} =
      {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (∃ i, Valued.v (x i) = 1) ∧
        (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} := by
    intro A
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  have hsplit : ∀ A : Set (Fv F v),
      (Measure.pi fun _ : ι => lam)
        {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} =
      (Measure.pi fun _ : ι => lam)
        ({x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} ∩
          {x | ∃ i, Valued.v (x i) = 1}) +
      (Measure.pi fun _ : ι => lam)
        ({x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} \
          {x | ∃ i, Valued.v (x i) = 1}) :=
    fun A => (measure_inter_add_diff _ hmeasPrim).symm
  rcases le_or_gt (-1 : ℤ) (WithZero.log (Valued.v s)) with hbig | hsmall
  · refine ⟨Dp, ?_, fun A hA hA' => ?_⟩
    · have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have hpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) := by positivity
      have h1 : 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) :=
        one_div_le_one_div_of_le hpos hpow
      have h2' : 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) =
          1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) + 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) := by ring
      rw [h2']
      linarith
    · have hsub1 : A ⊆ {z | Valued.v (z - s) < 1} := fun z hz => lt_of_lt_of_le (hA' hz) hvs1
      have hempty : {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} \ {x | ∃ i, Valued.v (x i) = 1} = ∅ := by
        refine Set.subset_empty_iff.mp (fun x hx => ?_)
        obtain ⟨⟨hint, hQ⟩, hnp⟩ := hx
        have hle := q_nonprim h2 hB hπ hint hnp
        have heq : Valued.v ((2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x))) = Valued.v s :=
          Valuation.map_eq_of_sub_lt _ (hA' hQ)
        rw [heq, hL, WithZero.exp_le_exp] at hle
        exact absurd hle (by omega)
      rw [hsplit A, hempty, measure_empty, add_zero, hinter A, hP A hA hsub1]
  · obtain ⟨s', hss⟩ : ∃ s' : Fv F v, π * (π * s') = s :=
      ⟨π⁻¹ * (π⁻¹ * s), by rw [mul_inv_cancel_left₀ hπ0, mul_inv_cancel_left₀ hπ0]⟩
    have hrel : Valued.v s = WithZero.exp (-2 : ℤ) * Valued.v s' := by rw [← hss, val_pp hπ]
    have hvs'0 : Valued.v s' ≠ 0 := by
      intro h0
      apply hvs0
      rw [hrel, h0, mul_zero]
    have hL' : Valued.v s' = WithZero.exp (WithZero.log (Valued.v s')) := (WithZero.exp_log hvs'0).symm
    have hLL : WithZero.log (Valued.v s) = -2 + WithZero.log (Valued.v s') := by
      have h := hrel
      rw [hL, hL', ← WithZero.exp_add] at h
      have h1 := WithZero.exp_le_exp.mp h.le
      have h2'' := WithZero.exp_le_exp.mp h.ge
      omega
    have hs'int : s' ∈ v.adicCompletionIntegers F := by
      show Valued.v s' ≤ 1
      rw [hL']
      exact (WithZero.exp_le_exp.mpr (by omega : WithZero.log (Valued.v s') ≤ 0)).trans_eq WithZero.exp_zero
    have hs'0 : s' ≠ 0 := (Valuation.ne_zero_iff _).mp hvs'0
    have hn2 : 2 ≤ n := by omega
    have hs'n : WithZero.exp (-((n - 2 : ℕ) : ℤ)) ≤ Valued.v s' := by
      rw [hL', WithZero.exp_le_exp]
      omega
    obtain ⟨D', hD'b, hD'P⟩ := ih (n - 2) (by omega) s' hs'int hs'0 hs'n
    set K : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (2 * M) with hK
    have hK0 : K ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN0)
    set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ 2 / K with hc'
    have hcK : K * c = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ 2 := by
      rw [hc', mul_div_assoc', mul_div_cancel_left₀ _ hK0]
    refine ⟨Dp + c * D', ?_, fun A hA hA' => ?_⟩
    · have hcast : ((Dp + c * D' : ℝ≥0) : ℝ) =
          (Dp : ℝ) + (Ideal.absNorm v.asIdeal : ℝ) ^ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M) * (D' : ℝ) := by
        rw [hc', hK]
        push_cast
        ring
      rw [hcast]
      exact bound_step hq2 hM hD'b hDpb
    · have hsub1 : A ⊆ {z | Valued.v (z - s) < 1} := fun z hz => lt_of_lt_of_le (hA' hz) hvs1
      obtain ⟨hA'meas, hlamA'⟩ := lam_scale hstd hπ hA
      have hA'sub : {z | π * (π * z) ∈ A} ⊆ {z | Valued.v (z - s') < Valued.v s'} := by
        intro z hz
        have h := hA' hz
        simp only [Set.mem_setOf_eq] at h ⊢
        have he : π * (π * z) - s = π * (π * (z - s')) := by rw [← hss]; ring
        rw [he, val_pp hπ, hrel] at h
        by_contra hcon
        have := mul_le_mul_of_nonneg_left (not_lt.mp hcon) (zero_le : (0 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-2 : ℤ))
        exact absurd h (not_lt.mpr this)
      have hD'A := hD'P _ hA'meas hA'sub
      have hset : {y : ι → Fv F v | (fun i => π * y i) ∈
          ({x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} \
            {x | ∃ i, Valued.v (x i) = 1})} =
          {y | (∀ i, y i ∈ v.adicCompletionIntegers F) ∧
            (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ {z | π * (π * z) ∈ A}} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_diff]
        constructor
        · rintro ⟨⟨hint, hQ⟩, hnp⟩
          refine ⟨fun i => ?_, ?_⟩
          · have h1 : Valued.v (π * y i) ≤ 1 := hint i
            have h2' : Valued.v (π * y i) ≠ 1 := fun h => hnp ⟨i, h⟩
            have h3 := div_int hπ h1 h2'
            rwa [← mul_assoc, inv_mul_cancel₀ hπ0, one_mul] at h3
          · rw [← q_smul]
            exact hQ
        · rintro ⟨hyint, hQ⟩
          refine ⟨⟨fun i => (pi_mul_lt hπ (hyint i)).le, ?_⟩, ?_⟩
          · rw [q_smul]
            exact hQ
          · rintro ⟨i, hi⟩
            exact absurd hi (pi_mul_lt hπ (hyint i)).ne
      have hscale := pi_scale hstd hπ
        ({x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} \
          {x | ∃ i, Valued.v (x i) = 1})
      rw [hset, hD'A, hlamA', hc] at hscale
      have hKe : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (2 * M) = (K : ℝ≥0∞) := by
        rw [hK]; push_cast; rfl
      rw [hKe] at hscale
      have hnp : (Measure.pi fun _ : ι => lam)
          ({x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} \
            {x | ∃ i, Valued.v (x i) = 1}) = ((c * D' : ℝ≥0) : ℝ≥0∞) * lam A := by
        apply (ENNReal.mul_right_inj (a := (K : ℝ≥0∞)) (by exact_mod_cast hK0) ENNReal.coe_ne_top).mp
        rw [← hscale, ← mul_assoc (K : ℝ≥0∞), ← ENNReal.coe_mul, ← mul_assoc K c D', hcK]
        push_cast
        ring
      rw [hsplit A, hnp, hinter A, hP A hA hsub1]
      push_cast
      ring

theorem density_near_value : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ M : ℕ, Fintype.card ι = 2 * M → 3 ≤ M → ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 → ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) ∧ ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < Valued.v s} → (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  intro F _ _ v lam hstd h2 ι _ _ B hsym hB hdet M hc hM s hs hs0
  have hvs0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).mpr hs0
  have hL : Valued.v s = WithZero.exp (WithZero.log (Valued.v s)) := (WithZero.exp_log hvs0).symm
  have hle : WithZero.log (Valued.v s) ≤ 0 := by
    have h1 : WithZero.exp (WithZero.log (Valued.v s)) ≤ WithZero.exp (0 : ℤ) := by
      rw [← hL, WithZero.exp_zero]; exact hs
    exact WithZero.exp_le_exp.mp h1
  refine local_quadratic_density_bound_at_level hstd h2 B hsym hB hdet M hc hM (WithZero.log (Valued.v s)).natAbs s hs hs0 ?_
  rw [hL, WithZero.exp_le_exp, WithZero.log_exp]
  omega

end GlobalTheory.CompanionTheory.SW.GBall
