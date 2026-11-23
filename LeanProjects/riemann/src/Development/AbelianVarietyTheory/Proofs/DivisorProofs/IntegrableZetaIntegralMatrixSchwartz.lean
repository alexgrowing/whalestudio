import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableDetPowIndicatorIntegerGlStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJIntegrable

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unit_bound {m : ℕ} {K : Set (Matrix (Fin m) (Fin m) k)} (hK : IsCompact K) :
    ∃ c : kˣ, ∀ X ∈ K, ∀ i j, valuation k (X i j) ≤ valuation k (c : k) := by
  obtain ⟨y, hy⟩ := hK.elim_directed_cover
    (fun y : kˣ => {X : Matrix (Fin m) (Fin m) k | ∀ i j, X i j ∈ cball y})
    (fun y => by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (isOpen_cball y).preimage ((continuous_apply j).comp (continuous_apply i)))
    (fun X _ => by
      let f : Option (Fin m × Fin m) → k := fun p => match p with
        | none => 1
        | some q => X q.1 q.2
      obtain ⟨p, hp⟩ := Finite.exists_max fun q => valuation k (f q)
      have h1 : valuation k (f p) ≠ 0 := by
        have := hp none
        simp only [f, map_one] at this
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one this)
      have h0 : f p ≠ 0 := fun h => h1 (by rw [h, map_zero])
      exact Set.mem_iUnion.2 ⟨Units.mk0 _ h0, fun i j => by
        show valuation k (X i j) ≤ valuation k (f p)
        exact hp (some (i, j))⟩)
    (fun a b => by
      rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
      · exact ⟨b, fun X hX i j => le_trans (show valuation k (X i j) ≤ _ from hX i j) h, subset_rfl⟩
      · exact ⟨a, subset_rfl, fun X hX i j => le_trans (show valuation k (X i j) ≤ _ from hX i j) h⟩)
  exact ⟨y, fun X hX i j => hy hX i j⟩

theorem isLocallyConstant_char {ν : kˣ →* ℂˣ} (hν : IsOpen (ν.ker : Set kˣ)) :
    IsLocallyConstant fun x : kˣ => ((ν x : ℂˣ) : ℂ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x0 => ?_
  have hn : (fun x => x0⁻¹ * x) ⁻¹' (ν.ker : Set kˣ) ∈ nhds x0 :=
    (hν.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with x hx
  have hx' : ν (x0⁻¹ * x) = 1 := hx
  rw [map_mul, map_inv, inv_mul_eq_one] at hx'
  rw [hx']

theorem nabs_pos_unit (x : kˣ) : 0 < nabs k x := NNReal.coe_pos.mpr distribHaarChar_pos

theorem nabs_pow (x : kˣ) (m : ℕ) : nabs k (x ^ m) = nabs k x ^ m := by
  induction m with
  | zero => simp [nabs]
  | succ m ih => rw [pow_succ, nabs_mul, ih, pow_succ]

theorem integrable_gjIntegrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), Integrable (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (haarVol (KO k (Fin n))) := by
  intro k _ _ _ _ _ _ n ν z hν hz φ hφ
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : MeasurableMul (GL (Fin n) k) := inferInstance
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  obtain ⟨hl, hK⟩ : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  obtain ⟨C, hC⟩ := hl.continuous.bounded_above_of_compact_support hK
  obtain ⟨c, hc⟩ := exists_unit_bound (k := k) hK.isCompact
  set s : GL (Fin n) k := Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom c⁻¹ with hs
  have hsv : ∀ g : GL (Fin n) k, (s * g).val = ((c⁻¹ : kˣ) : k) • g.val := by
    intro g
    simp [hs, Algebra.smul_def]
  have hsd : ∀ g : GL (Fin n) k, gdet g = c ^ n * gdet (s * g) := by
    intro g
    ext
    simp only [gdet, Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, hsv,
      Matrix.det_smul, Fintype.card_fin, ← mul_assoc, ← mul_pow]
    simp
  set T : GL (Fin n) k → ℝ := fun g =>
    (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val * nabs k (gdet g) ^ z.re with hT
  have hTi : Integrable T (haarVol (KO k (Fin n))) := GlobalTheory.T.integrable_det_pow_indicator_integer_gl k n z.re hz
  have hT0 : ∀ g, 0 ≤ T g := fun g =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Real.rpow_nonneg (nabs_pos_unit _).le _)
  set D : ℝ := |C| * (nabs k c ^ n) ^ z.re with hD
  have hcont : Continuous fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z := by
    refine ((hl.continuous.comp Units.continuous_val).mul
      ((isLocallyConstant_char hν.1).continuous.comp GeneralLinearGroup.continuous_det)).mul ?_
    exact (((isLocallyConstant_nabs k).comp fun r : ℝ => (r : ℂ) ^ z).continuous).comp
      GeneralLinearGroup.continuous_det
  refine ((hTi.comp_mul_left s).const_mul D).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := nabs_pos_unit (gdet g)
  have hu : ‖((ν (gdet g) : ℂˣ) : ℂ)‖ = 1 := hν.2 _
  rw [norm_mul, norm_mul, hu, mul_one, apow, Complex.norm_cpow_eq_rpow_re_of_pos hp]
  by_cases h0 : φ g.val = 0
  · rw [h0, norm_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (pow_nonneg (nabs_pos_unit c).le _) _)) (hT0 _)
  have hmem : (s * g).val ∈ intM k (Fin n) (Fin n) := by
    intro i j
    rw [hsv, Matrix.smul_apply, smul_eq_mul, Valuation.mem_integer_iff, map_mul]
    have h1 := hc g.val (subset_tsupport _ h0) i j
    have h2 : valuation k ((c⁻¹ : kˣ) : k) * valuation k (c : k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc valuation k ((c⁻¹ : kˣ) : k) * valuation k (g.val i j)
        ≤ valuation k ((c⁻¹ : kˣ) : k) * valuation k (c : k) := by gcongr
      _ = 1 := h2
  have hTs : T (s * g) = nabs k (gdet (s * g)) ^ z.re := by
    simp only [hT, Set.indicator_of_mem hmem, one_mul]
  show _ ≤ D * T (s * g)
  rw [hTs, hsd g, nabs_mul, nabs_pow, Real.mul_rpow (pow_nonneg (nabs_pos_unit c).le _) (nabs_pos_unit _).le, hD]
  have hq := Real.rpow_nonneg (pow_nonneg (nabs_pos_unit c).le n) z.re
  have hr := Real.rpow_nonneg (nabs_pos_unit (gdet (s * g))).le z.re
  calc ‖φ g.val‖ * ((nabs k c ^ n) ^ z.re * nabs k (gdet (s * g)) ^ z.re)
      ≤ |C| * ((nabs k c ^ n) ^ z.re * nabs k (gdet (s * g)) ^ z.re) :=
        mul_le_mul_of_nonneg_right ((hC _).trans (le_abs_self C)) (mul_nonneg hq hr)
    _ = _ := by ring

end GlobalTheory.GJIntegrable
