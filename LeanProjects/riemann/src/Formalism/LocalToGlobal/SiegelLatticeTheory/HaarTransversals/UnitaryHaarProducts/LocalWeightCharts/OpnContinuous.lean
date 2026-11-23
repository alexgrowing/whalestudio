import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Matrix
open scoped ENNReal

namespace WlocSk

abbrev CSp (m d : ℕ) := (Fin m → ℂ) × (Fin d → ℝ)

instance instAddHaarCSp (m d : ℕ) : (volume : Measure (CSp m d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

def NCoordHaar : Prop :=
  ∀ (k r : ℕ) (μN : Measure (Formalism.QuantumDeterminants.Mt k r)), IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μN K < ⊤) →
    ∃ (m d q : ℕ) (Φ : CSp m d → Formalism.QuantumDeterminants.Mt k r) (c : ℝ≥0∞) (κ : ℝ),
      1 ≤ q ∧ ((q * (2 * m + d) : ℕ) : ℝ) < N1H k r ∧ 0 < κ ∧ c ≠ ⊤ ∧ Measurable Φ ∧
      μN = c • (volume : Measure (CSp m d)).map Φ ∧
      ∀ t, 1 + ‖t‖ ≤ κ * Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ q

def NChart : Prop :=
  ∀ (k r : ℕ), ∃ (m d q : ℕ) (Φ : CSp m d → Formalism.QuantumDeterminants.Mt k r) (κ : ℝ),
    1 ≤ q ∧ ((q * (2 * m + d) : ℕ) : ℝ) < N1H k r ∧ 0 < κ ∧ MeasurableEmbedding Φ ∧
    Set.range Φ = {x | Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r} ∧
    (∀ m₀ ∈ Formalism.QuantumDeterminants.Nset k r, ∃ T : CSp m d → CSp m d, MeasurePreserving T volume volume ∧
      ∀ t, Formalism.QuantumDeterminants.lmulM m₀ (Φ t) = Φ (T t)) ∧
    ∀ t, 1 + ‖t‖ ≤ κ * Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ q

def NUniq : Prop :=
  ∀ (k r : ℕ) (μ μ' : Measure (Formalism.QuantumDeterminants.Mt k r)), IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ →
    IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ' → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ μ = c • μ'

theorem nCoordHaar_of (hC : NChart) (hU : NUniq) : NCoordHaar := by
  intro k r μN hN _
  obtain ⟨m, d, q, Φ, κ, hq, hD, hκ, hΦ, hrange, hT, hgrow⟩ := hC k r
  have hmeasL : ∀ a : Mat k r, Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := fun a => by
    have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := by
      unfold Formalism.QuantumDeterminants.lmulM
      exact continuous_const.matrix_mul continuous_id
    exact this.measurable
  have hH : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) ((volume : Measure (CSp m d)).map Φ) := by
    refine ⟨hΦ.sigmaFinite_map, ?_, ?_, ?_⟩
    · intro h0
      rw [Measure.map_eq_zero_iff hΦ.measurable.aemeasurable] at h0
      exact isOpen_univ.measure_ne_zero (volume : Measure (CSp m d)) Set.univ_nonempty
        (by rw [h0, Measure.coe_zero, Pi.zero_apply])
    · rw [Measure.map_apply hΦ.measurable]
      · have : Φ ⁻¹' {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r} = ∅ := by
          ext t
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
          have : Φ t ∈ Set.range Φ := ⟨t, rfl⟩
          rw [hrange] at this
          exact this
        rw [this, measure_empty]
      · have hcl : MeasurableSet (Set.range Φ) := hΦ.measurableSet_range
        rw [hrange] at hcl
        exact hcl.compl
    · intro s hs
      obtain ⟨T, hTm, hTe⟩ := hT s hs
      rw [Measure.map_map (hmeasL s) hΦ.measurable]
      have : Formalism.QuantumDeterminants.lmulM s ∘ Φ = Φ ∘ T := funext hTe
      rw [this, ← Measure.map_map hΦ.measurable hTm.measurable, hTm.map_eq]
  obtain ⟨c, hc, hμ⟩ := hU k r μN _ hN hH
  exact ⟨m, d, q, Φ, c, κ, hq, hD, hκ, hc, hΦ.measurable, hμ, hgrow⟩

local instance instAlgCLM (n : ℕ) :
    Algebra ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.algebra
local instance instModCLM (n : ℕ) :
    Module ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.module

lemma opn_continuous (k r : ℕ) :
    Continuous fun m : Formalism.QuantumDeterminants.Mt k r => Formalism.L2.SG.WuDecay.opn (Matrix.of m) := by
  unfold Formalism.L2.SG.WuDecay.opn
  have : Continuous fun m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 * r + k + 1)) m := by
    let L : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℂ]
        (EuclideanSpace ℂ (Fin (2 * r + k + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1))) :=
      { toFun := fun m => Matrix.toEuclideanCLM (𝕜 := ℂ) m
        map_add' := fun a b => map_add _ a b
        map_smul' := fun a b => map_smul _ a b }
    exact L.continuous_of_finiteDimensional
  exact continuous_norm.comp (this.comp continuous_id)

lemma finrank_CSp (m d : ℕ) : Module.finrank ℝ (CSp m d) = 2 * m + d := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_fin_fun]
  simp [Complex.finrank_real_complex, mul_comm]

theorem nIntDecay_of (h : NCoordHaar) : NIntDecay := by
  intro k r μN hN hNc
  obtain ⟨m, d, q, Φ, c, κ, hq, hD, hκ, hc, hΦ, hμ, hgrow⟩ := h k r μN hN hNc
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hD' : (Module.finrank ℝ (CSp m d) : ℝ) < N1H k r / q := by
    rw [finrank_CSp, lt_div_iff₀ hq0, mul_comm]; exact_mod_cast hD
  have hF : Measurable fun x : Formalism.QuantumDeterminants.Mt k r =>
      ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (Matrix.of x) ^ (-N1H k r)) :=
    ENNReal.measurable_ofReal.comp ((opn_continuous k r).measurable.pow_const _)
  rw [hμ, lintegral_smul_measure, lintegral_map hF hΦ]
  refine ENNReal.mul_lt_top hc.lt_top ?_
  set s := N1H k r / q with hs
  have hbound : ∀ t : CSp m d,
      ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ (-N1H k r)) ≤
        ENNReal.ofReal (κ ^ s) * ENNReal.ofReal ((1 + ‖t‖) ^ (-s)) := by
    intro t
    set o := Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) with ho
    have ho0 : 0 ≤ o := norm_nonneg _
    have h1 : 0 < 1 + ‖t‖ := by positivity
    have h2 : (1 + ‖t‖) / κ ≤ o ^ q := by
      rw [div_le_iff₀ hκ, mul_comm]; exact hgrow t
    have h3 : 0 < (1 + ‖t‖) / κ := div_pos h1 hκ
    have hoq : o ^ (-N1H k r) = (o ^ q) ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ho0, hs]
      congr 1
      field_simp
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hoq]
    calc (o ^ q) ^ (-s)
        ≤ ((1 + ‖t‖) / κ) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos h3 h2 (by
            have : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg _) hD'
            linarith)
      _ = κ ^ s * (1 + ‖t‖) ^ (-s) := by
          rw [Real.div_rpow h1.le hκ.le, div_eq_mul_inv, ← Real.rpow_neg hκ.le, neg_neg, mul_comm]
  calc ∫⁻ t, ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ (-N1H k r))
      ≤ ∫⁻ t : CSp m d, ENNReal.ofReal (κ ^ s) *
          ENNReal.ofReal ((1 + ‖t‖) ^ (-s)) := lintegral_mono hbound
    _ = ENNReal.ofReal (κ ^ s) *
          ∫⁻ t : CSp m d, ENNReal.ofReal ((1 + ‖t‖) ^ (-s)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (finite_integral_one_add_norm hD')

end WlocSk
