import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.SigmaFiniteOfWeight

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem ae_inPair_pair (L : LocBessel k r) : ∀ᵐ p ∂(pairMeas L), InPair L p := by
  haveI := L.hμW.1.1
  haveI := L.hμW'.1.1
  have hW := ae_mem_sk L.hμW.1
  have hW' := ae_mem_sk L.hμW'.1
  have hN : ∀ᵐ x ∂L.μN, of x ∈ Nset k r := ae_mem_haarLieN _
  have h1 : ∀ᵐ p ∂(L.μW.prod L.μN), of p.1 ∈ UWset k r L.z ∧ of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW).and (Measure.quasiMeasurePreserving_snd.ae hN)
  have h2 : ∀ᵐ p ∂(L.μW'.prod L.μN), of p.1 ∈ UWset k r L.z' ∧ of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW').and (Measure.quasiMeasurePreserving_snd.ae hN)
  have h := (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  filter_upwards [h] with p hp
  exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩

theorem ae_inPair_nu (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hμR : IsHaarOn (RStab k r γ) μR)
    (hOQ : IsOrbQuot L γ μR ν) : ∀ᵐ p ∂ν, InPair L p := by
  classical
  have hc : IsClosed {p : PairSp k r | InPair L p} := by
    have hU : IsClosed {x : Mt k r | of x ∈ UWset k r L.z} := Formalism.FourierDecayAlt.P.B6.isClosed_UWset k r L.z
    have hU' : IsClosed {x : Mt k r | of x ∈ UWset k r L.z'} := Formalism.FourierDecayAlt.P.B6.isClosed_UWset k r L.z'
    have hN : IsClosed {x : Mt k r | of x ∈ Nset k r} := Formalism.FourierDecayAlt.P.B6.isClosed_Nset k r
    exact (hU.preimage (continuous_fst.comp continuous_fst)).inter
      ((hN.preimage (continuous_snd.comp continuous_fst)).inter
        ((hU'.preimage (continuous_fst.comp continuous_snd)).inter
          (hN.preimage (continuous_snd.comp continuous_snd))))
  have hB : MeasurableSet {p : PairSp k r | ¬ InPair L p} := hc.measurableSet.compl
  have hpair : pairMeas L {p | ¬ InPair L p} = 0 := ae_iff.mp (ae_inPair_pair L)
  have hq := hOQ _ (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hpair] at hq
  have hR : ∀ᵐ a ∂μR, of a ∈ RStab k r γ := ae_mem_sk hμR
  have hμR0 : μR Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hμR.2.1
  have key : ∀ x ∈ {p : PairSp k r | ¬ InPair L p},
      μR Set.univ ≤ ∫⁻ a, {p : PairSp k r | ¬ InPair L p}.indicator 1 (stabAct γ (of a) x) ∂μR := by
    intro x hx
    calc μR Set.univ = ∫⁻ _a, (1 : ℝ≥0∞) ∂μR := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hR] with a ha
        have hm : stabAct γ (of a) x ∈ {p : PairSp k r | ¬ InPair L p} :=
          fun h => hx (inPair_of_stab L ha h)
        simp [Set.indicator_of_mem hm]
  have h2 : ∫⁻ x, {p : PairSp k r | ¬ InPair L p}.indicator (fun _ => μR Set.univ) x ∂ν = 0 := by
    apply le_antisymm ?_ zero_le
    rw [hq]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ {p : PairSp k r | ¬ InPair L p}
    · rw [Set.indicator_of_mem hx]
      exact key x hx
    · simp only [Set.indicator, hx, if_false]
      exact zero_le
  rw [lintegral_indicator_const hB] at h2
  rw [ae_iff]
  exact (mul_eq_zero.mp h2).resolve_left hμR0

theorem ae_uh_nuR {μG : Measure (Mt k r)} {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μR νR : Measure (Mt k r)} (hγ : γ ∈ UH (Hpk k r)) (hμG : IsHaarOn (UH (Hpk k r)) μG)
    (hμR : IsHaarOn (RStab k r γ) μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR) :
    ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r) := by
  classical
  have hUH : IsClosed {x : Mt k r | of x ∈ UH (Hpk k r)} := Formalism.MainNotions.LowestKTypeMultiplicity.isClosed_UH k r
  have hB : MeasurableSet {x : Mt k r | of x ∉ UH (Hpk k r)} := hUH.measurableSet.compl
  have hG : μG {x : Mt k r | of x ∉ UH (Hpk k r)} = 0 := ae_iff.mp (ae_mem_sk hμG)
  have hq := hQ _ (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hG] at hq
  have hFc : Continuous (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact ((continuous_const.matrix_mul (continuous_id : Continuous fun x : Mt k r => x)).matrix_mul
      continuous_const).matrix_elem i j
  have hS : ∀ᵐ s ∂(μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)),
      of s ∈ UH (Hpk k r) := by
    rw [ae_map_iff hFc.measurable.aemeasurable hUH.measurableSet]
    filter_upwards [ae_mem_sk hμR] with a ha
    exact ha.2.1
  have hμ0 : (μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) Set.univ ≠ 0 := by
    rw [Measure.map_apply hFc.measurable MeasurableSet.univ, Set.preimage_univ]
    exact Measure.measure_univ_ne_zero.mpr hμR.2.1
  have mulUH : ∀ s x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      s ∈ UH (Hpk k r) → s * x ∈ UH (Hpk k r) → x ∈ UH (Hpk k r) := by
    intro s x hs hsx
    simp only [UH, Set.mem_setOf_eq] at hs hsx ⊢
    rw [Matrix.conjTranspose_mul] at hsx
    calc xᴴ * Hpk k r * x = xᴴ * (sᴴ * Hpk k r * s) * x := by rw [hs]
      _ = xᴴ * sᴴ * Hpk k r * (s * x) := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := hsx
  have key : ∀ x ∈ {x : Mt k r | of x ∉ UH (Hpk k r)},
      (μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) Set.univ ≤
        ∫⁻ s, {x : Mt k r | of x ∉ UH (Hpk k r)}.indicator 1 (fun i j => (of s * of x) i j)
          ∂(μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) := by
    intro x hx
    calc _ = ∫⁻ _s, (1 : ℝ≥0∞) ∂(μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hS] with s hs
        have hm : (fun i j => (of s * of x) i j : Mt k r) ∈ {x : Mt k r | of x ∉ UH (Hpk k r)} :=
          fun h => hx (mulUH _ _ hs h)
        simp [Set.indicator_of_mem hm]
  have h2 : ∫⁻ x, {x : Mt k r | of x ∉ UH (Hpk k r)}.indicator
      (fun _ => (μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) Set.univ) x ∂νR = 0 := by
    apply le_antisymm ?_ zero_le
    rw [hq]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ {x : Mt k r | of x ∉ UH (Hpk k r)}
    · rw [Set.indicator_of_mem hx]
      exact key x hx
    · simp only [Set.indicator, hx, if_false]
      exact zero_le
  rw [lintegral_indicator_const hB] at h2
  rw [ae_iff]
  exact (mul_eq_zero.mp h2).resolve_left hμ0

end Formalism.MainNotions.S.Pv.AmpDDPf
