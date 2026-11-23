import Mathlib
import GroundTheory.AutomorphicForms.ReductionLocalVolumeGL

open MeasureTheory Measure Set Matrix
open scoped NNReal ENNReal
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace PositivityTheory.Rg.Rs.boxvol

variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ}

def pairSum (m : ℕ) (x : Fin (m + 1) → ℝ) : ℝ :=
  ∑ p : StrictUpperIndex (Fin (m + 1)), (x p.1.1 - x p.1.2)

def boxGL (ω : Set (GL (Fin (m + 1)) 𝕜)) (B : ℝ) (x : Fin (m + 1) → ℝ) : Set (GL (Fin (m + 1)) 𝕜) :=
  {g | ∃ b ∈ ω, ∃ y : Fin (m + 1) → ℝ, (∀ i, |y i| ≤ B) ∧ ∃ k : unitaryGroup (Fin (m + 1)) 𝕜,
    g = b * (diagPosOf ⟨fun i => Real.exp (x i + y i), fun _ => Real.exp_pos _⟩ : GL (Fin (m + 1)) 𝕜) *
      Unitary.toUnits k}

theorem measure_boxGL_le [MeasurableSpace (GL (Fin (m + 1)) 𝕜)] [BorelSpace (GL (Fin (m + 1)) 𝕜)]
    [MeasurableSpace (unitaryGroup (Fin (m + 1)) 𝕜)] [BorelSpace (unitaryGroup (Fin (m + 1)) 𝕜)]
    (μ : Measure (GL (Fin (m + 1)) 𝕜))
    (hANK : ∀ (μK : Measure (unitaryGroup (Fin (m + 1)) 𝕜)) [μK.IsHaarMeasure]
      (μA : Measure (diagPosSubgroup (Fin (m + 1)) 𝕜)) [μA.IsHaarMeasure]
      (μN : Measure (upperUnipotentSubgroup (Fin (m + 1)) 𝕜)) [μN.IsHaarMeasure],
      ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞, Measurable f →
        ∫⁻ g, f g ∂μ = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA)
    {ω : Set (GL (Fin (m + 1)) 𝕜)} (hω : IsCompact ω)
    (hωB : ∀ b ∈ ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).IsUpperTriangular) (B : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x : Fin (m + 1) → ℝ,
      μ (boxGL ω B x) ≤ C * ENNReal.ofReal (Real.exp (-((Module.finrank ℝ 𝕜 : ℝ) * pairSum m x))) := by
  classical
  set e : ℝ := (Module.finrank ℝ 𝕜 : ℝ) with he
  have he0 : 0 ≤ e := Nat.cast_nonneg _
  have hent : ∀ i j, Continuous fun g : GL (Fin (m + 1)) 𝕜 =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i j := fun i j =>
    (continuous_apply_apply i j).comp (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜))
  have hb0 : ∀ b ∈ ω, ∀ i, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i ≠ 0 := fun b hb i =>
    apply_self_ne_zero_of_isUpperTriangular (hωB b hb) i

  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, ∀ b ∈ ω, ∀ i,
      |Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖| ≤ B₀ := by
    have hcont : ContinuousOn (fun b : GL (Fin (m + 1)) 𝕜 => ∑ i,
        |Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖|) ω :=
      continuousOn_finsetSum _ fun i _ => ((hent i i).norm.continuousOn.log
        fun b hb => norm_ne_zero_iff.2 (hb0 b hb i)).abs
    obtain ⟨M, hM⟩ := hω.exists_bound_of_continuousOn hcont
    refine ⟨M, fun b hb i => ?_⟩
    calc _ ≤ ∑ i, |Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖| :=
          Finset.single_le_sum (f := fun i => |Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ M := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM b hb)
  set L : ℝ := B₀ + B with hL

  set Vset : Set (StrictUpperIndex (Fin (m + 1)) → 𝕜) :=
    (fun b : GL (Fin (m + 1)) 𝕜 => unipotentPart (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜)) '' ω
    with hVset
  have hVc : IsCompact Vset := hω.image_of_continuousOn (continuousOn_pi.2 fun p =>
    ContinuousOn.div (hent _ _).continuousOn (hent _ _).continuousOn fun b hb => hb0 b hb _)
  set Nc : Set (upperUnipotentSubgroup (Fin (m + 1)) 𝕜) := unipotentCoordsHomeomorph '' Vset
    with hNc
  have hNcc : IsCompact Nc := hVc.image unipotentCoordsHomeomorph.continuous
  have hNcm : MeasurableSet Nc := hNcc.isClosed.measurableSet

  set μK : Measure (unitaryGroup (Fin (m + 1)) 𝕜) := Measure.haar with hμK
  set μN : Measure (upperUnipotentSubgroup (Fin (m + 1)) 𝕜) := Measure.haar with hμN
  haveI := isHaarMeasure_map_expDiag (𝕜 := 𝕜) (m := m)
  set μA : Measure (diagPosSubgroup (Fin (m + 1)) 𝕜) :=
    Measure.map (expDiag 𝕜 m) (volume : Measure (Fin (m + 1) → ℝ)) with hμA
  obtain ⟨c, -, hc⟩ := hANK μK μA μN
  set P : ℝ := (Fintype.card (StrictUpperIndex (Fin (m + 1))) : ℝ) with hP
  set V : ℝ≥0∞ := ∏ _i : Fin (m + 1), ENNReal.ofReal (2 * L) with hV
  refine ⟨(c : ℝ≥0∞) * (μK univ * μN Nc) * (ENNReal.ofReal (Real.exp (e * (2 * L * P))) * V), ?_, fun x => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top
      (measure_ne_top μK univ) hNcc.measure_lt_top.ne)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top))

  set box : Set (Fin (m + 1) → ℝ) := Set.Icc (x - fun _ => L) (x + fun _ => L) with hbox
  set R : Set (diagPosSubgroup (Fin (m + 1)) 𝕜) := expDiag 𝕜 m '' box with hR
  have hRm : MeasurableSet R := ((expDiag 𝕜 m).isClosed_image.2 isClosed_Icc).measurableSet
  have hSc : IsCompact (boxGL ω B x) := by
    have : boxGL ω B x = (fun p : GL (Fin (m + 1)) 𝕜 × (Fin (m + 1) → ℝ) × unitaryGroup (Fin (m + 1)) 𝕜 =>
        p.1 * ((expDiag 𝕜 m (x + p.2.1) : diagPosSubgroup (Fin (m + 1)) 𝕜) : GL (Fin (m + 1)) 𝕜) *
          Unitary.toUnits p.2.2) '' (ω ×ˢ (Set.univ.pi fun _ => Set.Icc (-B) B) ×ˢ Set.univ) := by
      ext g
      constructor
      · rintro ⟨b, hb, y, hy, k, rfl⟩
        exact ⟨(b, y, k), ⟨hb, fun i _ => abs_le.1 (hy i), Set.mem_univ _⟩, rfl⟩
      · rintro ⟨⟨b, y, k⟩, ⟨hb, hy, -⟩, rfl⟩
        exact ⟨b, hb, y, fun i => abs_le.2 (hy i (Set.mem_univ i)), k, rfl⟩
    rw [this]
    refine (hω.prod ((isCompact_univ_pi fun _ => isCompact_Icc).prod isCompact_univ)).image ?_
    exact (continuous_fst.mul (continuous_subtype_val.comp ((expDiag 𝕜 m).continuous.comp
      (continuous_const.add (continuous_fst.comp continuous_snd))))).mul
      (continuous_unitary_toUnits.comp (continuous_snd.comp continuous_snd))
  have hSm : MeasurableSet (boxGL ω B x) := hSc.isClosed.measurableSet

  have hpt : ∀ (a : diagPosSubgroup (Fin (m + 1)) 𝕜) (u : upperUnipotentSubgroup (Fin (m + 1)) 𝕜)
      (k : unitaryGroup (Fin (m + 1)) 𝕜),
      (boxGL ω B x).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
        ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ≤
        R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a *
          Nc.indicator (1 : upperUnipotentSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) (diagConj a u) := by
    intro a u k
    by_cases hS : (a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k ∈ boxGL ω B x
    swap
    · rw [indicator_of_notMem hS]; exact zero_le
    obtain ⟨b, hbω, y, hy, k₀, hg⟩ := hS
    obtain ⟨a', u', k', heq', hdiag', hconj'⟩ :=
      exists_ANK_of_siegel (hωB b hbω) ⟨fun i => Real.exp (x i + y i), fun i => Real.exp_pos _⟩ k₀
    obtain ⟨rfl, rfl⟩ := ANK_unique (hg.trans heq')
    have haR : a ∈ R := by
      refine ⟨fun i => Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖ + (x i + y i),
        ⟨fun i => ?_, fun i => ?_⟩, ?_⟩
      · have h1 := abs_le.1 (hB₀ b hbω i); have h2 := abs_le.1 (hy i)
        simp only [Pi.sub_apply]; linarith
      · have h1 := abs_le.1 (hB₀ b hbω i); have h2 := abs_le.1 (hy i)
        simp only [Pi.add_apply]; linarith
      · apply Subtype.ext
        apply Units.ext
        rw [coe_expDiag, coe_diagPosOf, eq_diagonal_of_mem_diagPos a.2]
        congr 1
        funext i
        rw [hdiag' i, RCLike.ofReal_re]
        congr 1
        exact (by rw [Real.exp_add, Real.exp_log (norm_pos_iff.2 (hb0 b hbω i))] :
          Real.exp (Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖ + (x i + y i)) =
            ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖ * Real.exp (x i + y i))
    have hnc : diagConj a u ∈ Nc := by
      rw [hconj']
      exact ⟨_, ⟨b, hbω, rfl⟩, rfl⟩
    rw [indicator_of_mem (show _ ∈ boxGL ω B x from ⟨b, hbω, y, hy, k₀, hg⟩), indicator_of_mem haR,
      indicator_of_mem hnc]
    simp
  set δi : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞ :=
    fun a => ((iwasawaDelta (a : GL (Fin (m + 1)) 𝕜) : ℝ≥0∞))⁻¹ with hδi
  have hinner : ∀ a : diagPosSubgroup (Fin (m + 1)) 𝕜,
      ∫⁻ u, ∫⁻ k, (boxGL ω B x).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
        ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ∂μK ∂μN ≤
      μK univ * μN Nc * R.indicator δi a := by
    intro a
    have hpre : μN (diagConj a ⁻¹' Nc) = δi a * μN Nc := by
      rw [← Measure.map_apply (continuous_diagConj a).measurable hNcm, map_diagConj_haar,
        Measure.smul_apply, smul_eq_mul]
    calc ∫⁻ u, ∫⁻ k, (boxGL ω B x).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
          ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ∂μK ∂μN
        ≤ ∫⁻ u, ∫⁻ _k, R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a *
            Nc.indicator (1 : upperUnipotentSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) (diagConj a u) ∂μK ∂μN :=
          lintegral_mono fun u => lintegral_mono fun k => hpt a u k
      _ = ∫⁻ u, (R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a * μK univ) *
            (diagConj a ⁻¹' Nc).indicator (1 : upperUnipotentSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) u ∂μN := by
          refine lintegral_congr fun u => ?_
          rw [lintegral_const]
          simp only [indicator, mem_preimage, Pi.one_apply]
          split_ifs <;> ring
      _ = (R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a * μK univ) *
            μN (diagConj a ⁻¹' Nc) := by
          rw [lintegral_const_mul _ (measurable_one.indicator
            (hNcm.preimage (continuous_diagConj a).measurable)),
            lintegral_indicator_one (hNcm.preimage (continuous_diagConj a).measurable)]
      _ = μK univ * μN Nc * R.indicator δi a := by
          rw [hpre]
          simp only [indicator, Pi.one_apply]
          split_ifs <;> ring
  have hmeasF : Measurable (R.indicator δi) :=
    (ENNReal.continuous_coe.comp continuous_iwasawaDelta_diagPos).measurable.inv.indicator hRm

  have hA : ∫⁻ a, R.indicator δi a ∂μA ≤
      ENNReal.ofReal (Real.exp (-(e * pairSum m x))) * (ENNReal.ofReal (Real.exp (e * (2 * L * P))) * V) := by
    rw [hμA, lintegral_map hmeasF (expDiag 𝕜 m).continuous.measurable]
    calc ∫⁻ z, R.indicator δi (expDiag 𝕜 m z)
        ≤ ∫⁻ z, box.indicator (fun _ => ENNReal.ofReal (Real.exp (-(e * pairSum m x))) *
            ENNReal.ofReal (Real.exp (e * (2 * L * P)))) z := by
          refine lintegral_mono fun z => ?_
          by_cases hz : expDiag 𝕜 m z ∈ R
          · have hzb : z ∈ box := by
              obtain ⟨z', hz', hzz⟩ := hz
              rwa [← (expDiag 𝕜 m).injective hzz]
            rw [indicator_of_mem hz, indicator_of_mem hzb]
            have hD : ((iwasawaDelta (diagPosOf ⟨fun i => Real.exp (z i), fun i => Real.exp_pos _⟩ :
                GL (Fin (m + 1)) 𝕜) : ℝ)) = Real.exp (e * pairSum m z) := by
              rw [iwasawaDelta_diagPosOf, pairSum, Finset.mul_sum, Real.exp_sum]
              refine Finset.prod_congr rfl fun p _ => ?_
              rw [← Real.exp_sub, ← Real.exp_nat_mul]
            rw [hδi]
            dsimp only
            rw [coe_expDiag, ← ENNReal.ofReal_coe_nnreal,
              ← ENNReal.ofReal_inv_of_pos (by rw [hD]; exact Real.exp_pos _), hD, ← Real.exp_neg,
              ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
            have hdiff : pairSum m x - pairSum m z ≤ 2 * L * P := by
              rw [pairSum, pairSum, ← Finset.sum_sub_distrib, hP]
              calc _ ≤ ∑ _p : StrictUpperIndex (Fin (m + 1)), 2 * L := Finset.sum_le_sum fun p _ => by
                    have h1 := hzb.1 p.1.1; have h2 := hzb.2 p.1.1
                    have h3 := hzb.1 p.1.2; have h4 := hzb.2 p.1.2
                    simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 h3 h4
                    linarith
                _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
            nlinarith [mul_le_mul_of_nonneg_left hdiff he0]
          · rw [indicator_of_notMem hz]; exact zero_le
      _ = ENNReal.ofReal (Real.exp (-(e * pairSum m x))) *
            ENNReal.ofReal (Real.exp (e * (2 * L * P))) * volume box := by
          rw [lintegral_indicator_const measurableSet_Icc]
      _ = _ := by
          rw [hbox, Real.volume_Icc_pi, mul_assoc, hV]
          congr 2
          refine Finset.prod_congr rfl fun i _ => ?_
          congr 1
          simp only [Pi.add_apply, Pi.sub_apply]
          ring

  rw [← lintegral_indicator_one hSm, hc _ (measurable_one.indicator hSm)]
  calc (c : ℝ≥0∞) * ∫⁻ a, ∫⁻ u, ∫⁻ k, (boxGL ω B x).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
        ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ∂μK ∂μN ∂μA
      ≤ (c : ℝ≥0∞) * ∫⁻ a, μK univ * μN Nc * R.indicator δi a ∂μA :=
        mul_le_mul_of_nonneg_left (lintegral_mono hinner) zero_le
    _ = (c : ℝ≥0∞) * (μK univ * μN Nc * ∫⁻ a, R.indicator δi a ∂μA) := by
        rw [lintegral_const_mul _ hmeasF]
    _ ≤ (c : ℝ≥0∞) * (μK univ * μN Nc * (ENNReal.ofReal (Real.exp (-(e * pairSum m x))) *
          (ENNReal.ofReal (Real.exp (e * (2 * L * P))) * V))) := by gcongr
    _ = _ := by ring

end PositivityTheory.Rg.Rs.boxvol

end
