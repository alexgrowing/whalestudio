import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import Development.AutomorphicArithmetic.WhittakerHecke.RealIdeleMulAbsContinuousAndUnitAbsEqOne
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsRatIdeleEqExpUnitPrincipal
import Development.AutomorphicArithmetic.WhittakerHecke.IsCompactIntegralIdeleUnitsAndAbsEqOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem gen {G Q : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [Group Q] [Countable Q] (μ υ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure υ] (c : ℝ → G → Q → G) (S : Set G) (hc : ∀ α, Continuous fun p : ℝ × G => c p.1 p.2 α) (hS : υ Sᶜ = 0)
    (hinv : ∀ w ∈ S, υ.map (fun x => w * x) = υ) (hcov : ∀ x, ∃ t u α, u ∈ S ∧ x = c t u α)
    (hmul : ∀ τ w β t u α, c τ w β * c t u α = c (τ + t) (w * u) (β * α))
    (hfin : ∀ K, IsCompact K → ∃ (R : ℝ) (F : Finset Q), ∀ t, ∀ u ∈ S, ∀ α, c t u α ∈ K → t ∈ Set.Icc (-R) R ∧ α ∈ F) :
    ∃ k : ℝ≥0, k ≠ 0 ∧ ∀ h : G → ℝ≥0∞, Measurable h → ∫⁻ t : ℝ, ∫⁻ u, ∑' α : Q, h (c t u α) ∂υ = k * ∫⁻ y, h y ∂μ := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (ℝ × G), ν = volume.prod υ := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : Measure G, m = Measure.sum fun α : Q => ν.map fun p => c p.1 p.2 α := ⟨_, rfl⟩
  have key : ∀ h : G → ℝ≥0∞, Measurable h → ∫⁻ y, h y ∂m = ∫⁻ t : ℝ, ∫⁻ u, ∑' α : Q, h (c t u α) ∂υ := fun h hh => by
    have hα : ∀ α, Measurable fun p : ℝ × G => h (c p.1 p.2 α) := fun α => hh.comp (hc α).measurable
    rw [hm, lintegral_sum_measure, tsum_congr fun α => lintegral_map hh (hc α).measurable,
      ← lintegral_tsum fun α => (hα α).aemeasurable, hν, lintegral_prod _ (Measurable.ennreal_tsum hα).aemeasurable]
  have inv : m.IsMulLeftInvariant := ⟨fun x => by
    obtain ⟨τ, w, β, hw, rfl⟩ := hcov x
    have hp : MeasurePreserving (fun p : ℝ × G => (τ + p.1, w * p.2)) ν ν := by
      rw [hν]
      exact (measurePreserving_add_left volume τ).prod (g := fun x => w * x) ⟨measurable_const_mul w, hinv w hw⟩
    have e : ∀ α, ((ν.map fun p => c p.1 p.2 α).map (c τ w β * ·)) = ν.map fun p => c p.1 p.2 (β * α) := fun α => by
      refine Eq.trans ?_ (congrArg (Measure.map fun p : ℝ × G => c p.1 p.2 (β * α)) hp.map_eq)
      rw [Measure.map_map (measurable_const_mul _) (hc α).measurable, Measure.map_map (hc (β * α)).measurable hp.measurable]
      exact congrArg (fun f => Measure.map f ν) (funext fun p => hmul τ w β p.1 p.2 α)
    rw [hm, Measure.map_sum (measurable_const_mul _).aemeasurable]
    ext s hs
    rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs, tsum_congr fun α => congrArg (fun n : Measure G => n s) (e α)]
    exact (Equiv.mulLeft β).tsum_eq fun α : Q => (ν.map fun p => c p.1 p.2 α) s⟩
  have fin : IsFiniteMeasureOnCompacts m := ⟨fun K hK => by
    obtain ⟨R, F, hF⟩ := hfin K hK
    have hb : ∀ α, (ν.map fun p => c p.1 p.2 α) K ≤ if α ∈ F then volume (Set.Icc (-R) R) else 0 := fun α => by
      rw [Measure.map_apply (hc α).measurable hK.measurableSet]
      have hn : ν (Set.univ ×ˢ Sᶜ) = 0 := by rw [hν, Measure.prod_prod, hS, mul_zero]
      split_ifs with h
      · refine (measure_mono (t := Set.Icc (-R) R ×ˢ Set.univ ∪ Set.univ ×ˢ Sᶜ) fun p hp => ?_).trans ((measure_union_le _ _).trans ?_)
        · by_cases hu : p.2 ∈ S
          · exact Or.inl ⟨(hF _ _ hu α hp).1, trivial⟩
          · exact Or.inr ⟨trivial, hu⟩
        · rw [hn, add_zero, hν, Measure.prod_prod, measure_univ, mul_one]
      · exact (measure_mono (t := Set.univ ×ˢ Sᶜ) fun p hp => ⟨trivial, fun hu => h (hF _ _ hu α hp).2⟩).trans hn.le
    rw [hm, Measure.sum_apply _ hK.measurableSet]
    refine (ENNReal.tsum_le_tsum hb).trans_lt ?_
    rw [tsum_eq_sum (s := F) fun α h => if_neg h]
    exact ENNReal.sum_lt_top.2 fun α h => by rw [if_pos h]; exact measure_Icc_lt_top⟩
  have e := Measure.isMulLeftInvariant_eq_smul m μ
  refine ⟨m.haarScalarFactor μ, fun h0 => ?_, fun h hh => ?_⟩
  · rw [h0, zero_smul] at e
    have h1 := key (fun _ => 1) measurable_const
    rw [e, lintegral_zero_measure] at h1
    have h2 : (∑' _ : Q, (1 : ℝ≥0∞)) ≠ 0 := fun h => one_ne_zero (ENNReal.tsum_eq_zero.1 h 1)
    rw [lintegral_const, lintegral_const, measure_univ, mul_one, Real.volume_univ] at h1
    exact mul_ne_zero h2 ENNReal.top_ne_zero h1.symm
  · rw [← key h hh]
    exact (congrArg (fun n : Measure G => ∫⁻ y, h y ∂n) e).trans (by rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul])

private theorem cov_cont (α : ℚˣ) : Continuous fun p : ℝ × IdeleGroup ℚ => Un.cov p.1 p.2 α := by
  have hcont := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one.2.2.1
  unfold Un.cov
  exact (continuous_const.mul ((hcont.comp continuous_fst).mul (hcont.comp continuous_fst))).mul continuous_snd

private theorem fin_rat {C : Set (IdeleGroup ℚ)} (hC : IsCompact C) : {α : ℚˣ | IdeleGroup.diagonal ℚ α ∈ C}.Finite := by
  have h1 : (C ∩ (IdeleGroup.diagonal ℚ).range).Finite :=
    (hC.inter_right (Subgroup.isClosed_of_discrete (H := (IdeleGroup.diagonal ℚ).range))).finite
      (isDiscrete_iff_discreteTopology.2 (DiscreteTopology.of_subset (s := ((IdeleGroup.diagonal ℚ).range : Set _)) (inferInstanceAs (DiscreteTopology (IdeleGroup.diagonal ℚ).range))
        Set.inter_subset_right))
  exact (h1.preimage (IdeleGroup.diagonal_injective ℚ).injOn).subset fun α hα => ⟨hα, α, rfl⟩

private theorem cov_fin (K : Set (IdeleGroup ℚ)) (hK : IsCompact K) :
    ∃ (R : ℝ) (F : Finset ℚˣ), ∀ t, ∀ u ∈ UU, ∀ α, Un.cov t u α ∈ K → t ∈ Set.Icc (-R) R ∧ α ∈ F := by
  obtain ⟨-, hab, -, habU⟩ := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one
  have hl : Continuous fun y : (A ℚ)ˣ => Real.log (ab y) := M.continuous_ab.log fun y => (M.ab_pos y).ne'
  obtain ⟨R, hR⟩ := (hK.image hl).isBounded.exists_norm_le
  have ht : ∀ t, ∀ u ∈ UU, ∀ α, Un.cov t u α ∈ K → t ∈ Set.Icc (-R) R := fun t u hu α h => by
    have h1 := hR _ ⟨_, h, rfl⟩
    have h2 : ab (Un.cov t u α) = Real.exp (t + t) := by
      unfold Un.cov
      rw [M.ab_mul, M.ab_mul, M.ab_mul, M.ab_diag, habU u hu, hab _ (Real.exp_ne_zero _), abs_of_pos (Real.exp_pos _), one_mul,
        mul_one, Real.exp_add]
    dsimp only at h1
    rw [h2, Real.log_exp, Real.norm_eq_abs, abs_le] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hq : Continuous fun q : IdeleGroup ℚ × ℝ × IdeleGroup ℚ => q.1 * (Un.cov q.2.1 q.2.2 1)⁻¹ :=
    continuous_fst.mul ((cov_cont 1).comp continuous_snd).inv
  have hfin := fin_rat ((hK.prod ((isCompact_Icc (a := -R) (b := R)).prod UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one.1)).image hq)
  refine ⟨R, hfin.toFinset, fun t u hu α h => ⟨ht t u hu α h, hfin.mem_toFinset.2 ⟨(_, t, u), ⟨h, ht t u hu α h, hu⟩, ?_⟩⟩⟩
  simp only [Un.cov, map_one, one_mul, mul_assoc, mul_inv_cancel, mul_one]

theorem UpperTheory.ideleCovering_lintegral_eq_const_mul_haar :
    ∀ U : UMeas, ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ h : IdeleGroup ℚ → ℝ≥0∞, Measurable h →
        ∫⁻ t : ℝ, ∫⁻ u, ∑' α : ℚˣ, h (Un.cov t u α) ∂U.υ = c * ∫⁻ y, h y ∂(ideleMeasure ℚ) := by
  intro U
  haveI := U.prob
  haveI : Countable ℚˣ := Units.val_injective.countable
  refine gen (ideleMeasure ℚ) U.υ Un.cov UU cov_cont U.supp U.inv UpperTheory.exists_rat_idele_eq_exp_unit_principal (fun τ w β t u α => ?_) cov_fin
  simp only [Un.cov, Real.exp_add, UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one.1 _ _ (Real.exp_ne_zero _) (Real.exp_ne_zero _), map_mul]
  ac_rfl
