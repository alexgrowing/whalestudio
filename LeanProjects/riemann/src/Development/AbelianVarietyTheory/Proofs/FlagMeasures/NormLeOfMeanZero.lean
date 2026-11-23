import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentQuotientInvariantProbabilityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

namespace GlobalTheory.MeanZero

theorem continuous_mean {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasure ν] {C : Set G} (hC : IsCompact C) (hν : ν Cᶜ = 0)
    {f : G → ℂ} (hf : Continuous f) : Continuous fun y => ∫ m, f (m * y) ∂ν := by

  have hae : ∀ᵐ m ∂ν, m ∈ C := by
    rw [ae_iff]
    exact hν
  have hres : ν.restrict C = ν := Measure.restrict_eq_self_of_ae_mem hae
  have hcont : Continuous (Function.uncurry fun (y m : G) => f (m * y)) :=
    hf.comp (continuous_snd.mul continuous_fst)
  have h := continuous_parametric_integral_of_continuous (μ := ν) hcont hC
  rw [hres] at h
  exact h

theorem norm_le_of_mean_zero {X : Type} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] {D : ℕ}
    (f : Fin D → X → ℂ) (c : Fin D → ℂ) (r : ℝ) (hi : ∀ i, Integrable (f i) ν)
    (h0 : ∀ i, ∫ m, f i m ∂ν = 0) (hb : ∀ᵐ m ∂ν, Real.sqrt (∑ i, ‖f i m - c i‖ ^ 2) ≤ r) :
    Real.sqrt (∑ i, ‖c i‖ ^ 2) ≤ r := by
  set S : ℝ := ∑ i, ‖c i‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hr0 : 0 ≤ r := by
    obtain ⟨m, hm⟩ := hb.exists
    exact (Real.sqrt_nonneg _).trans hm

  have hint : ∀ i ∈ (Finset.univ : Finset (Fin D)),
      Integrable (fun m => star (c i) * (c i - f i m)) ν :=
    fun i _ => ((integrable_const (c i)).sub (hi i)).const_mul (star (c i))
  have hval : ∫ m, (∑ i, star (c i) * (c i - f i m)) ∂ν = (S : ℂ) := by
    rw [integral_finset_sum _ hint, hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_sub (integrable_const _) (hi i), h0 i, integral_const]
    simp [Complex.conj_mul']

  have hbound : ∀ᵐ m ∂ν, ‖∑ i, star (c i) * (c i - f i m)‖ ≤ Real.sqrt S * r := by
    filter_upwards [hb] with m hm
    calc ‖∑ i, star (c i) * (c i - f i m)‖ ≤ ∑ i, ‖star (c i) * (c i - f i m)‖ := norm_sum_le _ _
      _ = ∑ i, ‖c i‖ * ‖f i m - c i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_star, norm_sub_rev]
      _ ≤ Real.sqrt (∑ i, ‖c i‖ ^ 2) * Real.sqrt (∑ i, ‖f i m - c i‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt S * r := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg _)
  have key : S ≤ Real.sqrt S * r := by
    have h := norm_integral_le_of_norm_le (integrable_const (Real.sqrt S * r)) hbound
    rw [hval, integral_const] at h
    simpa [Complex.norm_real, abs_of_nonneg hS0] using h
  have hsq := Real.sq_sqrt hS0
  have hs0 := Real.sqrt_nonneg S
  nlinarith

theorem norm_le_of_cusp (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (g : ℕ)
    (W : Submodule I.E (Fin I.n → I.E)) (D : ℕ) (Fn : Fin D → I.GA → ℂ) (x : I.GA) (c : Fin D → ℂ) (r : ℝ)
    (hg : 1 ≤ g) (hW : I.IsIsot W)
    (hF : ∀ i, Continuous (Fn i) ∧ (∀ γ ∈ I.GFset, ∀ y, Fn i (γ * y) = Fn i y) ∧
      (∀ k ∈ I.Kg g, ∀ y, Fn i (y * (1, k)) = Fn i y) ∧ I.IsCuspFn (I.muA μf) (Fn i))
    (hr : ∀ ν : I.Ginf, ((ν, 1) : I.GA) ∈ I.NA W →
      Real.sqrt (∑ i, ‖Fn i ((ν, 1) * x) - c i‖ ^ 2) ≤ r) :
    Real.sqrt (∑ i, ‖c i‖ ^ 2) ≤ r := by
  classical
  obtain ⟨ν, hνP, hνQ, Cp, hCp, -, hνCp⟩ := GlobalTheory.T.exists_unipotentQuotient_invariant_probability I W hW
  obtain ⟨⟨N, hN⟩, -, hsplit, hdense, -⟩ := GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I W hW
  obtain ⟨-, -, -, -, hpos⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant I μf
  obtain ⟨hT2, hLC, hSC, -, -, -, hKg⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨hKo, ⟨K, hK⟩, -⟩ := hKg g hg
  haveI := hT2
  haveI := hLC
  haveI := hSC

  have hU : {u : I.Gf | x.2⁻¹ * u * x.2 ∈ I.Kg g} ∈ nhds (1 : I.Gf) := by
    refine hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const) |>.mem_nhds ?_
    show x.2⁻¹ * 1 * x.2 ∈ I.Kg g
    rw [mul_one, inv_mul_cancel, ← hK]
    exact K.one_mem

  have horb : ∀ m ∈ I.NA W, Real.sqrt (∑ i, ‖Fn i (m * x) - c i‖ ^ 2) ≤ r := by
    intro m hm
    obtain ⟨γ, ⟨hγF, hγN⟩, hγU⟩ := hdense _ hU m hm
    have hm' : γ⁻¹ * m ∈ I.NA W := by
      rw [← hN] at hγN hm ⊢
      exact N.mul_mem (N.inv_mem hγN) hm
    have hk : x.2⁻¹ * (γ⁻¹ * m).2 * x.2 ∈ I.Kg g := hγU
    have heq : ∀ i, Fn i (m * x) = Fn i (((γ⁻¹ * m).1, 1) * x) := by
      intro i
      have h1 := (hF i).2.1 γ hγF (γ⁻¹ * m * x)
      rw [← mul_assoc, mul_inv_cancel_left] at h1
      have h2 : γ⁻¹ * m * x = (((γ⁻¹ * m).1, 1) * x) * (1, x.2⁻¹ * (γ⁻¹ * m).2 * x.2) := by
        ext <;> simp [mul_assoc]
      rw [h1, h2, (hF i).2.2.1 _ hk]
    simp_rw [heq]
    exact hr _ (hsplit _ hm').1

  have hzero : ∀ i, ∫ m, Fn i (m * x) ∂ν = 0 := by
    intro i
    by_contra hne
    have hc := continuous_mean ν hCp hνCp (hF i).1
    have hopen : IsOpen {y | ∫ m, Fn i (m * y) ∂ν ≠ 0} := isOpen_ne_fun hc continuous_const
    have hae := (hF i).2.2.2 W hW ν hνQ
    rw [ae_iff] at hae
    exact (hpos _ hopen ⟨x, hne⟩).ne' hae

  have hint : ∀ i, Integrable (fun m => Fn i (m * x)) ν := by
    intro i
    have hci : Continuous fun m => Fn i (m * x) := (hF i).1.comp (continuous_id.mul continuous_const)
    obtain ⟨B, hB⟩ := hCp.exists_bound_of_continuousOn hci.continuousOn
    have hae : ∀ᵐ m ∂ν, m ∈ Cp := by
      rw [ae_iff]
      exact hνCp
    refine Integrable.of_bound hci.aestronglyMeasurable B ?_
    filter_upwards [hae] with m hm
    exact hB m hm
  have hb : ∀ᵐ m ∂ν, Real.sqrt (∑ i, ‖Fn i (m * x) - c i‖ ^ 2) ≤ r := by
    have hae : ∀ᵐ m ∂ν, m ∈ I.NA W := by
      rw [ae_iff]
      exact hνQ.2.2.1
    filter_upwards [hae] with m hm
    exact horb m hm
  exact norm_le_of_mean_zero ν (fun i m => Fn i (m * x)) c r hint hzero hb

end GlobalTheory.MeanZero
