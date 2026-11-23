import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.AbLeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IdeleSum

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem isClosed_range_nU {F : Type} [Field F] [NumberField F] :
    IsClosed (Set.range (nU : A F → G1 F)) := by
  have e : Set.range (nU : A F → G1 F) = {g : G1 F | g 0 0 = 1} ∩ ({g : G1 F | g 1 0 = 0} ∩ {g : G1 F | g 1 1 = 1}) := by
    ext g
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · show (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) (A F)) 0 0 = 1
        simp
      · show (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) (A F)) 1 0 = 0
        simp
      · show (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) (A F)) 1 1 = 1
        simp
    · rintro ⟨h0, h1, h2⟩
      refine ⟨g 0 1, Subtype.ext ?_⟩
      simp only [Set.mem_setOf_eq] at h0 h1 h2
      ext i j
      fin_cases i <;> fin_cases j <;> simp [nU, h0, h1, h2]
  rw [e]
  exact (isClosed_eq (M.continuous_entry 0 0) continuous_const).inter
    ((isClosed_eq (M.continuous_entry 1 0) continuous_const).inter
      (isClosed_eq (M.continuous_entry 1 1) continuous_const))

private theorem quot_mem {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {U : Set (IdeleGroup F)} (hbor : ∀ (b : A F) (a : (A F)ˣ), nU b * mD a ∈ KK F → a ∈ U ∧ ab a = 1)
    {a a' : (A F)ˣ} {b : A F} {k k' : G1 F} (hk : k ∈ KK F) (hk' : k' ∈ KK F)
    (h : mD a * k = nU b * mD a' * k') : a'⁻¹ * a ∈ U := by
  obtain ⟨hKs, -⟩ := M.kkCpt F
  have hm : k' * k⁻¹ ∈ KK F := by
    rw [hKs] at hk hk' ⊢
    exact (M.Ks F).mul_mem hk' ((M.Ks F).inv_mem hk)
  have e : k' * k⁻¹ = nU (((a'⁻¹ : (A F)ˣ) : A F) ^ 2 * (-b)) * mD (a'⁻¹ * a) := by
    rw [M.mD_mul, ← mul_assoc, ← M.mD_mul_nU, M.nU_neg, M.mD_inv]
    have : k' = (mD a')⁻¹ * (nU b)⁻¹ * (mD a * k) := by rw [h]; group
    rw [this]; group
  rw [e] at hm
  exact (hbor _ _ hm).1

theorem UpperTheory.ConvolutionTheory.R2.M.siegJ :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M₀ : Meas F) (C : Set (IdeleGroup F)) (ρ : IdeleGroup F), IsCompact C → 1 < ab ρ → MeasurableSet {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} ∧ M.J0 M₀ (Set.indicator {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} 1) < ⊤ := by
  intro F _ _ _ M₀ C ρ hC hρ
  obtain ⟨-, hKc⟩ := M.kkCpt F
  obtain ⟨U, hU, hbor⟩ := M.borK F
  constructor
  · have e : {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} =
        ⋃ n : ℕ, Set.range (nU : A F → G1 F) * ((mD '' ((ρ ^ n * ·) '' C)) * KK F) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_mul, Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨b, n, x, hx, k, hk, rfl⟩
        exact ⟨n, _, ⟨b, rfl⟩, _, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, k, hk, rfl⟩, (mul_assoc _ _ _).symm⟩
      · rintro ⟨n, _, ⟨b, rfl⟩, _, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, k, hk, rfl⟩, rfl⟩
        exact ⟨b, n, x, hx, k, hk, (mul_assoc _ _ _).symm⟩
    rw [e]
    refine MeasurableSet.iUnion fun n => ?_
    have hc : IsCompact ((mD '' ((ρ ^ n * ·) '' C)) * KK F) :=
      ((hC.image (continuous_mul_left _)).image M.continuous_mD).mul hKc
    exact (isClosed_range_nU.mul_right_of_isCompact hc).measurableSet
  · set S : Set (G1 F) := {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} with hS
    set W : Set (IdeleGroup F) := ⋃ n : ℕ, (ρ ^ n * ·) '' (C * U) with hW
    have hCU : IsCompact (C * U) := hC.mul hU
    have hWm : MeasurableSet W := MeasurableSet.iUnion fun n =>
      (hCU.image (continuous_mul_left _)).measurableSet
    haveI := M₀.prob
    have hae : ∀ᵐ p ∂M₀.ν, p.2 ∈ KK F := by
      have h0 : ∀ᵐ k ∂M₀.κ, k ∈ KK F := M₀.supp
      exact Measure.quasiMeasurePreserving_snd.ae h0
    have hle : M.J0 M₀ (S.indicator 1) ≤ ∫⁻ p, W.indicator M.wt p.1 ∂M₀.ν := by
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with p hp
      by_cases hmem : mD p.1 * p.2 ∈ S
      · obtain ⟨b, n, x, hx, k, hk, h⟩ := id hmem
        have hq := quot_mem hbor hp hk h
        have hpW : p.1 ∈ W := by
          refine Set.mem_iUnion.2 ⟨n, x * ((ρ ^ n * x)⁻¹ * p.1), ⟨x, hx, _, hq, rfl⟩, ?_⟩
          show ρ ^ n * (x * ((ρ ^ n * x)⁻¹ * p.1)) = p.1
          group
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpW]
        simp
      · rw [Set.indicator_of_notMem hmem]
        simp
    have heq : ∫⁻ p, W.indicator M.wt p.1 ∂M₀.ν = ∫⁻ a in W, M.wt a ∂(ideleMeasure F) := by
      rw [← lintegral_indicator hWm, Meas.ν,
        lintegral_prod (fun p : IdeleGroup F × G1 F => W.indicator M.wt p.1)
          ((M.measurable_wt.indicator hWm).comp measurable_fst).aemeasurable]
      simp
    exact hle.trans_lt (heq ▸ M.ideleSum F (C * U) ρ hCU hρ)
