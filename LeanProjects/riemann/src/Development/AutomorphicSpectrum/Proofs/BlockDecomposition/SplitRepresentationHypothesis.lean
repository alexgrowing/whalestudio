import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableCharMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormUnitPair
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitRep

open GlobalTheory.CompanionTheory.WeilSplit (norm_pair nsg_pair)
open GlobalTheory.CompanionTheory.SplitGauss (trace_swap)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem chi_add (χ : AddChar F Circle) (x y : F) : (χ (x + y) : ℂ) = (χ x : ℂ) * (χ y : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_neg_one : modulus (-1 : F) = 1 := by
  have h : modulus (-1 : F) * modulus (-1 : F) = 1 := by
    rw [← modulus_mul]; simp [modulus_one]
  have h2 : modulus (-1 : F) ^ 2 = 1 := by rw [sq]; exact h
  exact (pow_eq_one_iff.1 h2).resolve_right (by norm_num)

omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_neg' (x : F) : modulus (-x) = modulus x := by
  rw [show -x = -1 * x by ring, modulus_mul, modulus_neg_one, one_mul]

theorem rWS_zero (χ : AddChar F Circle) {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1) (h : g 1 0 = 0)
    (Φ : F × F → ℂ) (z : F × F) :
    rWS χ g Φ z = (χ (g 0 0 * g 0 1 * (z.1 * z.2)) : ℂ) * ((modulus (g 0 0) : ℝ) : ℂ) *
      Φ (g 0 0 * z.1, g 0 0 * z.2) := by
  have ha : g 0 0 ≠ 0 := by
    intro h0
    rw [Matrix.det_fin_two, h, h0] at hg
    simp at hg
  have e : algebraMap F (F × F) (g 0 0) * z = (g 0 0 * z.1, g 0 0 * z.2) := by ext <;> simp
  simp only [rWm, rW, if_pos h, norm_pair, nsg_pair ha, e]
  ring

theorem rWS_ne (χ : AddChar F Circle) {g : Matrix (Fin 2) (Fin 2) F} (h : g 1 0 ≠ 0)
    (Φ : F × F → ℂ) (z : F × F) :
    rWS χ g Φ z = (((modulus (g 1 0) : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ u, (χ ((g 0 0 * (z.1 * z.2) + g 1 1 * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / g 1 0) : ℂ) * Φ u
        ∂muS χ := by
  simp only [rWm, rW, if_neg h, norm_pair, trace_swap, nsg_pair (neg_ne_zero.mpr h), one_mul, mul_one]

theorem fts_apply (χ : AddChar F Circle) (Φ : F × F → ℂ) (y : F × F) :
    FTs χ swapE (muS χ) Φ y = ∫ u, Φ u * (χ (u.1 * y.2 + u.2 * y.1) : ℂ) ∂muS χ := by
  simp only [FTs, trace_swap]

omit [MeasurableSpace F] [BorelSpace F] in
theorem isLC_char {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) :
    IsLocallyConstant fun x : F => (χ x : ℂ) :=
  isLocallyConstant_of_add_valBall (N := addCharConductor χ) fun x h hh => by
    rw [AddChar.map_add_eq_mul, isTrivialOn_addCharConductor hχ hχ1 h hh]
    simp

omit [MeasurableSpace F] [BorelSpace F] in
theorem sbe_char_mul {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) {k : F × F → F}
    (hk : Continuous k) {Φ : F × F → ℂ} (hΦ : Φ ∈ SBE (F × F)) :
    (fun z => (χ (k z) : ℂ) * Φ z) ∈ SBE (F × F) :=
  ⟨((isLC_char hχ hχ1).comp_continuous hk).mul hΦ.1, hΦ.2.mul_left⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem sbe_const_mul (C : ℂ) {Φ : F × F → ℂ} (hΦ : Φ ∈ SBE (F × F)) :
    (fun z => C * Φ z) ∈ SBE (F × F) :=
  ⟨(IsLocallyConstant.const C).mul hΦ.1, hΦ.2.mul_left⟩

def scaleH [IsTopologicalRing F] {s : F} (hs : s ≠ 0) : (F × F) ≃ₜ (F × F) :=
  (Homeomorph.mulLeft₀ s hs).prodCongr (Homeomorph.mulLeft₀ s hs)

omit [MeasurableSpace F] [BorelSpace F] in
theorem sbe_scale {s : F} (hs : s ≠ 0) {Φ : F × F → ℂ} (hΦ : Φ ∈ SBE (F × F)) :
    (fun z : F × F => Φ (s * z.1, s * z.2)) ∈ SBE (F × F) :=
  ⟨hΦ.1.comp_continuous (scaleH hs).continuous, hΦ.2.comp_homeomorph (scaleH hs)⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem sbe_sum {ι : Type*} (s : Finset ι) (f : ι → F × F → ℂ) (h : ∀ i ∈ s, f i ∈ SBE (F × F)) :
    (fun z => ∑ i ∈ s, f i z) ∈ SBE (F × F) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert ha]
    exact ⟨h1.1.add h2.1, h1.2.add h2.2⟩

omit [MeasurableSpace F] [BorelSpace F] in

theorem sbe_tensor {f g : F → ℂ} (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F) :
    (fun u : F × F => f u.2 * g u.1) ∈ SBE (F × F) := by
  refine ⟨(hf.1.comp_continuous continuous_snd).mul (hg.1.comp_continuous continuous_fst), ?_⟩
  refine HasCompactSupport.intro (hg.2.isCompact.prod hf.2.isCompact) fun u hu => ?_
  by_cases h1 : u.1 ∈ tsupport g
  · have h2 : u.2 ∉ tsupport f := fun h2 => hu ⟨h1, h2⟩
    simp [image_eq_zero_of_notMem_tsupport h2]
  · simp [image_eq_zero_of_notMem_tsupport h1]

theorem fts_sbe {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) {Φ : F × F → ℂ}
    (hΦ : Φ ∈ SBE (F × F)) : FTs χ swapE (muS χ) Φ ∈ SBE (F × F) := by
  obtain ⟨n, f, g, hf, hg, hfg⟩ := GlobalTheory.CompanionTheory.PureTensor.exists_pure_sum hΦ.1 hΦ.2
  have hf' : ∀ i, f i ∈ schwartzBruhat F := hf
  have hg' : ∀ i, g i ∈ schwartzBruhat F := hg
  obtain rfl : Φ = fun z => ∑ i, f i z.1 * g i z.2 := funext fun z => hfg z.1 z.2
  have e : FTs χ swapE (muS χ) (fun z => ∑ i, f i z.1 * g i z.2) = fun u => ∑ i,
      localFourier (selfDualMeasure χ) χ (f i) u.2 * localFourier (selfDualMeasure χ) χ (g i) u.1 :=
    funext fun u => GlobalTheory.CompanionTheory.SplitGauss.fts_sum hχ hf' hg' u
  rw [e]
  exact sbe_sum _ _ fun i _ => sbe_tensor
    (localFourier_mem_schwartzBruhat _ hχ hχ1 (hf' i)) (localFourier_mem_schwartzBruhat _ hχ hχ1 (hg' i))

theorem fts_fts {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) {Φ : F × F → ℂ}
    (hΦ : Φ ∈ SBE (F × F)) (z : F × F) :
    FTs χ swapE (muS χ) (FTs χ swapE (muS χ) Φ) z = Φ (-z) := by
  obtain ⟨n, f, g, hf, hg, hfg⟩ := GlobalTheory.CompanionTheory.PureTensor.exists_pure_sum hΦ.1 hΦ.2
  have hf' : ∀ i, f i ∈ schwartzBruhat F := hf
  have hg' : ∀ i, g i ∈ schwartzBruhat F := hg
  obtain rfl : Φ = fun z => ∑ i, f i z.1 * g i z.2 := funext fun z => hfg z.1 z.2
  have hT := fun {h : F → ℂ} (hh : h ∈ schwartzBruhat F) =>
    localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hh
  have e : FTs χ swapE (muS χ) (fun z => ∑ i, f i z.1 * g i z.2) = fun u => ∑ i,
      localFourier (selfDualMeasure χ) χ (g i) u.1 * localFourier (selfDualMeasure χ) χ (f i) u.2 :=
    funext fun u => by
      rw [GlobalTheory.CompanionTheory.SplitGauss.fts_sum hχ hf' hg' u]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e, GlobalTheory.CompanionTheory.SplitGauss.fts_sum hχ (fun i => hT (hg' i)) (fun i => hT (hf' i)) z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [localFourier_localFourier_selfDual hχ hχ1 (hg' i), localFourier_localFourier_selfDual hχ hχ1 (hf' i)]
  simp [mul_comm]

theorem integral_scale (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) (G : F × F → ℂ) :
    ∫ u, G (s * u.1, s * u.2) ∂muS χ =
      (((modulus s : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus s : ℝ)⁻¹ : ℝ) : ℂ) * ∫ u, G u ∂muS χ := by
  have he1 : MeasurableEmbedding (fun x : F => s * x) := (Homeomorph.mulLeft₀ s hs).measurableEmbedding
  have he := he1.prodMap he1
  have hmap : Measure.map (Prod.map (fun x : F => s * x) (fun x : F => s * x)) (muS χ) =
      ((modulus s)⁻¹ * (modulus s)⁻¹) • muS χ := by
    rw [← Measure.map_prod_map _ _ he1.measurable he1.measurable,
      map_mul_left_eq_smul _ hs, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have h := he.integral_map (μ := muS χ) G
  rw [hmap, integral_smul_nnreal_measure] at h
  simp only [Prod.map] at h
  rw [← h, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring_nf

theorem rWS_n (χ : AddChar F Circle) (b : F) (Φ : F × F → ℂ) :
    rWS χ !![1, b; 0, 1] Φ = fun z => (χ (b * (z.1 * z.2)) : ℂ) * Φ z := by
  funext z
  rw [rWS_zero χ (by simp [Matrix.det_fin_two]) (by simp)]
  simp [modulus_one]

theorem rWS_m (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) (Φ : F × F → ℂ) :
    rWS χ !![s, 0; 0, s⁻¹] Φ = fun z => ((modulus s : ℝ) : ℂ) * Φ (s * z.1, s * z.2) := by
  funext z
  rw [rWS_zero χ (by simp [Matrix.det_fin_two, hs]) (by simp)]
  simp

theorem rWS_w (χ : AddChar F Circle) (Φ : F × F → ℂ) :
    rWS χ !![0, 1; -1, 0] Φ = FTs χ swapE (muS χ) Φ := by
  funext z
  rw [rWS_ne χ (by simp), fts_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, modulus_neg_one]
  simp only [NNReal.coe_one, inv_one, Complex.ofReal_one, one_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have e : (0 * (z.1 * z.2) + 0 * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / (-1 : F) =
      u.1 * z.2 + u.2 * z.1 := by ring
  simp only [e]
  ring

theorem rep_n (χ : AddChar F Circle) {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1) (b : F)
    (Φ : F × F → ℂ) :
    rWS χ (g * !![1, b; 0, 1]) Φ = rWS χ g (rWS χ !![1, b; 0, 1] Φ) := by
  have e00 : (g * !![1, b; 0, 1]) 0 0 = g 0 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * !![1, b; 0, 1]) 0 1 = g 0 0 * b + g 0 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * !![1, b; 0, 1]) 1 0 = g 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * !![1, b; 0, 1]) 1 1 = g 1 0 * b + g 1 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : (g * !![1, b; 0, 1]).det = 1 := by
    rw [Matrix.det_mul, hg]; simp [Matrix.det_fin_two]
  rw [rWS_n]
  funext z
  by_cases hc : g 1 0 = 0
  · rw [rWS_zero χ hdet (e10.trans hc), rWS_zero χ hg hc, e00, e01]
    have e : g 0 0 * (g 0 0 * b + g 0 1) * (z.1 * z.2) =
        g 0 0 * g 0 1 * (z.1 * z.2) + b * (g 0 0 * z.1 * (g 0 0 * z.2)) := by ring
    simp only [e, chi_add]
    ring
  · rw [rWS_ne χ (by rwa [e10]), rWS_ne χ hc, e00, e10, e11]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e : (g 0 0 * (z.1 * z.2) + (g 1 0 * b + g 1 1) * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / g 1 0 =
        (g 0 0 * (z.1 * z.2) + g 1 1 * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / g 1 0 + b * (u.1 * u.2) := by
      field_simp
      ring
    simp only [e, chi_add]
    ring

theorem rep_m (χ : AddChar F Circle) {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1) {s : F} (hs : s ≠ 0)
    (Φ : F × F → ℂ) :
    rWS χ (g * !![s, 0; 0, s⁻¹]) Φ = rWS χ g (rWS χ !![s, 0; 0, s⁻¹] Φ) := by
  have e00 : (g * !![s, 0; 0, s⁻¹]) 0 0 = g 0 0 * s := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * !![s, 0; 0, s⁻¹]) 0 1 = g 0 1 * s⁻¹ := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * !![s, 0; 0, s⁻¹]) 1 0 = g 1 0 * s := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * !![s, 0; 0, s⁻¹]) 1 1 = g 1 1 * s⁻¹ := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : (g * !![s, 0; 0, s⁻¹]).det = 1 := by
    rw [Matrix.det_mul, hg]; simp [Matrix.det_fin_two, hs]
  have hM : ((modulus s : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero hs
  rw [rWS_m χ hs]
  funext z
  by_cases hc : g 1 0 = 0
  · rw [rWS_zero χ hdet (by rw [e10, hc, zero_mul]), rWS_zero χ hg hc, e00, e01, modulus_mul]
    have e : g 0 0 * s * (g 0 1 * s⁻¹) * (z.1 * z.2) = g 0 0 * g 0 1 * (z.1 * z.2) := by
      field_simp
    have e2 : ∀ x : F, g 0 0 * s * x = s * (g 0 0 * x) := fun x => by ring
    rw [e, e2 z.1, e2 z.2]
    push_cast
    ring
  · rw [rWS_ne χ (by rw [e10]; exact mul_ne_zero hc hs), rWS_ne χ hc, e00, e10, e11, modulus_mul]
    set G : F × F → ℂ := fun u =>
      (χ ((g 0 0 * (z.1 * z.2) + g 1 1 * (s⁻¹ * s⁻¹) * (u.1 * u.2) - s⁻¹ * (u.1 * z.2 + u.2 * z.1)) / g 1 0) : ℂ) * Φ u
      with hG
    have h1 : ∫ u, (χ ((g 0 0 * s * (z.1 * z.2) + g 1 1 * s⁻¹ * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / (g 1 0 * s)) : ℂ) * Φ u ∂muS χ =
        ∫ u, G u ∂muS χ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      have e : (g 0 0 * s * (z.1 * z.2) + g 1 1 * s⁻¹ * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / (g 1 0 * s) =
          (g 0 0 * (z.1 * z.2) + g 1 1 * (s⁻¹ * s⁻¹) * (u.1 * u.2) - s⁻¹ * (u.1 * z.2 + u.2 * z.1)) / g 1 0 := by
        field_simp
      simp only [hG, e]
    have h2 : ∫ u, (χ ((g 0 0 * (z.1 * z.2) + g 1 1 * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / g 1 0) : ℂ) *
        (((modulus s : ℝ) : ℂ) * Φ (s * u.1, s * u.2)) ∂muS χ =
        ((modulus s : ℝ) : ℂ) * ∫ u, G (s * u.1, s * u.2) ∂muS χ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      have e : (g 0 0 * (z.1 * z.2) + g 1 1 * (s⁻¹ * s⁻¹) * (s * u.1 * (s * u.2)) -
          s⁻¹ * (s * u.1 * z.2 + s * u.2 * z.1)) / g 1 0 =
          (g 0 0 * (z.1 * z.2) + g 1 1 * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / g 1 0 := by
        field_simp
      simp only [hG, e]
      ring
    rw [h1, h2, integral_scale χ hs]
    push_cast
    field_simp

theorem gauss_step [CharZero F] {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) {Φ : F × F → ℂ}
    (hΦ : Φ ∈ SBE (F × F)) {a b c d : F} (hc : c ≠ 0) (hd : d ≠ 0) (hdet : a * d - b * c = 1) (z : F × F) :
    (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ v, (χ ((a * (z.1 * z.2) + d * (v.1 * v.2) - (v.1 * z.2 + v.2 * z.1)) / c) : ℂ) *
        FTs χ swapE (muS χ) Φ v ∂muS χ =
    (((modulus d : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ u, (χ ((-b * (z.1 * z.2) + c * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / (-d)) : ℂ) * Φ u ∂muS χ := by
  have ha : a = (1 + b * c) / d := by
    field_simp
    linear_combination hdet
  set t : F × F := (z.1 / d, z.2 / d) with ht
  set Ψ : F × F → ℂ := fun u => (χ (u.1 * t.2 + u.2 * t.1) : ℂ) * Φ u with hΨd
  have hΨ : Ψ ∈ SBE (F × F) := sbe_char_mul hχ hχ1 (by fun_prop) hΦ
  have hA : d / c ≠ 0 := div_ne_zero hd hc
  have hG := GlobalTheory.CompanionTheory.SplitGauss.sGauss F χ hχ hχ1 (Units.mk0 (d / c) hA) Ψ hΨ
  simp only [Units.val_mk0] at hG
  have hFT : ∀ v, FTs χ swapE (muS χ) Ψ v = FTs χ swapE (muS χ) Φ (v + t) := by
    intro v
    rw [fts_apply, fts_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e : u.1 * (v + t).2 + u.2 * (v + t).1 = (u.1 * t.2 + u.2 * t.1) + (u.1 * v.2 + u.2 * v.1) := by
      simp only [Prod.snd_add, Prod.fst_add]
      ring
    simp only [hΨd, e, chi_add]
    ring
  have h1 : ∫ v, (χ ((a * (z.1 * z.2) + d * (v.1 * v.2) - (v.1 * z.2 + v.2 * z.1)) / c) : ℂ) *
      FTs χ swapE (muS χ) Φ v ∂muS χ =
      (χ (b * (z.1 * z.2) / d) : ℂ) * ∫ v, (χ (d / c * (v.1 * v.2)) : ℂ) * FTs χ swapE (muS χ) Ψ v ∂muS χ := by
    rw [← integral_add_right_eq_self (fun v => (χ ((a * (z.1 * z.2) + d * (v.1 * v.2) - (v.1 * z.2 + v.2 * z.1)) / c) : ℂ) *
      FTs χ swapE (muS χ) Φ v) t, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have e : (a * (z.1 * z.2) + d * ((v + t).1 * (v + t).2) - ((v + t).1 * z.2 + (v + t).2 * z.1)) / c =
        b * (z.1 * z.2) / d + d / c * (v.1 * v.2) := by
      simp only [Prod.fst_add, Prod.snd_add, ht]
      rw [ha]
      field_simp
      ring
    simp only [e, chi_add, hFT]
    ring
  have h2 : ∫ u, (χ ((-b * (z.1 * z.2) + c * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / (-d)) : ℂ) * Φ u ∂muS χ =
      (χ (b * (z.1 * z.2) / d) : ℂ) * ∫ u, (χ (-(u.1 * u.2) / (d / c)) : ℂ) * Ψ u ∂muS χ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e : (-b * (z.1 * z.2) + c * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / (-d) =
        b * (z.1 * z.2) / d + (-(u.1 * u.2) / (d / c) + (u.1 * t.2 + u.2 * t.1)) := by
      simp only [ht]
      field_simp
      ring
    simp only [e, chi_add, hΨd]
    ring
  have hMc : ((modulus c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hc
  have hMd : ((modulus d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hd
  have hmod : modulus (d / c) = modulus d * (modulus c)⁻¹ := by
    rw [div_eq_mul_inv, modulus_mul, modulus_inv]
  rw [h1, hG, h2, hmod]
  generalize (∫ u, (χ (-(u.1 * u.2) / (d / c)) : ℂ) * Ψ u ∂muS χ) = I
  push_cast
  field_simp

theorem rep_w [CharZero F] {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1) {Φ : F × F → ℂ} (hΦ : Φ ∈ SBE (F × F)) :
    rWS χ (g * !![0, 1; -1, 0]) Φ = rWS χ g (rWS χ !![0, 1; -1, 0] Φ) := by
  have e00 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 0 0 = -g 0 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 0 1 = g 0 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 1 0 = -g 1 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 1 1 = g 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : (g * !![0, 1; -1, 0]).det = 1 := by
    rw [Matrix.det_mul, hg]; simp [Matrix.det_fin_two]
  have hd2 : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hg
  rw [rWS_w]
  funext z
  by_cases hd : g 1 1 = 0
  · have hbc : g 0 1 * g 1 0 = -1 := by rw [hd] at hd2; linear_combination -hd2
    have hb : g 0 1 ≠ 0 := fun h => by rw [h] at hbc; simp at hbc
    have hc : g 1 0 ≠ 0 := fun h => by rw [h] at hbc; simp at hbc
    have hcb : g 1 0 = -(g 0 1)⁻¹ := by field_simp; linear_combination hbc
    have hinv := fts_fts hχ hχ1 hΦ (g 0 1 * z.1, g 0 1 * z.2)
    rw [fts_apply] at hinv
    rw [rWS_zero χ hdet (by rw [e10, hd, neg_zero]), rWS_ne χ hc, e00, e01, hd, modulus_neg']
    have e1 : ∫ u, (χ ((g 0 0 * (z.1 * z.2) + 0 * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / g 1 0) : ℂ) *
        FTs χ swapE (muS χ) Φ u ∂muS χ = (χ (-g 0 1 * g 0 0 * (z.1 * z.2)) : ℂ) *
        ∫ u, FTs χ swapE (muS χ) Φ u * (χ (u.1 * (g 0 1 * z.2) + u.2 * (g 0 1 * z.1)) : ℂ) ∂muS χ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      have e : (g 0 0 * (z.1 * z.2) + 0 * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / g 1 0 =
          -g 0 1 * g 0 0 * (z.1 * z.2) + (u.1 * (g 0 1 * z.2) + u.2 * (g 0 1 * z.1)) := by
        rw [hcb]
        field_simp
        ring
      simp only [e, chi_add]
      ring
    have hm : modulus (g 1 0) = (modulus (g 0 1))⁻¹ := by
      rw [hcb, modulus_neg', modulus_inv]
    have hneg : (-(g 0 1 * z.1, g 0 1 * z.2) : F × F) = (-g 0 1 * z.1, -g 0 1 * z.2) := by
      ext <;> simp
    rw [e1, hinv, hm, hneg]
    push_cast
    simp only [inv_inv]
    ring
  · by_cases hc : g 1 0 = 0
    · have had : g 0 0 * g 1 1 = 1 := by rw [hc] at hd2; linear_combination hd2
      have ha : g 0 0 ≠ 0 := fun h => by rw [h] at had; simp at had
      have hda : g 1 1 = (g 0 0)⁻¹ := by field_simp; linear_combination had
      rw [rWS_ne χ (by rw [e10]; exact neg_ne_zero.mpr hd), rWS_zero χ hg hc, e00, e10, e11, fts_apply,
        modulus_neg', hda, modulus_inv, hc]
      simp only [NNReal.coe_inv, inv_inv]
      have e1 : ∫ u, (χ ((-g 0 1 * (z.1 * z.2) + 0 * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / -(g 0 0)⁻¹) : ℂ) * Φ u ∂muS χ =
          (χ (g 0 0 * g 0 1 * (z.1 * z.2)) : ℂ) *
            ∫ u, Φ u * (χ (u.1 * (g 0 0 * z.2) + u.2 * (g 0 0 * z.1)) : ℂ) ∂muS χ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        have e : (-g 0 1 * (z.1 * z.2) + 0 * (u.1 * u.2) - (u.1 * z.2 + u.2 * z.1)) / -(g 0 0)⁻¹ =
            g 0 0 * g 0 1 * (z.1 * z.2) + (u.1 * (g 0 0 * z.2) + u.2 * (g 0 0 * z.1)) := by
          field_simp
          ring
        simp only [e, chi_add]
        ring
      rw [e1]
      ring
    · rw [rWS_ne χ (by rw [e10]; exact neg_ne_zero.mpr hd), rWS_ne χ hc, e00, e10, e11, modulus_neg']
      exact (gauss_step hχ hχ1 hΦ hc hd hd2 z).symm

def Good (χ : AddChar F Circle) (h : Matrix (Fin 2) (Fin 2) F) : Prop :=
  h.det = 1 ∧ ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Φ ∈ SBE (F × F),
    rWS χ h Φ ∈ SBE (F × F) ∧ rWS χ (g * h) Φ = rWS χ g (rWS χ h Φ)

theorem Good.mul {χ : AddChar F Circle} {x y : Matrix (Fin 2) (Fin 2) F} (hx : Good χ x) (hy : Good χ y) :
    Good χ (x * y) := by
  refine ⟨by rw [Matrix.det_mul, hx.1, hy.1, one_mul], fun g hg Φ hΦ => ?_⟩
  have a := hy.2 x hx.1 Φ hΦ
  have b := hx.2 g hg _ a.1
  have c := hy.2 (g * x) (by rw [Matrix.det_mul, hg, hx.1, one_mul]) Φ hΦ
  exact ⟨by rw [a.2]; exact b.1, by rw [← mul_assoc, c.2, b.2, a.2]⟩

theorem good_n {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) (b : F) : Good χ !![1, b; 0, 1] := by
  refine ⟨by simp [Matrix.det_fin_two], fun g hg Φ hΦ => ⟨?_, rep_n χ hg b Φ⟩⟩
  rw [rWS_n]
  exact sbe_char_mul hχ hχ1 (k := fun z => b * (z.1 * z.2)) (by fun_prop) hΦ

theorem good_m (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) : Good χ !![s, 0; 0, s⁻¹] := by
  refine ⟨by simp [Matrix.det_fin_two, hs], fun g hg Φ hΦ => ⟨?_, rep_m χ hg hs Φ⟩⟩
  rw [rWS_m χ hs]
  exact sbe_const_mul _ (sbe_scale hs hΦ)

theorem good_w [CharZero F] {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) : Good χ !![0, 1; -1, 0] := by
  refine ⟨by simp [Matrix.det_fin_two], fun g hg Φ hΦ => ⟨?_, rep_w hχ hχ1 hg hΦ⟩⟩
  rw [rWS_w]
  exact fts_sbe hχ hχ1 hΦ

theorem good_all [CharZero F] {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    {h : Matrix (Fin 2) (Fin 2) F} (hh : h.det = 1) : Good χ h := by
  have hd2 : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hh
  by_cases hc : h 1 0 = 0
  · have had : h 0 0 * h 1 1 = 1 := by rw [hc] at hd2; linear_combination hd2
    have ha : h 0 0 ≠ 0 := fun e => by rw [e] at had; simp at had
    have e : h = !![h 0 0, 0; 0, (h 0 0)⁻¹] * !![1, h 0 1 / h 0 0; 0, 1] := by
      have hda : h 1 1 = (h 0 0)⁻¹ := by field_simp; linear_combination had
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hda] <;> field_simp
    rw [e]
    exact (good_m χ ha).mul (good_n hχ hχ1 _)
  · have hs : -(h 1 0)⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hc)
    have e : h = !![1, h 0 0 / h 1 0; 0, 1] * !![-(h 1 0)⁻¹, 0; 0, (-(h 1 0)⁻¹)⁻¹] * !![0, 1; -1, 0] *
        !![1, h 1 1 / h 1 0; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
      linear_combination -hd2
    rw [e]
    exact (((good_n hχ hχ1 _).mul (good_m χ hs)).mul (good_w hχ hχ1)).mul (good_n hχ hχ1 _)

theorem sRep : SRep := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 g h hg hh Φ hΦ
  exact (good_all hχ hχ1 hh).2 g hg Φ hΦ

end GlobalTheory.CompanionTheory.SplitRep
