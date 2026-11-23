import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

private abbrev M4 : Type := Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ
private abbrev MS : Type := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ

private noncomputable def rx (M : MS) : M4 := reindex finSumFinEquiv finSumFinEquiv M

private theorem rx_mul (M N : MS) : rx M * rx N = rx (M * N) := by
  simp [rx, reindex_apply, submatrix_mul_equiv]

private theorem rx_star (M : MS) : star (rx M) = rx (star M) := by
  ext i j
  simp [rx, reindex_apply, star_eq_conjTranspose]

private theorem rx_one : rx (1 : MS) = 1 := by
  simp [rx, reindex_apply]

private theorem rx_mem {M : MS} (h : M * star M = 1) : rx M ∈ unitaryGroup (Fin (2 + 2)) ℂ := by
  rw [mem_unitaryGroup_iff, rx_star, rx_mul, h, rx_one]

private theorem blk_mem (a b : U2) :
    rx (fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ)) ∈
      unitaryGroup (Fin (2 + 2)) ℂ := by
  apply rx_mem
  rw [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply]
  have ha := mem_unitaryGroup_iff.1 a.2
  have hb := mem_unitaryGroup_iff.1 b.2
  rw [star_eq_conjTranspose] at ha hb
  simp [ha, hb, fromBlocks_one]

private theorem bd_val (a b : U2) : (bd a b : M4) =
    rx (fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ)) :=
  Classical.epsilon_spec (p := fun k : U4 => (k : M4) =
    reindex finSumFinEquiv finSumFinEquiv (fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ)))
    ⟨⟨_, blk_mem a b⟩, rfl⟩

private theorem sw_mem : rx (fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∈
    unitaryGroup (Fin (2 + 2)) ℂ := by
  apply rx_mem
  rw [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply]
  simp [fromBlocks_one]

private theorem long_weyl_element_val : (w4 : M4) = rx (fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0) :=
  Classical.epsilon_spec (p := fun k : U4 => (k : M4) =
    reindex finSumFinEquiv finSumFinEquiv (fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0))
    ⟨⟨_, sw_mem⟩, rfl⟩

private theorem dg_mem (θ : Fin (2 + 2) → ℝ) :
    (diagonal fun i => Complex.exp (Complex.I * θ i) : M4) ∈ unitaryGroup (Fin (2 + 2)) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext i
  simp only [Pi.star_apply, RCLike.star_def]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

private theorem dg_val (θ : Fin (2 + 2) → ℝ) :
    (dg θ : M4) = diagonal fun i => Complex.exp (Complex.I * θ i) :=
  Classical.epsilon_spec (p := fun k : U4 => (k : M4) = diagonal fun i => Complex.exp (Complex.I * θ i))
    ⟨⟨_, dg_mem θ⟩, rfl⟩

private theorem bd_mul (a b a' b' : U2) : bd a b * bd a' b' = bd (a * a') (b * b') := by
  apply Subtype.ext
  show (bd a b : M4) * (bd a' b' : M4) = (bd (a * a') (b * b') : M4)
  rw [bd_val, bd_val, bd_val, rx_mul, fromBlocks_multiply]
  simp

private theorem bd_one : bd 1 1 = 1 := by
  apply Subtype.ext
  show (bd 1 1 : M4) = 1
  rw [bd_val]
  simp [fromBlocks_one, rx_one]

private theorem bd_cont : Continuous (fun p : U2 × U2 => bd p.1 p.2) := by
  refine continuous_induced_rng.2 ?_
  have : (fun p : U2 × U2 => ((bd p.1 p.2 : U4) : M4)) = fun p : U2 × U2 =>
      rx (fromBlocks (p.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (p.2 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    funext p; exact bd_val _ _
  show Continuous (fun p : U2 × U2 => ((bd p.1 p.2 : U4) : M4))
  rw [this]
  simp only [rx, reindex_apply]
  refine Continuous.matrix_submatrix ?_ _ _
  exact Continuous.matrix_fromBlocks (continuous_subtype_val.comp continuous_fst) continuous_const
    continuous_const (continuous_subtype_val.comp continuous_snd)

private theorem long_weyl_element_sq : w4 * w4 = 1 := by
  apply Subtype.ext
  show (w4 : M4) * (w4 : M4) = 1
  rw [long_weyl_element_val, rx_mul, fromBlocks_multiply]
  simp [fromBlocks_one, rx_one]

private theorem long_weyl_swaps_block_diagonal (a b : U2) : w4 * bd a b = bd b a * w4 := by
  apply Subtype.ext
  show (w4 : M4) * (bd a b : M4) = (bd b a : M4) * (w4 : M4)
  rw [long_weyl_element_val, bd_val, bd_val, rx_mul, rx_mul, fromBlocks_multiply, fromBlocks_multiply]
  simp

private theorem dg_neg (θ : Fin (2 + 2) → ℝ) : dg θ * dg (-θ) = 1 := by
  apply Subtype.ext
  show (dg θ : M4) * (dg (-θ) : M4) = 1
  rw [dg_val, dg_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← Complex.exp_add]
  simp

private theorem dg_bd (a b c d : ℝ) : dg ![a, b, c, d] = bd (tC a b) (tC c d) := by
  apply Subtype.ext
  show (dg ![a, b, c, d] : M4) = (bd (tC a b) (tC c d) : M4)
  rw [dg_val, bd_val]
  have e0 : (finSumFinEquiv (m := 2) (n := 2)).symm 0 = Sum.inl 0 := by
    rw [Equiv.symm_apply_eq]; rfl
  have e1 : (finSumFinEquiv (m := 2) (n := 2)).symm 1 = Sum.inl 1 := by
    rw [Equiv.symm_apply_eq]; rfl
  have e2 : (finSumFinEquiv (m := 2) (n := 2)).symm 2 = Sum.inr 0 := by
    rw [Equiv.symm_apply_eq]; rfl
  have e3 : (finSumFinEquiv (m := 2) (n := 2)).symm 3 = Sum.inr 1 := by
    rw [Equiv.symm_apply_eq]; rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rx, reindex_apply, mul_comm, e0, e1, e2, e3]

private theorem chi_inj (ν ν' : Fin (2 + 2) → ℤ) (h : ∀ θ, chi ν θ = chi ν' θ) : ν = ν' := by
  funext i
  by_contra hne
  have hd : ((ν i - ν' i : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 hne
  set t : ℝ := Real.pi / ((ν i - ν' i : ℤ) : ℝ) with ht
  have h1 := h (Pi.single i t)
  simp only [chi] at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
  have s : ∀ μ : Fin (2 + 2) → ℤ, ∑ j, (μ j : ℂ) * ((Pi.single i t : Fin (2 + 2) → ℝ) j : ℂ) = (μ i : ℂ) * t := by
    intro μ
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  rw [s, s] at hn
  have hdC : ((ν i : ℂ) - (ν' i : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 hne
  have htC : (t : ℂ) = (Real.pi : ℂ) / ((ν i : ℂ) - (ν' i : ℂ)) := by
    simp [ht]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : ((ν i : ℂ) - (ν' i : ℂ)) * t = 2 * n * Real.pi := by
    have : Complex.I * (((ν i : ℂ) - (ν' i : ℂ)) * t) = Complex.I * (2 * n * Real.pi) := by
      linear_combination hn
    exact mul_left_cancel₀ Complex.I_ne_zero this
  rw [htC, mul_div_cancel₀ _ hdC] at key
  have k2 : (1 : ℂ) = 2 * n := by
    apply mul_right_cancel₀ hpi
    linear_combination key
  have k3 : (1 : ℤ) = 2 * n := by exact_mod_cast k2
  omega

private noncomputable def hm : Measure U4 := Measure.haarMeasure ⊤

private theorem hm_haar : Haar4 hm ∧ hm.IsOpenPosMeasure := by
  haveI : hm.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  haveI : IsProbabilityMeasure hm := ⟨by
    simpa [hm] using Measure.haarMeasure_self (G := U4) (K₀ := ⊤)⟩
  haveI : hm.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    haveI : (Measure.map (· * g) hm).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right hm g
    haveI : IsProbabilityMeasure (Measure.map (· * g) hm) :=
      Measure.isProbabilityMeasure_map (continuous_mul_right g).measurable.aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  haveI : hm.IsInvInvariant := by
    refine ⟨?_⟩
    haveI : hm.inv.IsHaarMeasure :=
      { lt_top_of_isCompact := fun K hK => by
          rw [Measure.inv_apply]; exact hK.inv.measure_lt_top
        toIsOpenPosMeasure := ⟨fun U hU hne => by
          rw [Measure.inv_apply]; exact hU.inv.measure_ne_zero hm (by simpa using hne)⟩ }
    haveI : IsProbabilityMeasure hm.inv := by
      rw [Measure.inv]; exact Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  exact ⟨⟨inferInstance, fun k => measurePreserving_mul_left hm k,
    fun k => measurePreserving_mul_right hm k, Measure.measurePreserving_inv hm⟩, inferInstance⟩

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4 :
    (∀ a b : U2, (bd a b : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) = reindex finSumFinEquiv finSumFinEquiv (fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ))) ∧
      (∀ a b a' b', bd a b * bd a' b' = bd (a * a') (b * b')) ∧ bd 1 1 = 1 ∧ (∀ a b, (bd a b)⁻¹ = bd a⁻¹ b⁻¹) ∧ Continuous (fun p : U2 × U2 => bd p.1 p.2) ∧
      w4 * w4 = 1 ∧ (∀ a b, w4 * bd a b = bd b a * w4) ∧ (∀ θ, (dg θ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) = diagonal fun i => Complex.exp (Complex.I * θ i)) ∧
      (∀ a b c d : ℝ, dg ![a, b, c, d] = bd (tC a b) (tC c d)) ∧ (∀ θ, (dg θ)⁻¹ = dg (-θ)) ∧
      (∀ ν ν', (∀ θ, chi ν θ = chi ν' θ) → ν = ν') ∧ CompactSpace U4 ∧ ∃ μ : Measure U4, Haar4 μ ∧ μ.IsOpenPosMeasure := by
  refine ⟨bd_val, bd_mul, bd_one, fun a b => ?_, bd_cont, long_weyl_element_sq, long_weyl_swaps_block_diagonal, dg_val, dg_bd,
    fun θ => inv_eq_of_mul_eq_one_right (dg_neg θ), chi_inj, inferInstance, hm, hm_haar.1, hm_haar.2⟩
  apply inv_eq_of_mul_eq_one_right
  rw [bd_mul, mul_inv_cancel, mul_inv_cancel, bd_one]
