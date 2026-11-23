import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CommuteCenterRtInfGL
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.AbsFar

open NumberField UpperTheory.ConvolutionTheory.BW

private theorem rho_le {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} {S : Set (Pl E)}
    (d : Dat S n) (j : Fin d.len) : ‖(d.rho j : ℂ)‖ ≤ n := by
  have h : ∑ l, d.size l = n := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := d.idx)
      (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  have h' : ∀ s : Finset (Fin d.len), 0 ≤ ∑ l ∈ s, (d.size l : ℝ) ∧ ∑ l ∈ s, (d.size l : ℝ) ≤ n := fun s => by
    refine ⟨Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _, ?_⟩
    have := (Finset.sum_le_sum_of_subset (f := d.size) (Finset.subset_univ s)).trans h.le
    exact_mod_cast this
  rw [Complex.norm_real, Real.norm_eq_abs, Dat.rho, abs_le]
  have h1 := h' (Finset.Iio j)
  have h2 := h' (Finset.Ioi j)
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem UpperTheory.ConvolutionTheory.BW.far :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.Far E := by
  intro E _ _ _ n C hC
  obtain ⟨B, hB⟩ := absFar (E →+* ℂ) n C (∑ _p : (E →+* ℂ) × Fin n, (n : ℝ))
  refine ⟨B + n, fun S d φ hφ hs ⟨τ, i, hi⟩ => ?_⟩
  obtain ⟨A, _, _, _, _, Z, H, I, t, -, -, h⟩ := exists_sys d hC
  have h0 := hB _ A _ d.len Z H I t _ _ _ _ _ h (fun j => ?_) ⟨(τ, i), ?_⟩
  · exact LinearMap.congr_fun h0 ⟨φ, hφ, hs⟩
  · simp only [Dat.lamR]
    rw [Finset.sum_add_distrib, ((datBasics E).2 S n d).2.2.1 j, zero_add]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun p _ => rho_le d _).trans ?_)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.cast_nonneg _
  · have h1 := norm_sub_le (d.lamR (τ, i)) (d.rho (d.idx i) : ℂ)
    have h2 : d.lamR (τ, i) - (d.rho (d.idx i) : ℂ) = d.lam τ i := add_sub_cancel_right _ _
    rw [h2] at h1
    linarith [rho_le d (d.idx i)]
