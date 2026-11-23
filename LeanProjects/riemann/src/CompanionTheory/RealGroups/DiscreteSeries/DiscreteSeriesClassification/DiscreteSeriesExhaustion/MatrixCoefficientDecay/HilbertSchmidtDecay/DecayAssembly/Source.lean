import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.Imports

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem source_gen (hL : N.LeftRule) {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (A : Matrix (Fin n) (Fin n) ℂ) (τ : S7.UJ ε → ℝ) (C : ℝ)
    (hC : ∀ (x : PSub ε A) (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ nilpC A → 0 ≤ τ x →
      Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Y * (S7.toM (x : S7.UJ ε))⁻¹) ≤ C * Real.exp (-2 * τ x) * Formalism.REAL.hs Y)
    (i : D × List (Fin n)) (m : ℕ) (Y : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (v : Fin m → (path ⟨D, E, hK.gl⟩ χ ss).V) (hY : ∀ k, Y k ∈ nilpC A) :
    ∃ T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ h ∈ T, h ∈ SS σ D E hK.gl χ ss) ∧
      ∀ x : PSub ε A, 0 ≤ τ x →
        ‖famP σ D E hK.gl χ ss i (∑ k, actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k)) (S7.toM (x : S7.UJ ε))‖ ≤
          Real.exp (-τ x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖ := by
  classical
  obtain ⟨l, hl⟩ := hL n ε H σ D E hK χ ss hU i
  let Lf : Fin n → Fin n → (path ⟨D, E, hK.gl⟩ χ ss).V → (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
    fun c d w => (l c d).sum (fun i' r => r • famP σ D E hK.gl χ ss i' w)
  have hLf_mem : ∀ c d w, Lf c d w ∈ SS σ D E hK.gl χ ss := fun c d w =>
    Submodule.sum_mem _ (fun i' _ => Submodule.smul_mem _ _ (gen_mem σ D E hK.gl χ ss i' w))
  have hLf_apply : ∀ c d w g, Lf c d w g = (l c d).sum (fun i' r => r * famP σ D E hK.gl χ ss i' w g) := by
    intro c d w g
    simp only [Lf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

  have hmat : ∀ (g Y' : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n),
      (g * Y' * g⁻¹) c d = ∑ a, ∑ b, Y' a b * (g * Matrix.single a b (1 : ℂ) * g⁻¹) c d := by
    intro g Y' c d
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y']
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show Matrix.single a b (Y' a b) = Y' a b • Matrix.single a b (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  have hcomm : ∀ (F : Fin n → Fin n → Fin n → Fin n → ℂ),
      ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
    intro F
    have h := Finset.sum_comm (s := (Finset.univ : Finset (Fin n × Fin n))) (t := (Finset.univ : Finset (Fin n × Fin n)))
      (f := fun p q => F p.1 p.2 q.1 q.2)
    simpa only [Fintype.sum_prod_type] using h

  have hid : ∀ g, Formalism.REAL.inUJ ε g → famP σ D E hK.gl χ ss i (∑ k, actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k)) g =
      ∑ k, ∑ c, ∑ d, (g * Y k * g⁻¹) c d * Lf c d (v k) g := by
    intro g hg
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hact : actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k) = ∑ a, ∑ b, Y k a b • (path ⟨D, E, hK.gl⟩ χ ss).E a b (v k) := by
      simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [hact]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hl _ _ _ g hg, ← hLf_apply]
    simp only [hmat g (Y k), Finset.mul_sum, Finset.sum_mul]
    rw [hcomm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring

  have hent : ∀ (x : PSub ε A) (k : Fin m) (c d : Fin n), 0 ≤ τ x →
      ‖(S7.toM (x : S7.UJ ε) * Y k * (S7.toM (x : S7.UJ ε))⁻¹) c d‖ ≤
        Real.exp (-τ x) * Real.sqrt (C * Formalism.REAL.hs (Y k)) := by
    intro x k c d hx
    set M := S7.toM (x : S7.UJ ε) * Y k * (S7.toM (x : S7.UJ ε))⁻¹
    have e1 : ‖M c d‖ ^ 2 ≤ Formalism.REAL.hs M := by
      unfold Formalism.REAL.hs
      exact (Finset.single_le_sum (f := fun j => ‖M c j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ d)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ c))
    have hexp2 : Real.exp (-τ x) ^ 2 = Real.exp (-2 * τ x) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : Formalism.REAL.hs M ≤ (C * Formalism.REAL.hs (Y k)) * Real.exp (-τ x) ^ 2 := by
      rw [hexp2]
      calc Formalism.REAL.hs M ≤ C * Real.exp (-2 * τ x) * Formalism.REAL.hs (Y k) := hC x (Y k) (hY k) hx
        _ = (C * Formalism.REAL.hs (Y k)) * Real.exp (-2 * τ x) := by ring
    calc ‖M c d‖ = Real.sqrt (‖M c d‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((C * Formalism.REAL.hs (Y k)) * Real.exp (-τ x) ^ 2) := Real.sqrt_le_sqrt (e1.trans e2)
      _ = Real.sqrt (C * Formalism.REAL.hs (Y k)) * Real.exp (-τ x) := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
      _ = Real.exp (-τ x) * Real.sqrt (C * Formalism.REAL.hs (Y k)) := mul_comm _ _

  let hq : Fin m × Fin n × Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) := fun q =>
    ((Real.sqrt (C * Formalism.REAL.hs (Y q.1)) : ℝ) : ℂ) • Lf q.2.1 q.2.2 (v q.1)
  obtain ⟨T, hTS, hT⟩ := absorb (SS σ D E hK.gl χ ss) (Finset.univ : Finset (Fin m × Fin n × Fin n)) hq
    (fun q _ => Submodule.smul_mem _ _ (hLf_mem _ _ _)) 1 le_rfl
  refine ⟨T, hTS, fun x hx => ?_⟩
  have hg : Formalism.REAL.inUJ ε (S7.toM (x : S7.UJ ε)) := (x : S7.UJ ε).2
  rw [hid _ hg]
  set g := S7.toM (x : S7.UJ ε)
  have hq_norm : ∀ q : Fin m × Fin n × Fin n, ‖hq q g‖ =
      Real.sqrt (C * Formalism.REAL.hs (Y q.1)) * ‖Lf q.2.1 q.2.2 (v q.1) g‖ := by
    intro q
    simp only [hq, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  calc ‖∑ k, ∑ c, ∑ d, (g * Y k * g⁻¹) c d * Lf c d (v k) g‖
      ≤ ∑ k, ∑ c, ∑ d, ‖(g * Y k * g⁻¹) c d‖ * ‖Lf c d (v k) g‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
        rw [norm_mul]
    _ ≤ ∑ k, ∑ c, ∑ d, Real.exp (-τ x) * (Real.sqrt (C * Formalism.REAL.hs (Y k)) * ‖Lf c d (v k) g‖) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hent x k c d hx) (norm_nonneg _)
    _ = Real.exp (-τ x) * ∑ q : Fin m × Fin n × Fin n, ‖hq q g‖ ^ 1 := by
        simp only [pow_one, hq_norm, Finset.mul_sum, Fintype.sum_prod_type]
    _ ≤ Real.exp (-τ x) * ∑ h ∈ T, ‖h g‖ ^ 1 :=
        mul_le_mul_of_nonneg_left (hT g) (Real.exp_pos _).le
    _ = Real.exp (-τ x) * ∑ h ∈ T, ‖h g‖ := by simp only [pow_one]

end CompanionTheory.RgExh.Dec.L.SA
