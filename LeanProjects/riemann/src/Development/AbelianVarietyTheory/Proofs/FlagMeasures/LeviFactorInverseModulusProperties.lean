import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwDelta

variable {n : ℕ}

theorem exists_cont_detOn (V : Submodule ℂ (Fin n → ℂ)) :
    ∃ D : Matrix (Fin n) (Fin n) ℂ → ℝ, Continuous D ∧
      ∀ X, (∀ y ∈ V, X *ᵥ y ∈ V) → detOn X V = D X := by
  obtain ⟨U, hVU⟩ := Submodule.exists_isCompl V
  let p := Submodule.projectionOnto V U hVU
  let b := Module.finBasis ℂ V
  refine ⟨fun X => ‖(Matrix.of fun i k => b.repr (p (X *ᵥ (b k : Fin n → ℂ))) i).det‖, ?_, ?_⟩
  · apply Continuous.norm
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i k
    have hlin : Continuous fun y : Fin n → ℂ => b.repr (p y) i :=
      ((b.coord i).comp p).continuous_of_finiteDimensional
    exact hlin.comp (continuous_id.matrix_mulVec continuous_const)
  · intro X hX
    have h' : ∀ y ∈ V, Matrix.toLin' X y ∈ V := fun y hy => by
      simpa [Matrix.toLin'_apply] using hX y hy
    have e : ∀ k, p (X *ᵥ (b k : Fin n → ℂ)) = (Matrix.toLin' X).restrict h' (b k) := by
      intro k
      have hp : p (X *ᵥ (b k : Fin n → ℂ)) = ⟨X *ᵥ (b k : Fin n → ℂ), hX _ (b k).2⟩ :=
        Submodule.projectionOnto_apply_left hVU ⟨X *ᵥ (b k : Fin n → ℂ), hX _ (b k).2⟩
      rw [hp]
      apply Subtype.ext
      simp [LinearMap.restrict_apply, Matrix.toLin'_apply]
    rw [detOn, dif_pos h', ← LinearMap.det_toMatrix b]
    congr 2
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.of_apply, e k]

theorem detOn_one (V : Submodule ℂ (Fin n → ℂ)) : detOn (1 : Matrix (Fin n) (Fin n) ℂ) V = 1 := by
  have h' : ∀ y ∈ V, Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ) y ∈ V := fun y hy => by simpa using hy
  rw [detOn, dif_pos h']
  have hid : (Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ)).restrict h' = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (by simp [LinearMap.restrict_apply])
  rw [hid, LinearMap.det_id, norm_one]

private theorem detOn_le_one_of_unitary_of_invariant (U : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ))
    (hU : Uᴴ * U = 1) (hV : ∀ y ∈ V, U *ᵥ y ∈ V) : detOn U V ≤ 1 := by
  obtain ⟨D, hDc, hD⟩ := exists_cont_detOn V
  have hKc : IsCompact {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * X = 1} := by
    have hcl : IsClosed {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * X = 1} :=
      isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
        Metric.closedBall (0 : ℂ) 1 : Set (Matrix (Fin n) (Fin n) ℂ)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
    refine hbox.of_isClosed_subset hcl ?_
    intro X hX
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i k
    exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hX) i k
  have hUg : U ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.2 hU
  have hpow : ∀ k : ℕ, (∀ y ∈ V, U ^ k *ᵥ y ∈ V) ∧ detOn (U ^ k) V = detOn U V ^ k := by
    intro k
    induction k with
    | zero => exact ⟨fun y hy => by simpa using hy, by simpa using detOn_one V⟩
    | succ k ih =>
      have hs : ∀ y ∈ V, U ^ (k + 1) *ᵥ y ∈ V := fun y hy => by
        rw [pow_succ, ← Matrix.mulVec_mulVec]
        exact ih.1 _ (hV y hy)
      refine ⟨hs, ?_⟩
      rw [pow_succ, GlobalTheory.FlagMeas.SizeMove.detOn_mul _ _ V ih.1 hV, ih.2, pow_succ]
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hDc.continuousOn
  by_contra hlt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.mp hlt)
  have hmem : (U ^ k)ᴴ * U ^ k = 1 := Matrix.mem_unitaryGroup_iff'.1 (pow_mem hUg k)
  have hb := hC (U ^ k) hmem
  rw [← hD _ (hpow k).1, (hpow k).2, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (GlobalTheory.FlagMeas.SizeMove.detOn_nonneg U V) k)] at hb
  linarith

theorem detOn_le_one {ε : Fin n → Bool} {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    {l : Formalism.REAL.UJ ε} (hl : l ∈ maxK ε ∩ flagM ε W) (i : Fin (a + 1)) : detOn (uMat l) (W i) ≤ 1 := by
  have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
  exact detOn_le_one_of_unitary_of_invariant _ _ hl.1 (fun y hy => (hl2 i y hy).1)

theorem detOn_eq_one {ε : Fin n → Bool} {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    {l : Formalism.REAL.UJ ε} (hl : l ∈ maxK ε ∩ flagM ε W) (i : Fin (a + 1)) : detOn (uMat l) (W i) = 1 := by
  have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
  have hU : (uMat l)ᴴ * uMat l = 1 := hl.1
  have hU' : (uMat l)ᴴᴴ * (uMat l)ᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hU
  have h1 := detOn_le_one hl i
  have h2 := detOn_le_one_of_unitary_of_invariant _ (W i) hU' (fun y hy => (hl2 i y hy).2)
  have hprod : detOn ((uMat l)ᴴ) (W i) * detOn (uMat l) (W i) = 1 := by
    rw [← GlobalTheory.FlagMeas.SizeMove.detOn_mul _ _ _ (fun y hy => (hl2 i y hy).2) (fun y hy => (hl2 i y hy).1), hU,
      detOn_one]
  have h3 := GlobalTheory.FlagMeas.SizeMove.detOn_nonneg (uMat l) (W i)
  have h4 := GlobalTheory.FlagMeas.SizeMove.detOn_nonneg ((uMat l)ᴴ) (W i)
  exact le_antisymm h1 (by nlinarith)

theorem measurable_layerProd {a : ℕ} (j : Fin a → ℕ) :
    Measurable fun τ : Fin a → ℝ => layerProd n 1 j τ id := by
  unfold layerProd
  fun_prop

theorem continuousAt_layerProd {a : ℕ} (j : Fin a → ℕ) :
    Filter.Tendsto (fun τ : Fin a → ℝ => layerProd n 1 j τ id) (nhds 1) (nhds 1) := by
  have hc : ContinuousAt (fun τ : Fin a → ℝ => layerProd n 1 j τ id) 1 := by
    unfold layerProd
    fun_prop (disch := simp)
  have h1 : layerProd n 1 j (1 : Fin a → ℝ) id = 1 := by simp [layerProd]
  simpa [h1] using hc.tendsto

open scoped Matrix.Norms.Frobenius in
theorem exists_ball {s : Set (Matrix (Fin n) (Fin n) ℂ)} (hs : s ∈ nhds 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ X, nrm (X - 1) < t → X ∈ s := by
  obtain ⟨t, ht, hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨t, ht, fun X hX => hsub ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, ← nrm_eq]
  exact hX

theorem dlt_props : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), Measurable (dlt (ε := ε) j W) ∧ (∀ l ∈ maxK ε ∩ flagM ε W, ∀ m ∈ flagM ε W, dlt j W (m * l) = dlt j W m) ∧ ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ m ∈ flagM ε W, nrm (uMat m - 1) < t → dlt j W m ≤ ENNReal.ofReal (1 + η) ∧ 1 ≤ ENNReal.ofReal (1 + η) * dlt j W m := by
  intro n ε a j W
  refine ⟨?_, ?_, ?_⟩
  · unfold dlt
    exact ENNReal.measurable_ofReal.comp ((measurable_layerProd j).comp
      (measurable_pi_lambda _ fun i => measurable_locSize_uMat n ε a j W i))
  · intro l hl m hm
    have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
    have hm2 : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hmul : uMat (m * l) = uMat m * uMat l := rfl
    have hloc : locSize j W (uMat (m * l)) = locSize j W (uMat m) := by
      funext i
      simp only [locSize]
      rw [hmul,
        GlobalTheory.FlagMeas.SizeMove.detOn_mul (uMat m) (uMat l) (W i.succ) (fun y hy => (hm2 i.succ y hy).1)
          (fun y hy => (hl2 i.succ y hy).1),
        GlobalTheory.FlagMeas.SizeMove.detOn_mul (uMat m) (uMat l) (W i.castSucc) (fun y hy => (hm2 i.castSucc y hy).1)
          (fun y hy => (hl2 i.castSucc y hy).1),
        detOn_eq_one hl i.succ, detOn_eq_one hl i.castSucc, mul_one, mul_one]
    unfold dlt
    rw [hloc]
  · intro η hη
    choose D hDc hD using fun i : Fin (a + 1) => exists_cont_detOn (W i)
    have hD1 : ∀ i, D i 1 = 1 := fun i => by
      rw [← hD i 1 (fun y hy => by simpa using hy), detOn_one]
    set G : Matrix (Fin n) (Fin n) ℂ → Fin a → ℝ :=
      fun X i => (D i.succ X / D i.castSucc X) ^ (-(1 : ℝ) / j i) with hGdef
    have hG : Filter.Tendsto G (nhds 1) (nhds 1) := by
      rw [tendsto_pi_nhds]
      intro i
      have hc : ContinuousAt (fun X => (D i.succ X / D i.castSucc X) ^ (-(1 : ℝ) / j i)) 1 :=
        ((hDc _).continuousAt.div (hDc _).continuousAt (by simp [hD1])).rpow_const
          (Or.inl (by simp [hD1]))
      have ht := hc.tendsto
      simp only [hD1, div_one, Real.one_rpow] at ht
      exact ht
    have hF := (continuousAt_layerProd (n := n) j).comp hG
    have hpos : 0 < 1 + η := by linarith
    have hU : Set.Ioo (1 / (1 + η)) (1 + η) ∈ nhds (1 : ℝ) :=
      Ioo_mem_nhds ((div_lt_one hpos).2 (by linarith)) (by linarith)
    obtain ⟨t, ht, hball⟩ := exists_ball (Filter.tendsto_def.1 hF _ hU)
    refine ⟨t, ht, fun m hm hmt => ?_⟩
    have hm2 : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hin := hball _ hmt
    have hGm : G (uMat m) = locSize j W (uMat m) := by
      funext i
      simp only [hGdef, locSize]
      rw [hD i.succ _ (fun y hy => (hm2 i.succ y hy).1), hD i.castSucc _ (fun y hy => (hm2 i.castSucc y hy).1)]
    simp only [Set.mem_preimage, Function.comp_apply, hGm, Set.mem_Ioo] at hin
    obtain ⟨hlo, hhi⟩ := hin
    unfold dlt
    refine ⟨ENNReal.ofReal_le_ofReal hhi.le, ?_⟩
    rw [← ENNReal.ofReal_mul hpos.le, ENNReal.one_le_ofReal]
    rw [div_lt_iff₀ hpos] at hlo
    linarith [mul_comm (layerProd n 1 j (locSize j W (uMat m)) id) (1 + η)]

end GlobalTheory.IwDelta
