import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem blkM_castSucc_castSucc {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (i j : Fin n) : blkM b u d i.castSucc j.castSucc = b i j := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h]

theorem blkM_castSucc_last {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (i : Fin n) : blkM b u d i.castSucc (Fin.last n) = u i := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h, finSumFinEquiv_symm_last]

theorem blkM_last_last {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    blkM b u d (Fin.last n) (Fin.last n) = d := by
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]

theorem blkM_last_castSucc {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (j : Fin n) : blkM b u d (Fin.last n) j.castSucc = star (u j) := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h, finSumFinEquiv_symm_last]

theorem blkM_add {n : ℕ} (b b' : Matrix (Fin n) (Fin n) ℂ) (u u' : Fin n → ℂ) (d d' : ℝ) :
    blkM (b + b') (u + u') (d + d') = blkM b u d + blkM b' u' d' := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [blkM_last_last]
    | cast j => simp [blkM_last_castSucc]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [blkM_castSucc_last]
    | cast j => simp [blkM_castSucc_castSucc]

def upperLeftHermBlock {n : ℕ} (b : hermC (n + 1)) : hermC n :=
  ⟨(b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix Fin.castSucc Fin.castSucc,
    mem_hermC.2 ((mem_hermC.1 b.2).submatrix _)⟩

def blkEquiv (n : ℕ) : (hermC n × (Fin n → ℂ) × ℝ) ≃+ hermC (n + 1) where
  toFun x := blk x.1 x.2.1 x.2.2
  invFun b := (upperLeftHermBlock b, fun i => (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i.castSucc (Fin.last n),
    ((b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n)).re)
  left_inv x := by
    obtain ⟨b, u, d⟩ := x
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
    · ext i j
      simp [upperLeftHermBlock, blk, blkM_castSucc_castSucc]
    · ext i
      simp [blk, blkM_castSucc_last]
    · simp [blk, blkM_last_last]
  right_inv b := by
    have hb := mem_hermC.1 b.2
    apply Subtype.ext
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simp only [blk, blkM_last_last]
        have := hb.apply (Fin.last n) (Fin.last n)
        exact (Complex.conj_eq_iff_real.1 this).choose_spec ▸ by simp
      | cast j =>
        simp only [blk, blkM_last_castSucc]
        exact hb.apply _ _
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [blk, blkM_castSucc_last]
      | cast j => simp [blk, blkM_castSucc_castSucc, upperLeftHermBlock]
  map_add' x y := by
    apply Subtype.ext
    simp [blk, blkM_add]

theorem continuous_blkEquiv (n : ℕ) : Continuous (blkEquiv n) := by
  refine Continuous.subtype_mk (f := fun x : hermC n × (Fin n → ℂ) × ℝ =>
    blkM (x.1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) ?_ _
  exact continuous_blkM.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem continuous_blkEquiv_symm (n : ℕ) : Continuous (blkEquiv n).symm := by
  have h : ∀ i j : Fin (n + 1), Continuous fun b : hermC (n + 1) =>
      (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j := fun i j =>
    (continuous_apply_apply i j).comp continuous_subtype_val
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    exact h _ _
  · exact continuous_pi fun i => h _ _
  · exact Complex.continuous_re.comp (h _ _)

theorem haar_blocks (n : ℕ) (ν : Measure (hermC (n + 1))) (ν' : Measure (hermC n))
    (hν : ν.IsAddHaarMeasure) (hν' : ν'.IsAddHaarMeasure) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : hermC (n + 1) → ENNReal, Measurable F →
      ∫⁻ b, F b ∂ν = c * ∫⁻ b', ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ, F (blk b' u d) ∂volume ∂volume ∂ν' := by
  haveI := hν
  haveI := hν'
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hp : (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hm : (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ)))).IsAddHaarMeasure :=
    (blkEquiv n).isAddHaarMeasure_map _ (continuous_blkEquiv n) (continuous_blkEquiv_symm n)
  have he : Measurable (blkEquiv n) := (continuous_blkEquiv n).measurable
  refine ⟨(Measure.addHaarScalarFactor ν (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ)))) : ENNReal),
    ENNReal.coe_ne_top, fun F hF => ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ))))]
  rw [lintegral_smul_measure, lintegral_map hF he, lintegral_prod (fun a => F (blkEquiv n a)) (hF.comp he).aemeasurable]
  simp only [ENNReal.smul_def, smul_eq_mul]
  congr 1
  refine lintegral_congr fun b' => ?_
  rw [lintegral_prod]
  · rfl
  · exact ((hF.comp he).comp measurable_prodMk_left).aemeasurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
