import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLieEUnitaryGroupIffOfInvolutiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityLieAlgebraOfOmegaDensity

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.TubeLie

open GlobalTheory.OmegaFrobenius (realify unrealify_realify)

theorem norm_sq_unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp only [unrealify, Real.norm_eq_abs, sq_abs]
  ring

theorem skew_top {k : ℕ} (X : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) (i j : Fin k) :
    conj (unrealify (X : EuclideanSpace ℝ _) j i) + unrealify (X : EuclideanSpace ℝ _) i j = 0 := by
  have h := (GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive k 1 (X : EuclideanSpace ℝ _) (by simp)).1 X.2
  have h' := congrFun (congrFun h i) j
  simpa [Matrix.conjTranspose_apply, Complex.star_def] using h'

theorem lie_entry {k : ℕ} (η : ℝ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) :
    (Mᴴ * Hd k η + Hd k η * M) i j =
      conj (M j i) * (if j = Fin.last k then (η : ℂ) else 1) + (if i = Fin.last k then (η : ℂ) else 1) * M i j := by
  simp [Hd, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

private theorem Hd_mul_self_eq_one {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) : Hd k η * Hd k η = 1 := by
  unfold Hd
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> rcases hη with rfl | rfl <;> norm_num

theorem tang_mem {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) (v : Par k) :
    realify (k + 1) (tang η v) ∈ lieE (UH (Hd k η)) := by
  rw [GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive _ _ _ (Hd_mul_self_eq_one hη), GlobalTheory.OmegaFrobenius.unrealify_realify]
  have hs := skew_top v.1
  ext i j
  rw [lie_entry, Matrix.zero_apply]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [tang, blk, hv, hs] <;> ring

theorem unrealify_add {m : ℕ} (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem unrealify_smul {m : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = c • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem tang_add {k : ℕ} (η : ℝ) (v w : Par k) : tang η (v + w) = tang η v + tang η w := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [tang, blk, hv, unrealify_add, add_div] <;> ring

theorem tang_smul {k : ℕ} (η c : ℝ) (v : Par k) : tang η (c • v) = c • tang η v := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [tang, blk, hv, unrealify_smul, Complex.real_smul] <;> ring

def tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) : Par k →ₗ[ℝ] lieE (UH (Hd k η)) where
  toFun v := ⟨realify (k + 1) (tang η v), tang_mem hη v⟩
  map_add' v w := by ext1; simp [tang_add]
  map_smul' c v := by ext1; simp [tang_smul]

theorem unrealify_tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) (v : Par k) :
    unrealify (tangL hη v : EuclideanSpace ℝ _) = tang η v := by
  exact GlobalTheory.OmegaFrobenius.unrealify_realify (tang η v)

theorem norm_sq_tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) (v : Par k) :
    ‖tangL hη v‖ ^ 2 = ‖v.1‖ ^ 2 + (‖v.2.1‖ ^ 2 + ‖v.2.2‖ ^ 2) := by
  have hη1 : ‖(η : ℂ)‖ = 1 := by rcases hη with rfl | rfl <;> simp
  have e1 : ‖tangL hη v‖ ^ 2 = ∑ i, ∑ j, ‖tang η v i j‖ ^ 2 := by
    have h := norm_sq_unrealify (tangL hη v).1
    rw [unrealify_tangL] at h
    rw [← h, Submodule.coe_norm]
  have e2 : ‖v.1‖ ^ 2 = ∑ i, ∑ j, ‖unrealify v.1.1 i j‖ ^ 2 := by
    rw [← norm_sq_unrealify, Submodule.coe_norm]
  have e3 : ‖v.2.2‖ ^ 2 = ∑ j, ‖v.2.2 j‖ ^ 2 := EuclideanSpace.norm_sq_eq _
  rw [e1, e2, e3]
  simp only [Fin.sum_univ_castSucc, tang, blk, Fin.lastCases_castSucc, Fin.lastCases_last, hv]
  have hc : ∀ z : ℂ, ‖z / (√2 : ℝ)‖ ^ 2 = ‖z‖ ^ 2 / 2 := by
    intro z
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
  have hb : ∀ z : ℂ, ‖-(η : ℂ) * (starRingEnd ℂ) (z / (√2 : ℝ))‖ ^ 2 = ‖z‖ ^ 2 / 2 := by
    intro z
    rw [norm_mul, norm_neg, hη1, one_mul, Complex.norm_conj, hc]
  have hd : ‖((v.2.1 : ℝ) : ℂ) * Complex.I‖ ^ 2 = ‖v.2.1‖ ^ 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  simp only [hb, hc, hd, Finset.sum_add_distrib]
  linarith [Finset.sum_div Finset.univ (fun x => ‖v.2.2.ofLp x‖ ^ 2) (2 : ℝ)]

theorem tangL_surjective {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) : Function.Surjective (tangL (k := k) hη) := by
  intro y
  set M := unrealify (y : EuclideanSpace ℝ (Fin (k + 1) × Fin (k + 1) × Bool)) with hMdef
  have hM := (GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive _ _ _ (Hd_mul_self_eq_one hη)).1 y.2
  have e : ∀ i j, (starRingEnd ℂ) (M j i) * (if j = Fin.last k then (η : ℂ) else 1) +
      (if i = Fin.last k then (η : ℂ) else 1) * M i j = 0 := by
    intro i j
    have h := congrFun (congrFun hM i) j
    rwa [lie_entry, Matrix.zero_apply] at h
  let A : Matrix (Fin k) (Fin k) ℂ := fun i j => M i.castSucc j.castSucc
  have hA : GlobalTheory.OmegaFrobenius.realify k A ∈ lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) := by
    rw [GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive _ _ _ (by simp), GlobalTheory.OmegaFrobenius.unrealify_realify]
    ext i j
    have h := e i.castSucc j.castSucc
    simp [Fin.castSucc_ne_last] at h
    simp only [Matrix.mul_one, Matrix.one_mul]
    exact h
  have hll : (M (Fin.last k) (Fin.last k)).re = 0 := by
    have h := congrArg Complex.re (e (Fin.last k) (Fin.last k))
    rcases hη with rfl | rfl <;> simp at h <;> linarith
  have h2 : ((√2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  refine ⟨(⟨GlobalTheory.OmegaFrobenius.realify k A, hA⟩, (M (Fin.last k) (Fin.last k)).im,
    WithLp.toLp 2 (fun j => ((√2 : ℝ) : ℂ) * M (Fin.last k) j.castSucc)), ?_⟩
  apply Subtype.ext
  rw [← (GlobalTheory.OmegaFrobenius.realify (k + 1)).apply_symm_apply (y : EuclideanSpace ℝ _)]
  show GlobalTheory.OmegaFrobenius.realify (k + 1) (tang η _) = GlobalTheory.OmegaFrobenius.realify (k + 1) M
  congr 1
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · apply Complex.ext <;> simp [tang, blk, hll]
  · simp [tang, blk, hv, h2]
  · have h := e i.castSucc (Fin.last k)
    simp [Fin.castSucc_ne_last] at h
    simp [tang, blk, hv, h2]
    linear_combination -h
  · have hu : unrealify (GlobalTheory.OmegaFrobenius.realify k A) = A := GlobalTheory.OmegaFrobenius.unrealify_realify A
    simp only [tang, blk, Fin.lastCases_castSucc]
    exact congrFun (congrFun hu i) j

def tangIsom {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) :
    WithLp 2 (lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) × WithLp 2 (ℝ × EuclideanSpace ℂ (Fin k))) →ₗᵢ[ℝ]
      lieE (UH (Hd k η)) where
  toFun p := tangL hη (p.fst, p.snd.fst, p.snd.snd)
  map_add' p q := by rw [← map_add]; rfl
  map_smul' c p := by rw [← map_smul]; rfl
  norm_map' p := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    exact norm_sq_tangL hη _

theorem measurePreserving_of_isom {A B C D : Type} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    [FiniteDimensional ℝ C] [MeasurableSpace C] [BorelSpace C] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
    (J : WithLp 2 (A × WithLp 2 (B × C)) →ₗᵢ[ℝ] D) (hs : Function.Surjective J) :
    MeasurePreserving (fun v : A × B × C => J (WithLp.toLp 2 (v.1, WithLp.toLp 2 v.2)))
      (volume.prod (volume.prod volume)) volume := by
  have h1 : MeasurePreserving (Prod.map (id : A → A) (WithLp.toLp 2 : B × C → WithLp 2 (B × C)))
      (volume.prod (volume.prod volume)) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod (WithLp.volume_preserving_toLp B C)
  have h2 := WithLp.volume_preserving_toLp A (WithLp 2 (B × C))
  have h3 := (LinearIsometryEquiv.ofSurjective J hs).measurePreserving
  exact h3.comp (h2.comp h1)

theorem measurePreserving_tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) :
    MeasurePreserving (tangL (k := k) hη) (volume.prod (volume.prod volume)) volume := by
  have hsurj : Function.Surjective (tangIsom (k := k) hη) := by
    intro y
    obtain ⟨v, rfl⟩ := tangL_surjective hη y
    exact ⟨WithLp.toLp 2 (v.1, WithLp.toLp 2 (v.2.1, v.2.2)), rfl⟩
  exact measurePreserving_of_isom (tangIsom hη) hsurj

theorem exists_tang_equiv : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∃ L : Par k ≃L[ℝ] lieE (UH (Hd k η)), (∀ v : Par k, unrealify ((L v : lieE (UH (Hd k η))) : EuclideanSpace ℝ _) = tang η v) ∧ ∀ ρ : ℝ, 0 < ρ → volume (L '' Metric.ball (0 : Par k) ρ) = volume (Metric.ball (0 : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) ρ) * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))) := by
  intro k η hk hη
  have hinj : Function.Injective (tangL (k := k) hη) := by
    refine (injective_iff_map_eq_zero (tangL hη)).2 fun v hv => ?_
    have h := norm_sq_tangL hη v
    rw [hv, norm_zero] at h
    have a := sq_nonneg ‖v.1‖
    have b := sq_nonneg ‖v.2.1‖
    have c := sq_nonneg ‖v.2.2‖
    have h1 : ‖v.1‖ ^ 2 = 0 := by nlinarith
    have h2 : ‖v.2.1‖ ^ 2 = 0 := by nlinarith
    have h3 : ‖v.2.2‖ ^ 2 = 0 := by nlinarith
    simp only [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h1 h2 h3
    exact Prod.ext h1 (Prod.ext h2 h3)
  let Lₗ := LinearEquiv.ofBijective (tangL hη) ⟨hinj, tangL_surjective hη⟩
  let L : Par k ≃L[ℝ] lieE (UH (Hd k η)) := Lₗ.toContinuousLinearEquiv
  refine ⟨L, fun v => unrealify_tangL hη v, fun ρ hρ => ?_⟩
  let e := L.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving e (volume.prod (volume.prod volume)) volume :=
    ⟨(measurePreserving_tangL hη).measurable, (measurePreserving_tangL hη).map_eq⟩
  have hpre := hmp.measure_preimage_equiv (e '' Metric.ball (0 : Par k) ρ)
  rw [MeasurableEquiv.preimage_image] at hpre
  change volume (e '' Metric.ball (0 : Par k) ρ) = _
  rw [← hpre]
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hz : (0 : Par k) = (0, 0, 0) := rfl
  rw [hz, ← ball_prod_same, ← ball_prod_same, Measure.prod_prod, Measure.prod_prod, Real.volume_ball,
    InnerProductSpace.volume_ball (0 : EuclideanSpace ℂ (Fin k))]
  have hf : Module.finrank ℝ (EuclideanSpace ℂ (Fin k)) = 2 * k := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace_fin]
  have hG : Real.Gamma (((2 * k : ℕ) : ℝ) / 2 + 1) = (k.factorial : ℝ) := by
    rw [show ((2 * k : ℕ) : ℝ) / 2 = (k : ℝ) by push_cast; ring, Real.Gamma_nat_eq_factorial]
  have hπ : √Real.pi ^ (2 * k) = Real.pi ^ k := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hf, hG, hπ]
  congr 1
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ρ ^ (2 * k)),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * ρ)]
  congr 1
  ring

end GlobalTheory.TubeLie
