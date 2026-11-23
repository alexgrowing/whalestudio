import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousRenameCastLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianFirstCoordsMeasurePreserving

set_option autoImplicit false

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.UnitProductCombination.XB

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop GlobalTheory.ChowHt

theorem mean_incl (B N n δ : ℕ) (f : MvPolynomial (Fin B × Fin N) ℂ) (hN : 0 < N)
    (hNn : N ≤ n) (hf : f ≠ 0) (hm : IsMultiHomogeneous (fun _ => δ) f) :
    blockSphereMean B n (linSubst (Matrix.of fun (j : Fin N) (k : Fin n) =>
        if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) f) =
      blockSphereMean B N f + (B : ℝ) * δ * ((harmonic (N - 1) : ℝ) - (harmonic (n - 1) : ℝ)) / 2 := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  rw [linSubst_incl hNn]
  set e : Fin B × Fin N → Fin B × Fin n := fun p => (p.1, Fin.castLE hNn p.2) with he
  have heinj : Function.Injective e := by
    intro p q hpq
    simp only [he, Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Fin.castLE_injective hNn hpq.2)
  set g := rename e f with hgdef
  have hg : g ≠ 0 := fun h0 => hf (rename_injective e heinj (by rw [← hgdef, h0, map_zero]))
  have hgm : IsMultiHomogeneous (fun _ => δ) g := isMultiHomogeneous_rename_castLE hNn _ f hm
  have hIn := (gauss_blockMean hn δ g hg hgm).2
  have hIN := (gauss_blockMean hN δ f hf hm).2
  have : IsProbabilityMeasure (gaussProb N) := isProbabilityMeasure_gaussProb hN
  have hproj : MeasurePreserving (fun (x : Fin B → EuclideanSpace ℂ (Fin n)) b => firstCoords hNn (x b))
      (Measure.pi fun _ => gaussProb n) (Measure.pi fun _ => gaussProb N) :=
    measurePreserving_pi _ _ fun _ => GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb N n hNn
  have hev : ∀ x : Fin B → EuclideanSpace ℂ (Fin n),
      eval (fun p => WithLp.ofLp (x p.1) p.2) g =
        eval (fun p => WithLp.ofLp (firstCoords hNn (x p.1)) p.2) f := by
    intro x
    rw [hgdef, eval_rename]
    rfl
  have hmeas : Measurable fun y : Fin B → EuclideanSpace ℂ (Fin N) =>
      Real.log ‖eval (fun p => WithLp.ofLp (y p.1) p.2) f‖ := by
    refine Real.measurable_log.comp (Continuous.measurable ?_)
    exact continuous_norm.comp ((continuous_eval f).comp (by fun_prop))
  have hchange : ∫ x, Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖
        ∂(Measure.pi fun _ => gaussProb n) =
      ∫ y, Real.log ‖eval (fun p => WithLp.ofLp (y p.1) p.2) f‖
        ∂(Measure.pi fun _ => gaussProb N) := by
    simp_rw [hev]
    rw [← hproj.map_eq, integral_map hproj.measurable.aemeasurable hmeas.aestronglyMeasurable]
  rw [hchange, hIN] at hIn
  have hr := radRatio_sub hN hn
  linear_combination hIn.symm + (B : ℝ) * δ * hr

theorem exists_unitary {N m : ℕ} (Q : Matrix (Fin N) (Fin m) ℂ)
    (hQ : ∀ z : Fin N → ℂ, ∑ a, ‖∑ i, Q i a * z i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) :
    N ≤ m ∧ ∃ U : Matrix (Fin m) (Fin m) ℂ,
      (∀ x : EuclideanSpace ℂ (Fin m), ‖Matrix.toEuclideanLin U x‖ = ‖x‖) ∧
      Q = (Matrix.of fun (j : Fin N) (k : Fin m) => if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) * U := by
  let T : EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) :=
    ⟨Matrix.toEuclideanLin Q.transpose, fun z => by
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      exact congrArg _ (hQ z.ofLp)⟩
  have hle : N ≤ m := by
    have := LinearMap.finrank_le_finrank_of_injective (f := T.toLinearMap) T.injective
    simpa using this
  refine ⟨hle, ?_⟩
  have ho : Orthonormal ℂ (T ∘ EuclideanSpace.basisFun (Fin N) ℂ) :=
    (EuclideanSpace.basisFun (Fin N) ℂ).orthonormal.comp_linearIsometry T
  let v : Fin m → EuclideanSpace ℂ (Fin m) := fun k =>
    if h : (k : ℕ) < N then T (EuclideanSpace.basisFun (Fin N) ℂ ⟨k, h⟩) else 0
  have hv : Orthonormal ℂ (({k : Fin m | (k : ℕ) < N}).restrict v) := by
    have h1 := ho.comp (fun k : {k : Fin m | (k : ℕ) < N} => (⟨k.1, k.2⟩ : Fin N))
      fun a b h => Subtype.ext (Fin.ext (congrArg Fin.val h :))
    convert h1 using 1
    funext k
    exact dif_pos k.2
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨Matrix.of fun k a => b k a, fun x => ?_, ?_⟩
  · let x' : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 fun a => starRingEnd ℂ (x a)
    have h1 := b.sum_sq_norm_inner_right x'
    have h2 : ‖x'‖ = ‖x‖ := by
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      simp [x']
    rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg x), ← h2, ← h1]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [← Complex.norm_conj]
    congr 1
    change starRingEnd ℂ (∑ a, b k a * x a) = _
    simp only [PiLp.inner_apply, RCLike.inner_apply, map_sum, map_mul, x']
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  · ext j a
    rw [Matrix.mul_apply, Fintype.sum_eq_single (Fin.castLE hle j)]
    · have hj : ((Fin.castLE hle j : Fin m) : ℕ) < N := j.2
      simp only [Matrix.of_apply, Fin.val_castLE, if_true, one_mul]
      rw [hb _ hj]
      simp only [v]
      rw [dif_pos hj]
      change Q j a = ∑ i, Q i a * (EuclideanSpace.basisFun (Fin N) ℂ j) i
      simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
    · intro k hk
      have hne : (j : ℕ) ≠ (k : ℕ) := fun he => hk (Fin.ext he.symm)
      simp [hne]

theorem mean_gen {B N m δ : ℕ} (hN : 0 < N) (G : Matrix (Fin N) (Fin m) ℂ) {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.det ≠ 0) (M : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ x : Fin N → ℂ, ∑ a, ‖∑ k, M k a * ∑ j, G j k * x j‖ ^ 2 = GlobalTheory.Adelic.archSize A x ^ 2)
    {f : MvPolynomial (Fin B × Fin N) ℂ} (hf : f ≠ 0) (hm : IsMultiHomogeneous (fun _ => δ) f) :
    blockSphereMean B m (linSubst M (linSubst G f)) + (B : ℝ) * δ * (harmonic (m - 1) : ℝ) / 2 =
      blockSphereMean B N (linSubst A f) + (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2 := by
  obtain ⟨hle, U, hU, hQ⟩ := exists_unitary (A⁻¹ * (G * M)) fun z => by
    have h1 := h (Matrix.vecMul z A⁻¹)
    rw [GlobalTheory.Adelic.archSize, Real.sq_sqrt (by positivity)] at h1
    have e1 : ∀ a, ∑ k, M k a * ∑ j, G j k * Matrix.vecMul z A⁻¹ j = ∑ i, (A⁻¹ * (G * M)) i a * z i := fun a => by
      have := congrFun (Matrix.vecMul_vecMul z A⁻¹ (G * M)) a
      rw [← Matrix.vecMul_vecMul] at this
      simp only [Matrix.vecMul, dotProduct] at this ⊢
      simp only [mul_comm (M _ a), mul_comm (G _ _), mul_comm _ (z _)]
      exact this
    have e2 : ∀ i, ∑ j, A j i * Matrix.vecMul z A⁻¹ j = z i := fun i => by
      have := congrFun (Matrix.vecMul_vecMul z A⁻¹ A) i
      rw [Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.vecMul_one] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    simpa only [e1, e2] using h1
  have e : G * M = A * (Matrix.of fun (j : Fin N) (k : Fin m) => if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) * U := by
    rw [Matrix.mul_assoc, ← hQ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.one_mul]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [GlobalTheory.HeightUnique.linSubst_linSubst, e, ← GlobalTheory.HeightUnique.linSubst_linSubst,
    GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst U hU, ← GlobalTheory.HeightUnique.linSubst_linSubst,
    mean_incl B N (n + 1) δ _ hN hle (GlobalTheory.HeightUnique.linSubst_ne_zero (A.mul_nonsing_inv hA.isUnit) hf)
      (GlobalTheory.HeightUnique.linSubst_homog _ hm)]
  ring

end PositivityTheory.UnitarySelfGeneration.UnitProductCombination.XB

end

open MvPolynomial NumberField GlobalTheory.ChowHt GlobalTheory.CompHt

theorem PositivityTheory.UnitarySelfGeneration.UnitProductCombination.formHeight_gen {K : Type} [Field K] [NumberField K] {B N m δ : ℕ} (hN : 0 < N)
    (g : Matrix (Fin N) (Fin m) K) (hg : Submodule.span K (Set.range g.col) = ⊤)
    (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hA : ∀ σ, (A σ).det ≠ 0)
    (Mt : (K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ)
    (hMt : ∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt σ k a * ∑ j, σ (g j k) * x j‖ ^ 2 =
      GlobalTheory.Adelic.archSize (A σ) x ^ 2)
    {Φ : MvPolynomial (Fin B × Fin N) K} (h0 : Φ ≠ 0) (hΦ : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) Φ) :
    formHeight δ (1 : Matrix (Fin m) (Fin m) K) Mt (linSubst g Φ) = formHeight δ g A Φ := by
  unfold formHeight
  rw [GlobalTheory.HeightUnique.linSubst_one]
  congr 2
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [GlobalTheory.ImageHeightUnique.map_linSubst]
  exact PositivityTheory.UnitarySelfGeneration.UnitProductCombination.XB.mean_gen hN (g.map σ) (hA σ) (Mt σ) (hMt σ)
    (fun h => h0 (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero])))
    (ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_map_ring _ Φ hΦ σ)
