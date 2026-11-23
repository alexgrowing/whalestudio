import Development.WeilBound.ThetaLifts.LatticeBasics.OffOpenAlt

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Matrix

namespace Ht

variable {p q : Type} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

theorem htOf_le {R : Type} [CommRing R] {N₁ : Matrix p p R → ℝ≥0} {N₂ : Matrix q q R → ℝ≥0}
    {N : Matrix (p ⊕ q) (p ⊕ q) R → ℝ≥0} (hN : ∀ a b, N (fromBlocks a 0 0 b) ≤ max (N₁ a) (N₂ b))
    {X : GL (p ⊕ q) R} {x : GL p R} {y : GL q R} (h1 : X.1 = fromBlocks x.1 0 0 y.1) :
    htOf N X ≤ htOf N₁ x * htOf N₂ y := by
  have h2 : (X⁻¹).1 = fromBlocks (x⁻¹).1 0 0 (y⁻¹).1 :=
    Units.inv_eq_of_mul_eq_one_right (by rw [h1, fromBlocks_multiply]; simp)
  have hx := one_le_htOf N₁ x
  have hy := one_le_htOf N₂ y
  refine max_le (one_le_mul_of_one_le_of_one_le hx hy) (max_le ?_ ?_)
  · rw [h1]
    exact (hN _ _).trans (max_le ((le_htOf N₁ x).trans (le_mul_of_one_le_right' hy))
      ((le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)))
  · rw [h2]
    exact (hN _ _).trans (max_le ((inv_le_htOf N₁ x).trans (le_mul_of_one_le_right' hy))
      ((inv_le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)))

theorem opNorm_le (a : Matrix p p ℂ) (b : Matrix q q ℂ) : opNorm (fromBlocks a 0 0 b) ≤ max (opNorm a) (opNorm b) := by
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  obtain ⟨v, rfl⟩ : ∃ v : p ⊕ q → ℂ, x = WithLp.toLp 2 v := ⟨x.ofLp, rfl⟩
  set c : ℝ := ((max (opNorm a) (opNorm b) : ℝ≥0) : ℝ) with hc
  have h0 : 0 ≤ c := NNReal.coe_nonneg _
  have ha : ‖(WithLp.toLp 2 (a *ᵥ v ∘ .inl) : EuclideanSpace ℂ p)‖ ≤ c * ‖(WithLp.toLp 2 (v ∘ .inl) : EuclideanSpace ℂ p)‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.2 (le_max_left (opNorm a) (opNorm b))) (norm_nonneg _))
  have hb : ‖(WithLp.toLp 2 (b *ᵥ v ∘ .inr) : EuclideanSpace ℂ q)‖ ≤ c * ‖(WithLp.toLp 2 (v ∘ .inr) : EuclideanSpace ℂ q)‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.2 (le_max_right (opNorm a) (opNorm b))) (norm_nonneg _))
  have kn : ∀ w : p ⊕ q → ℂ, ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (p ⊕ q))‖ ^ 2 =
      ‖(WithLp.toLp 2 (w ∘ .inl) : EuclideanSpace ℂ p)‖ ^ 2 + ‖(WithLp.toLp 2 (w ∘ .inr) : EuclideanSpace ℂ q)‖ ^ 2 := fun w => by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]; rfl
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _)) two_ne_zero).1 ?_
  rw [Matrix.toEuclideanCLM_toLp, fromBlocks_mulVec, kn, mul_pow, kn, mul_add, ← mul_pow, ← mul_pow]
  simp only [zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl, Sum.elim_comp_inr]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) ha 2) (pow_le_pow_left₀ (norm_nonneg _) hb 2)

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

omit [DecidableEq p] [DecidableEq q] in
theorem normFin_le (v : Pl F) (a : Matrix p p (Fv F v ⊗[F] E)) (b : Matrix q q (Fv F v ⊗[F] E)) :
    normFin F v (fromBlocks a 0 0 b) ≤ max (normFin F v a) (normFin F v b) := by
  refine (normFin_le_iff F v).2 ?_
  rintro (i | i) (j | j)
  · exact (absFin_le_normFin F v a i j).trans (le_max_left _ _)
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, absFin_zero]; exact zero_le
  · exact (absFin_le_normFin F v b i j).trans (le_max_right _ _)

theorem normInf_le (w : InfinitePlace F) (a : Matrix p p (w.Completion ⊗[F] E)) (b : Matrix q q (w.Completion ⊗[F] E)) :
    normInf F w (fromBlocks a 0 0 b) ≤ max (normInf F w a) (normInf F w b) :=
  (normInf_le_iff F w).2 fun τ => by
    rw [fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    exact (opNorm_le _ _).trans (max_le_max ((normInf_le_iff F w).1 le_rfl τ) ((normInf_le_iff F w).1 le_rfl τ))

theorem heightGL_le {X : GL (p ⊕ q) (AE F E)} {x : GL p (AE F E)} {y : GL q (AE F E)} (h : X.1 = fromBlocks x.1 0 0 y.1) :
    heightGL F X ≤ heightGL F x * heightGL F y := by
  have b : ∀ {R : Type} [CommRing R] (φ : AE F E →+* R), (Formalism.UG.bc φ X).1 = fromBlocks (Formalism.UG.bc φ x).1 0 0 (Formalism.UG.bc φ y).1 := fun φ => by
    show X.1.map φ = _
    rw [h, fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]; rfl
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib (finite_mulSupport_htFin F x) (finite_mulSupport_htFin F y)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => htOf_le (normInf_le F w) (b _))
    (finprod_le_finprod' (finite_mulSupport_htFin F _) ?_ fun v => htOf_le (normFin_le F v) (b _))
  exact ((finite_mulSupport_htFin F x).union (finite_mulSupport_htFin F y)).subset (Function.mulSupport_mul _ _)

end Ht

theorem htEmb : HtEmb := fun F _ _ _ _ _ _ _ _ _ =>
  ⟨1, fun _ _ _ h => (Ht.heightGL_le F h).trans_eq (one_mul _).symm,
    fun h h' => (heightGL_mul_le F h.1 h'.1).trans_eq (one_mul _).symm, fun h => one_le_heightGL F h.1⟩

end GlobalTheory.ThK.Dbl

end
