import ReciprocityTheory.ReducedBases.GsInnerBOfLt
import ReciprocityTheory.ReducedBases.LatDefs

noncomputable section

namespace ReciprocityTheory.ReducedBases.T2

open Finset InnerProductSpace Matrix

private lemma eq_sum_smul_gs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (v : Fin m → E) (a : Fin m) :
    v a = ∑ b, (if b = a then (1 : ℝ) else if b < a then ⟪gs v b, v a⟫_ℝ / ‖gs v b‖ ^ 2 else 0) •
      gs v b := by
  have hterm : ∀ b, (if b = a then (1 : ℝ) else if b < a then ⟪gs v b, v a⟫_ℝ / ‖gs v b‖ ^ 2 else 0) •
      gs v b = (if b = a then gs v b else 0) +
        (if b < a then (⟪gs v b, v a⟫_ℝ / ‖gs v b‖ ^ 2) • gs v b else 0) := by
    intro b
    by_cases h1 : b = a
    · subst h1; simp
    · by_cases h2 : b < a <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun b => b < a) = Finset.Iio a := by ext; simp
  rw [hf]
  conv_lhs => rw [gramSchmidt_def'' ℝ v a]
  simp

theorem det_gram_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (v : Fin m → E) (hv : LinearIndependent ℝ v) :
    (Matrix.gram ℝ v).det = ∏ j, ‖gs v j‖ ^ 2 := by
  set C : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun a b =>
    if b = a then (1 : ℝ) else if b < a then ⟪gs v b, v a⟫_ℝ / ‖gs v b‖ ^ 2 else 0 with hCdef
  have hexp : ∀ a, v a = ∑ b, C a b • gs v b := fun a => by
    simpa [C] using eq_sum_smul_gs v a
  have hin : ∀ a b, ⟪v a, v b⟫_ℝ = ∑ c, C a c * ‖gs v c‖ ^ 2 * C b c := by
    intro a b
    rw [hexp a, hexp b]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [real_inner_self_eq_norm_sq]; ring
    · intro d _ hdc
      rw [gramSchmidt_orthogonal ℝ v hdc]; ring
    · simp
  have hG : Matrix.gram ℝ v = C * Matrix.diagonal (fun c => ‖gs v c‖ ^ 2) * Cᵀ := by
    ext a b
    rw [Matrix.gram_apply, hin, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · simp [Matrix.diagonal_apply_eq, Matrix.transpose_apply]
    · intro d _ hdc
      simp [Matrix.diagonal_apply_ne _ hdc]
    · simp
  have hC : C.det = 1 := by
    rw [Matrix.det_of_lowerTriangular C ?_]
    · simp [C]
    · intro i j hij
      have hlt : i < j := OrderDual.toDual_lt_toDual.1 hij
      simp [C, hlt.ne', not_lt.2 hlt.le]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hC, Matrix.det_diagonal]
  simp

variable {d : ℕ}

def fB (B : Matrix (Fin d) (Fin d) ℝ) : (Fin d → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin d) where
  toFun x := WithLp.toLp 2 (B *ᵥ toReal x)
  map_add' x y := by
    have : toReal (x + y) = toReal x + toReal y := by funext i; simp [toReal]
    rw [this, mulVec_add]; rfl
  map_smul' n x := by
    have : toReal (n • x) = (n : ℝ) • toReal x := by funext i; simp [toReal]
    rw [this, mulVec_smul]
    ext i
    simp

lemma fB_apply (B : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℤ) :
    fB B x = WithLp.toLp 2 (B *ᵥ toReal x) := rfl

def TB (B : Matrix (Fin d) (Fin d) ℝ) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun v := WithLp.toLp 2 (B *ᵥ WithLp.ofLp v)
  map_add' u v := by ext i; simp [mulVec_add]
  map_smul' r v := by ext i; simp [mulVec_smul]

lemma fB_eq_TB (B : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℤ) : fB B x = TB B (fB 1 x) := by
  simp [fB_apply, TB, Matrix.one_mulVec]

lemma polar_eq (A B : Matrix (Fin d) (Fin d) ℝ) (hAB : A = Bᴴ * B) (x y : Fin d → ℤ) :
    polar A x y = ⟪fB B x, fB B y⟫_ℝ := by
  subst hAB
  rw [fB_apply, fB_apply, polar, Matrix.conjTranspose_eq_transpose_of_trivial,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma Q_eq (A B : Matrix (Fin d) (Fin d) ℝ) (hAB : A = Bᴴ * B) (x : Fin d → ℤ) :
    Q A x = ‖fB B x‖ ^ 2 / 2 := by
  rw [Q, polar_eq A B hAB, real_inner_self_eq_norm_sq]

lemma fB_expand (B : Matrix (Fin d) (Fin d) ℝ) (e : Module.Basis (Fin d) ℤ (Fin d → ℤ))
    (x : Fin d → ℤ) : fB B x = ∑ i, ((e.repr x i : ℤ) : ℝ) • fB B (e i) := by
  conv_lhs => rw [← e.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, Int.cast_smul_eq_zsmul]

lemma TB_injective (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hAB : A = Bᴴ * B) :
    Function.Injective (TB B) := by
  have hdet : IsUnit B.det := by
    have h1 := hA.det_pos
    rw [hAB, Matrix.det_mul, Matrix.det_conjTranspose] at h1
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0] at h1
    simp at h1
  have hinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det B).2 hdet)
  intro u w h
  have h' : B *ᵥ WithLp.ofLp u = B *ᵥ WithLp.ofLp w := by
    have := congrArg WithLp.ofLp h
    simpa [TB] using this
  have h'' := congrArg (WithLp.toLp 2) (hinj h')
  simpa using h''

lemma li_basis (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hAB : A = Bᴴ * B)
    (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    LinearIndependent ℝ (fun i => fB 1 (e i)) ∧ LinearIndependent ℝ (fun i => fB B (e i)) := by
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range fun i => fB 1 (e i)) := by
    rw [← (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : (EuclideanSpace.basisFun (Fin d) ℝ).toBasis j = fB 1 (Pi.single j 1) := by
      ext k
      by_cases hk : k = j
      · subst hk; simp [fB_apply, toReal]
      · simp [fB_apply, toReal, hk]
    rw [SetLike.mem_coe, hj, fB_expand 1 e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 : LinearIndependent ℝ (fun i => fB 1 (e i)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)
  refine ⟨h1, ?_⟩
  have h2 := h1.map' (TB B) (LinearMap.ker_eq_bot.2 (TB_injective A B hA hAB))
  have hfun : (fun i => fB B (e i)) = (TB B) ∘ (fun i => fB 1 (e i)) := by
    funext i
    exact fB_eq_TB B (e i)
  rw [hfun]
  exact h2

private lemma sub_gs_mem_span_Iio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Fin d → E) (j : Fin d) :
    f j - gs f j ∈ Submodule.span ℝ (f '' Set.Iio j) := by
  rw [← span_gramSchmidt_Iio ℝ f j]
  rw [sub_eq_iff_eq_add'.2 (gramSchmidt_def'' ℝ f j)]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simpa using hi, rfl⟩)

private lemma norm_gs_sq_le_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Fin d → E) (j : Fin d) (w : E) (hw : w ∈ Submodule.span ℝ (f '' Set.Iio j)) :
    ‖gs f j‖ ≤ ‖f j - w‖ := by
  have hz : f j - gs f j - w ∈ Submodule.span ℝ (f '' Set.Iio j) :=
    Submodule.sub_mem _ (sub_gs_mem_span_Iio f j) hw
  rw [← span_gramSchmidt_Iio ℝ f j] at hz
  have hle : Submodule.span ℝ (gramSchmidt ℝ f '' Set.Iio j) ≤ (ℝ ∙ gs f j)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact gramSchmidt_orthogonal ℝ f (ne_of_gt (Set.mem_Iio.1 hi))
  have horth : ⟪gs f j, f j - gs f j - w⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hz)
  have hsplit : f j - w = gs f j + (f j - gs f j - w) := by abel
  have h2 : ‖f j - w‖ ^ 2 = ‖gs f j‖ ^ 2 + ‖f j - gs f j - w‖ ^ 2 := by
    rw [hsplit, norm_add_sq_real, horth]; ring
  nlinarith [norm_nonneg (gs f j), norm_nonneg (f j - w), sq_nonneg ‖f j - gs f j - w‖]

lemma gs_TB (B : Matrix (Fin d) (Fin d) ℝ) {K : ℝ} (hK : ∀ v, ‖v‖ ≤ K * ‖TB B v‖)
    (U : Fin d → EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    ‖gs U j‖ ≤ K * ‖gs (fun i => TB B (U i)) j‖ := by
  have hp := sub_gs_mem_span_Iio (fun i => TB B (U i)) j
  have himg : (fun i => TB B (U i)) '' Set.Iio j = (TB B) '' (U '' Set.Iio j) := by
    rw [Set.image_image]
  rw [himg, Submodule.span_image] at hp
  obtain ⟨w, hw, hTw⟩ := Submodule.mem_map.1 hp
  have hgs : gs (fun i => TB B (U i)) j = TB B (U j - w) := by
    rw [map_sub, hTw]; abel
  calc ‖gs U j‖ ≤ ‖U j - w‖ := norm_gs_sq_le_norm_sq U j w hw
    _ ≤ K * ‖TB B (U j - w)‖ := hK _
    _ = K * ‖gs (fun i => TB B (U i)) j‖ := by rw [hgs]

end ReciprocityTheory.ReducedBases.T2

end
