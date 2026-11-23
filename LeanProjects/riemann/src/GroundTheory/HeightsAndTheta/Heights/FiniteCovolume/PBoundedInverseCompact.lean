import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StBoundedInverseCompact

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace BoundedInverseCompact

section SlopeTestRemainingChoices

variable {ι : Type*} [Fintype ι]

theorem posDef_exists_lower {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → ℂ, c * ‖y‖ ^ 2 ≤ (star y ⬝ᵥ (P *ᵥ y)).re := by
  set f : (ι → ℂ) → ℝ := fun y => (star y ⬝ᵥ (P *ᵥ y)).re with hf
  have hscale : ∀ (r : ℝ) (y : ι → ℂ), f (r • y) = r ^ 2 * f y := by
    intro r y
    simp only [hf, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_dotProduct,
      Complex.smul_re]
    ring
  have hunit : ∀ y : ι → ℂ, y ≠ 0 → ‖y‖⁻¹ • y ∈ Metric.sphere (0 : ι → ℂ) 1 := by
    intro y hy
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
  have hrecover : ∀ y : ι → ℂ, y ≠ 0 → f y = ‖y‖ ^ 2 * f (‖y‖⁻¹ • y) := by
    intro y hy
    rw [hscale, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_pow,
      one_mul]
  by_cases hne : (Metric.sphere (0 : ι → ℂ) 1).Nonempty
  · have hcont : Continuous f := by simp only [hf]; fun_prop
    obtain ⟨y0, hy0, hmin⟩ :=
      (isCompact_sphere (0 : ι → ℂ) 1).exists_isMinOn hne hcont.continuousOn
    have hy0ne : y0 ≠ 0 := by
      rintro rfl
      simp at hy0
    refine ⟨f y0, by simpa [hf] using hP.re_dotProduct_pos hy0ne, fun y => ?_⟩
    by_cases hy : y = 0
    · subst hy
      simp [hf]
    · change f y0 * ‖y‖ ^ 2 ≤ f y
      rw [hrecover y hy, mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin (hunit y hy)) (sq_nonneg _)
  · refine ⟨1, one_pos, fun y => ?_⟩
    by_cases hy : y = 0
    · subst hy
      simp
    · exact absurd ⟨_, hunit y hy⟩ hne

omit [Fintype ι] in

theorem norm_mul_apply_le {m κ : Type*} [Fintype κ] (A : Matrix m κ ℂ) (B : Matrix κ ι ℂ)
    (i : m) (j : ι) : ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := by
  rw [mul_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

end SlopeTestRemainingChoices

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [IsTotallyComplex E] [Fintype ι] in

theorem exists_rightInv (v : Basis ι E W) {n : ℕ} {e : Fin n → W}
    (he : Submodule.span E (Set.range e) = ⊤) :
    ∃ c : ι → Fin n → E, ∀ w : InfinitePlace E,
      (Matrix.of fun k a => vecAt v (e a) w k) * (Matrix.of fun a i => w.embedding (c i a)) = 1 := by
  have hmem : ∀ i, ∃ c : Fin n → E, ∑ a, c a • e a = v i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun E).mp (he ▸ Submodule.mem_top)
  choose c hc using hmem
  refine ⟨c, fun w => ?_⟩
  ext k i
  have h1 : ∑ a, v.repr (e a) k * c i a = v.repr (v i) k := by
    rw [← hc i, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  simp only [mul_apply, of_apply, vecAt, ← map_mul, ← map_sum, h1, Basis.repr_self, one_apply]
  by_cases hki : k = i
  · subst hki
    simp
  · simp [hki]

end BoundedInverseCompact

open BoundedInverseCompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem BoundedInverseCompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    BoundedInverseCompact.Statement h v := by
  intro M n e he C
  obtain ⟨c, hc⟩ := exists_rightInv v he
  choose κ hκ hκle using fun w => posDef_exists_lower (M.posDef w)
  set U : InfinitePlace E → Matrix ι (Fin n) ℂ := fun w => Matrix.of fun k a => vecAt v (e a) w k
  set R : InfinitePlace E → Matrix (Fin n) ι ℂ := fun w => Matrix.of fun a i => w.embedding (c i a)
  set H := gramAt h v
  set D : InfinitePlace E → ℝ := fun w => 1 + C ^ 2 / κ w
  set r1 : InfinitePlace E → ι → ι → ℝ := fun w _ i => ∑ a, D w * ‖R w a i‖
  set r2 : InfinitePlace E → ι → ι → ℝ :=
    fun w j i => ∑ l, (∑ k, ‖(H w)⁻¹ j k‖ * r1 w l k) * ‖H w l i‖

  have hBx : ∀ r : ι → ι → ℝ, IsCompact {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r i j} := by
    intro r
    have : {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r i j} =
        Set.pi Set.univ fun i => Set.pi Set.univ fun j => Metric.closedBall (0 : ℂ) (r i j) := by
      ext A
      constructor
      · intro hA i _ j _
        simpa using hA i j
      · intro hA i j
        simpa using hA i (Set.mem_univ _) j (Set.mem_univ _)
    rw [this]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  set K : InfinitePlace E → Set (GL ι ℂ) := fun w => Units.embedProduct (Matrix ι ι ℂ) ⁻¹'
    ({A | ∀ i j, ‖A i j‖ ≤ r2 w i j} ×ˢ
      (MulOpposite.unop ⁻¹' {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r1 w i j}))
  have hK : ∀ w, IsCompact (K w) := fun w =>
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((hBx _).prod (MulOpposite.opHomeomorph.isCompact_preimage.mp (hBx _)))
  set S := {g : archUnitary h v | ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C}
  have hclosed : IsClosed S := by
    simp only [S, Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_le ?_ continuous_const
    have hw : ∀ w, Continuous fun x : archUnitary h v =>
        (((x⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) := fun w =>
      Units.continuous_val.comp ((continuous_apply w).comp (continuous_subtype_val.comp continuous_inv))
    have hm : ∀ w, Continuous fun x : archUnitary h v => invApply x (vecAt v (e a)) w := fun w =>
      (hw w).matrix_mulVec continuous_const
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
      ((continuous_star.comp (hm w)).dotProduct (continuous_const.matrix_mulVec (hm w))))
  rw [Subtype.isCompact_iff]
  refine (isCompact_univ_pi hK).of_isClosed_subset
    ((isClosed_archUnitary h v).isClosedEmbedding_subtypeVal.isClosedMap _ hclosed) ?_
  rintro _ ⟨g, hg, rfl⟩ w -
  set Gi : Matrix ι ι ℂ := (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  set G : Matrix ι ι ℂ := (((g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)

  have hy : ∀ a, ‖invApply g (vecAt v (e a)) w‖ ≤ D w := by
    intro a
    set y := invApply g (vecAt v (e a))
    have hnn : ∀ w', 0 ≤ (star (y w') ⬝ᵥ (M.P w' *ᵥ y w')).re := fun w' =>
      (Complex.nonneg_iff.mp ((M.posDef w').posSemidef.dotProduct_mulVec_nonneg (y w'))).1
    have h0 := Finset.sum_nonneg fun w' (_ : w' ∈ Finset.univ) => hnn w'
    have hsum : ∑ w', (star (y w') ⬝ᵥ (M.P w' *ᵥ y w')).re ≤ C ^ 2 := by
      rw [← Real.sq_sqrt h0]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hg a) 2
    have hterm := (Finset.single_le_sum (fun w' _ => hnn w') (Finset.mem_univ w)).trans hsum
    have hk := hκle w (y w)
    have hq : ‖y w‖ ^ 2 ≤ C ^ 2 / κ w := by
      rw [le_div_iff₀ (hκ w)]
      nlinarith
    simp only [D]
    nlinarith [norm_nonneg (y w)]

  have hGiU : ∀ j a, (Gi * U w) j a = invApply g (vecAt v (e a)) w j := by
    intro j a
    simp [Gi, U, invApply, mul_apply, mulVec, dotProduct]
  have hGi_eq : Gi = Gi * U w * R w := by
    rw [Matrix.mul_assoc, hc w, Matrix.mul_one]
  have hGi_le : ∀ j i, ‖Gi j i‖ ≤ r1 w j i := by
    intro j i
    rw [hGi_eq]
    refine (norm_mul_apply_le _ _ j i).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [hGiU]
    exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm _ j).trans (hy a)) (norm_nonneg _)

  have hHdet : IsUnit (H w).det := by
    simp only [H, gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact (isUnit_det_gram h v).map w.embedding
  have hinv : Giᴴ * H w * Gi = H w := (mem_archUnitary.mp (g⁻¹).2) w
  have hGiG : Gi * G = 1 := by
    simp only [Gi, G, Subgroup.coe_inv, Pi.inv_apply]
    exact Units.inv_mul _
  have hG_eq : G = (H w)⁻¹ * Giᴴ * H w := by
    have h1 : Giᴴ * H w = H w * G := by
      calc Giᴴ * H w = Giᴴ * H w * (Gi * G) := by rw [hGiG, Matrix.mul_one]
        _ = H w * G := by rw [← Matrix.mul_assoc, hinv]
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHdet, Matrix.one_mul]
  have hG_le : ∀ j i, ‖G j i‖ ≤ r2 w j i := by
    intro j i
    rw [hG_eq]
    refine (norm_mul_apply_le _ _ j i).trans
      (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_mul_apply_le _ _ j l).trans
      (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [conjTranspose_apply, norm_star]
    exact hGi_le l k
  exact ⟨hG_le, hGi_le⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
