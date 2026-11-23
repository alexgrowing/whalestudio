import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace LowestWeight

section Mat

variable {r : ℕ}

theorem quad_eq {p : ℕ} (e : Fin p → Fin r) (s : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin p → ℂ) :
    star v ⬝ᵥ ((Yᵀ * diagonal (fun a => (s a : ℂ)) * Y.map (starRingEnd ℂ)).submatrix e e *ᵥ v) =
      ((∑ k, s k * ‖∑ a, Y k (e a) * conj (v a)‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ a b, (Yᵀ * diagonal (fun a => (s a : ℂ)) * Y.map (starRingEnd ℂ)) a b =
      ∑ k, Y k a * s k * conj (Y k b) := by
    intro a b
    rw [Matrix.mul_apply]
    simp [Matrix.mul_diagonal]
  push_cast
  simp only [dotProduct, mulVec, submatrix_apply, h, Pi.star_apply, Complex.star_def,
    ← Complex.mul_conj', map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring

theorem signed_isHermitian (s : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ) :
    (Yᵀ * diagonal (fun a => (s a : ℂ)) * Y.map (starRingEnd ℂ)).IsHermitian := by
  have h : Yᵀ = (Y.map (starRingEnd ℂ))ᴴ := by
    ext a b; simp
  rw [h]
  refine isHermitian_conjTranspose_mul_mul _ ?_
  rw [isHermitian_diagonal_iff]
  intro i
  simp [IsSelfAdjoint]

theorem posDef_contract {p : ℕ} (e : Fin p → Fin r) (p0 : ℕ) (Y : Matrix (Fin r) (Fin r) ℂ)
    (t : Fin r → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (h1 : ∀ a : Fin r, (a : ℕ) < p0 → ρ ≤ ‖t a‖)
    (h2 : ∀ a : Fin r, p0 ≤ (a : ℕ) → ‖t a‖ ≤ ρ)
    (hY : ((Yᵀ * diagonal (fun a : Fin r => (sgn p0 a : ℂ)) *
      Y.map (starRingEnd ℂ)).submatrix e e).PosDef) :
    (((diagonal t * Y)ᵀ * diagonal (fun a : Fin r => (sgn p0 a : ℂ)) *
      (diagonal t * Y).map (starRingEnd ℂ)).submatrix e e).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ((signed_isHermitian _ _).submatrix e) fun v hv => ?_
  have h := hY.dotProduct_mulVec_pos hv
  rw [quad_eq] at h ⊢
  rw [Complex.zero_lt_real] at h ⊢
  refine (mul_pos (pow_pos hρ 2) h).trans_le ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have e1 : ∑ a, (diagonal t * Y) k (e a) * conj (v a) = t k * ∑ a, Y k (e a) * conj (v a) := by
    simp [Matrix.diagonal_mul, Finset.mul_sum, mul_assoc]
  rw [e1, norm_mul, mul_pow]
  set w := ‖∑ a, Y k (e a) * conj (v a)‖ ^ 2
  have hw : 0 ≤ w := by positivity
  unfold sgn
  split_ifs with hk
  · have : ρ ^ 2 ≤ ‖t k‖ ^ 2 := by gcongr; exact h1 k hk
    nlinarith
  · have : ‖t k‖ ^ 2 ≤ ρ ^ 2 := by gcongr; exact h2 k (not_lt.1 hk)
    nlinarith

theorem exists_lower (Y : Matrix (Fin r) (Fin r) ℂ) (hY : ∀ i, lminor Y i ≠ 0) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, (∀ a, B a a = 1) ∧ (∀ a c, c < a → B a c = 0) ∧
      ∀ a c, a < c → (Y * B) a c = 0 := by
  have key : ∀ c : Fin r, ∃ u : Fin r → ℂ, u c = 1 ∧ (∀ a, c < a → u a = 0) ∧
      ∀ a, a < c → (Y *ᵥ u) a = 0 := by
    intro c
    have hc : (c : ℕ) ≤ r := c.isLt.le
    set A := Y.submatrix (Fin.castLE hc) (Fin.castLE hc) with hA
    have hdet : IsUnit A.det := isUnit_iff_ne_zero.2 (hY c.castSucc)
    set w : Fin c → ℂ := A⁻¹ *ᵥ fun a => -Y (Fin.castLE hc a) c with hw
    have hAw : A *ᵥ w = fun a => -Y (Fin.castLE hc a) c := by
      rw [hw, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have hne : ∀ (j : Fin c) (a : Fin r), c ≤ a → a ≠ Fin.castLE hc j := by
      intro j a ha h
      have := j.isLt
      have h' : (a : ℕ) = j := by rw [h]; rfl
      have : (c : ℕ) ≤ a := ha
      omega
    refine ⟨Pi.single c 1 + ∑ j : Fin c, w j • Pi.single (Fin.castLE hc j) 1, ?_, ?_, ?_⟩
    · simp [Finset.sum_apply, Pi.single_eq_of_ne (hne _ c le_rfl)]
    · intro a ha
      simp [Finset.sum_apply, Pi.single_eq_of_ne (hne _ a ha.le), Pi.single_eq_of_ne ha.ne']
    · intro a ha
      have h := congrFun hAw ⟨a, ha⟩
      rw [mulVec_add, mulVec_sum]
      simp only [mulVec_smul, mulVec_single_one, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.col_apply]
      simp only [mulVec, dotProduct, hA, submatrix_apply] at h
      have e : Fin.castLE hc ⟨a, ha⟩ = a := rfl
      rw [e] at h
      rw [Finset.sum_congr rfl fun j _ => mul_comm (w j) _, h]
      ring
  choose u h1 h2 h3 using key
  exact ⟨Matrix.of fun a c => u c a, h1, fun a c h => h2 c a h, fun a c h => h3 c a h⟩

theorem finite_lminor (Y : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)) :
    {s : ℂ | lminor (Y + s • (1 : Matrix (Fin r) (Fin r) ℂ)) i = 0}.Finite := by
  have hi := Nat.le_of_lt_succ i.isLt
  refine (Polynomial.finite_setOf_isRoot
    (Matrix.charpoly_monic (-(Y.submatrix (Fin.castLE hi) (Fin.castLE hi)))).ne_zero).subset ?_
  intro s hs
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly] at hs ⊢
  rw [← hs, lminor]
  congr 1
  ext a b
  simp only [submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sub_apply,
    scalar_apply, Matrix.diagonal_apply, Matrix.neg_apply, sub_neg_eq_add, smul_eq_mul, mul_ite,
    mul_one, mul_zero, (Fin.castLE_injective hi).eq_iff]
  exact add_comm _ _

end Mat

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem gramPos_rmul {x₀ : Frame X.Ψ r}
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (y : Frame X.Ψ r) (τ : X.Ψ) :
    X.gramPos (rmul x₀ y) τ = ((mat y τ)ᵀ * diagonal (fun a : Fin r => (sgn X.p0 a : ℂ)) *
      (mat y τ).map (starRingEnd ℂ)).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le) := by
  rw [← hx₀ τ, ← FrameDegreeData.gram_mul]
  rfl

theorem contract_mem_dom {x₀ : Frame X.Ψ r}
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    {y : Frame X.Ψ r} (hy : rmul x₀ y ∈ X.dom) (t : Fin r → ℂ) (ht : ∀ a, t a ≠ 0) {ρ : ℝ}
    (hρ : 0 < ρ) (h1 : ∀ a : Fin r, (a : ℕ) < X.p0 → ρ ≤ ‖t a‖)
    (h2 : ∀ a : Fin r, X.p0 ≤ (a : ℕ) → ‖t a‖ ≤ ρ) :
    rmul x₀ (fun τ => (diagonal t * mat y τ : Matrix (Fin r) (Fin r) ℂ)) ∈ X.dom := by
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩
  · have h : (mat x₀ τ * mat y τ).det ≠ 0 := (hy τ).1
    change (mat x₀ τ * (diagonal t * mat y τ)).det ≠ 0
    rw [det_mul] at h
    rw [det_mul, det_mul, det_diagonal]
    exact mul_ne_zero (left_ne_zero_of_mul h)
      (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a _ => ht a) (right_ne_zero_of_mul h))
  · have h := X.gramPos_posDef hy τ
    rw [gramPos_rmul X hx₀] at h
    exact (gramPos_rmul X hx₀ _ τ).symm ▸ posDef_contract _ _ _ t hρ h1 h2 h

theorem diagonal_mem_bor (d : X.Ψ → Fin r → ℂ) (hd : ∀ τ a, d τ a ≠ 0) :
    (fun τ => (diagonal (d τ) : Matrix (Fin r) (Fin r) ℂ)) ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨?_, fun a c h => diagonal_apply_ne _ h.ne'⟩
  change (diagonal (d τ)).det ≠ 0
  rw [det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun a _ => hd τ a

theorem eq_zero_lower (la : Wt X.Ψ r) (x₀ : Frame X.Ψ r)
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (hx₀' : x₀ ∈ X.dom) (m : Frame X.Ψ r → ℂ) (hm : DifferentiableOn ℂ m X.dom)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, m (rmul x b) = bchar la b * m x)
    (hT : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      m (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) =
        (∏ τ, ∏ i, t τ i ^ la τ i) * m x)
    (h0 : m x₀ = 0) {L : Frame X.Ψ r} (hL : ∀ τ a c, a < c → L τ a c = 0)
    (hLd : rmul x₀ L ∈ X.dom) : m (rmul x₀ L) = 0 := by
  set F : ℂ → Frame X.Ψ r := fun ζ => rmul x₀ fun τ a c => ζ ^ ((a : ℕ) - c) * L τ a c with hF
  have hFd : Differentiable ℂ F := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c => ?_
    simp only [hF, rmul, mat, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hdiag : ∀ τ a, L τ a a ≠ 0 := by
    intro τ a
    have h : (mat x₀ τ * mat L τ).det ≠ 0 := (hLd τ).1
    rw [det_mul] at h
    have h' := right_ne_zero_of_mul h
    rw [det_of_lowerTriangular (mat L τ) (fun a c hac => hL τ a c (by simpa using hac))] at h'
    exact Finset.prod_ne_zero_iff.1 h' a (Finset.mem_univ _)
  have hF0 : F 0 = rmul x₀ fun τ => (diagonal fun a => L τ a a : Matrix (Fin r) (Fin r) ℂ) := by
    simp only [hF]
    congr 1
    funext τ a c
    rcases lt_trichotomy a c with h | rfl | h
    · rw [hL τ a c h, mul_zero, diagonal_apply_ne _ h.ne]
    · simp
    · rw [zero_pow (Nat.sub_ne_zero_of_lt h), zero_mul, diagonal_apply_ne _ h.ne']
  have hb0 := diagonal_mem_bor X _ hdiag
  have hFne : ∀ ζ : ℂ, ζ ≠ 0 → F ζ = rmul (rmul x₀ fun τ =>
      (diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * mat L τ : Matrix (Fin r) (Fin r) ℂ))
      (fun _ => (diagonal fun a : Fin r => (ζ ^ (a : ℕ))⁻¹ : Matrix (Fin r) (Fin r) ℂ)) := by
    intro ζ hζ
    funext τ
    change mat x₀ τ * Matrix.of (fun a c : Fin r => ζ ^ ((a : ℕ) - c) * L τ a c) =
      mat x₀ τ * (diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * mat L τ) *
        diagonal fun a : Fin r => (ζ ^ (a : ℕ))⁻¹
    rw [Matrix.mul_assoc]
    congr 1
    ext a c
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, mat, Matrix.of_apply]
    rcases lt_or_ge a c with h | h
    · simp [hL τ a c h]
    · rw [pow_sub₀ _ hζ h]
      ring
  have hbζ : ∀ ζ : ℂ, ζ ≠ 0 → (fun _ : X.Ψ =>
      (diagonal fun a : Fin r => (ζ ^ (a : ℕ))⁻¹ : Matrix (Fin r) (Fin r) ℂ)) ∈ Bor X.Ψ r :=
    fun ζ hζ => diagonal_mem_bor X (fun _ a => (ζ ^ (a : ℕ))⁻¹)
      fun _ a => inv_ne_zero (pow_ne_zero _ hζ)
  have hctr : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ ≤ 1 → (rmul x₀ fun τ =>
      (diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * mat L τ : Matrix (Fin r) (Fin r) ℂ)) ∈ X.dom := by
    intro ζ hζ hζ1
    refine contract_mem_dom X hx₀ hLd _ (fun a => pow_ne_zero _ hζ) (ρ := ‖ζ‖ ^ X.p0)
      (pow_pos (norm_pos_iff.2 hζ) _) (fun a ha => ?_) (fun a ha => ?_)
    · rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hζ1 ha.le
    · rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hζ1 ha
  have hFmem : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, F ζ ∈ X.dom := by
    intro ζ hζ
    rcases eq_or_ne ζ 0 with rfl | h
    · rw [hF0]; exact OrthogonalFrameDomain.rmul_mem_dom X hx₀' hb0
    · rw [hFne ζ h]
      exact OrthogonalFrameDomain.rmul_mem_dom X (hctr ζ h (mem_closedBall_zero_iff.1 hζ)) (hbζ ζ h)
  have hg : DiffContOnCl ℂ (m ∘ F) (Metric.ball 0 1) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ one_ne_zero]
    exact hm.comp hFd.differentiableOn hFmem
  have hsph : Set.EqOn (m ∘ F) (fun _ => m (rmul x₀ L)) (frontier (Metric.ball (0 : ℂ) 1)) := by
    intro ζ hζ
    rw [frontier_ball _ one_ne_zero, mem_sphere_zero_iff_norm] at hζ
    have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.1 (by rw [hζ]; exact one_ne_zero)
    have h1 := hT (fun _ a => ζ ^ (a : ℕ)) (fun _ a => by rw [norm_pow, hζ, one_pow]) _ hLd
    have e : X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (fun a : Fin r => ζ ^ (a : ℕ)) *
        (mat x₀ τ)⁻¹) (rmul x₀ L) = rmul x₀ fun τ =>
      (diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * mat L τ : Matrix (Fin r) (Fin r) ℂ) := by
      funext τ
      change mat x₀ τ * Matrix.diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * (mat x₀ τ)⁻¹ *
        (mat x₀ τ * mat L τ) = mat x₀ τ * (diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * mat L τ)
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _
        (isUnit_iff_ne_zero.2 (hx₀' τ).1), Matrix.mul_assoc]
    rw [e] at h1
    change m (F ζ) = m (rmul x₀ L)
    rw [hFne ζ hζ0, hB _ (hctr ζ hζ0 hζ.le) _ (hbζ ζ hζ0), h1, ← mul_assoc]
    change (∏ τ, ∏ a : Fin r, diagonal (fun a : Fin r => (ζ ^ (a : ℕ))⁻¹) a a ^ la τ a) * _ * _ = _
    rw [← Finset.prod_mul_distrib, Finset.prod_eq_one, one_mul]
    intro τ _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun a _ => ?_
    rw [diagonal_apply_eq, ← mul_zpow, inv_mul_cancel₀ (pow_ne_zero _ hζ0), _root_.one_zpow]
  have key := Complex.eqOn_of_eqOn_frontier Metric.isBounded_ball hg diffContOnCl_const hsph
    (Metric.mem_ball_self one_pos)
  change m (F 0) = m (rmul x₀ L) at key
  rw [← key, hF0, hB _ hx₀' _ hb0, h0, mul_zero]

end Frames

end LowestWeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem lowest_weight_function_unique {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (x₀ : Frame X.Ψ r)
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (hx₀' : x₀ ∈ X.dom)
    (m : Frame X.Ψ r → ℂ) (hm : DifferentiableOn ℂ m X.dom) (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, m (rmul x b) = bchar la b * m x)
    (hT : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      m (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) = (∏ τ, ∏ i, t τ i ^ la τ i) * m x)
    (h0 : m x₀ = 0) : ∀ x ∈ X.dom, m x = 0 := by

  have hcell : ∀ y : Frame X.Ψ r, rmul x₀ y ∈ X.dom → (∀ τ i, lminor (mat y τ) i ≠ 0) →
      m (rmul x₀ y) = 0 := by
    intro y hy hmin
    choose B hB1 hB2 hB3 using fun τ => LowestWeight.exists_lower (mat y τ) (hmin τ)
    have hBb : (fun τ => B τ : Frame X.Ψ r) ∈ Bor X.Ψ r := by
      intro τ
      refine ⟨?_, hB2 τ⟩
      change (B τ).det ≠ 0
      rw [Matrix.det_of_isUpperTriangular (fun a c h => hB2 τ a c h)]
      simp [hB1]
    have e : rmul (rmul x₀ y) (fun τ => B τ) =
        rmul x₀ (fun τ => (mat y τ * B τ : Matrix (Fin r) (Fin r) ℂ)) := by
      funext τ
      exact Matrix.mul_assoc (mat x₀ τ) (mat y τ) (B τ)
    have h1 := hB _ hy _ hBb
    have h2 := OrthogonalFrameDomain.rmul_mem_dom X hy hBb
    rw [e] at h1 h2
    rw [LowestWeight.eq_zero_lower X la x₀ hx₀ hx₀' m hm hB hT h0 hB3 h2] at h1
    simpa [bchar, hB1] using h1.symm

  intro x hx
  set y : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat x₀ τ)⁻¹ * mat x τ with hy
  have e : ∀ s : ℂ, x + s • x₀ =
      rmul x₀ fun τ => (y τ + s • (1 : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
    intro s
    funext τ
    change mat x τ + s • mat x₀ τ = mat x₀ τ * ((mat x₀ τ)⁻¹ * mat x τ + s • 1)
    rw [Matrix.mul_add, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hx₀' τ).1),
      Matrix.mul_smul, Matrix.mul_one]
  have hlim : Tendsto (fun s : ℂ => x + s • x₀) (𝓝[≠] 0) (𝓝 x) :=
    (Continuous.tendsto' (by fun_prop) _ _ (by simp)).mono_left nhdsWithin_le_nhds
  have hn : X.dom ∈ 𝓝 x := (FourierCoefficientDomain.isOpen_dom X).mem_nhds hx
  have hgood : ∀ᶠ s : ℂ in 𝓝[≠] 0, ∀ τ i,
      lminor (y τ + s • (1 : Matrix (Fin r) (Fin r) ℂ)) i ≠ 0 := by
    simp only [eventually_all]
    intro τ i
    exact nhdsNE_le_cofinite _ (LowestWeight.finite_lminor (y τ) i).eventually_cofinite_notMem
  have hz : ∀ᶠ s : ℂ in 𝓝[≠] 0, m (x + s • x₀) = 0 := by
    filter_upwards [hgood, hlim.eventually hn] with s hs hsd
    rw [e s] at hsd ⊢
    exact hcell _ hsd hs
  exact tendsto_nhds_unique ((hm.differentiableAt hn).continuousAt.tendsto.comp hlim)
    (tendsto_const_nhds.congr' (hz.mono fun s hs => hs.symm))

theorem lowest_weight_function_mul_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (x₀ : Frame X.Ψ r)
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (hx₀' : x₀ ∈ X.dom)
    (m m' : Frame X.Ψ r → ℂ) (hm : DifferentiableOn ℂ m X.dom) (hm' : DifferentiableOn ℂ m' X.dom)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, m (rmul x b) = bchar la b * m x)
    (hB' : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, m' (rmul x b) = bchar la b * m' x)
    (hT : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      m (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) =
        (∏ τ, ∏ i, t τ i ^ la τ i) * m x)
    (hT' : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      m' (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) =
        (∏ τ, ∏ i, t τ i ^ la τ i) * m' x) :
    ∀ x ∈ X.dom, m x * m' x₀ = m' x * m x₀ := by
  intro x hx
  refine sub_eq_zero.1 (lowest_weight_function_unique X la x₀ hx₀ hx₀'
    (fun x => m x * m' x₀ - m' x * m x₀) ((hm.mul_const _).sub (hm'.mul_const _))
    (fun x hx b hb => ?_) (fun t ht x hx => ?_) (by ring) x hx)
  · rw [hB x hx b hb, hB' x hx b hb]; ring
  · rw [hT t ht x hx, hT' t ht x hx]; ring

end GlobalTheory
