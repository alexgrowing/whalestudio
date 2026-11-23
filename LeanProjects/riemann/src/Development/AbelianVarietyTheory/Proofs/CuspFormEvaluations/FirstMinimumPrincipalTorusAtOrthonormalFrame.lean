import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupLeL2PrincipalTorus
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumEqZeroOfRankZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiablePolyDeriv
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.L2CanThEqInvSqrtTwoPowMulDetIm

open NumberField Matrix Complex
open scoped ComplexConjugate Real
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv GT lat Hf)

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem canFn_eq_canTh (a b : Fin g → ℝ) (x : Frame X.Ψ r) (z : Fin g → ℂ) :
    canFn X bas idx a b x z = CanTh.canTh (tauMat X bas idx x) a b (hMat X bas idx x *ᵥ z) := rfl

theorem differentiable_canFn (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (a b : Fin g → ℝ) : Differentiable ℂ (canFn X bas idx a b x) :=
  (CanTh.differentiable_canTh (tauMat_im_posDef idx hs hx) a b).comp
    (LinearMap.toContinuousLinearMap (hMat X bas idx x).mulVecLin).differentiable

theorem differentiable_prod_col {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}
    {f : Fin n → V → ℂ} (hf : ∀ k, Differentiable ℂ (f k)) :
    Differentiable ℂ fun z : Fin n → V => ∏ k, f k (z k) :=
  differentiableOn_univ.1 (CanTh.differentiableOn_prod_fun _ fun k _ =>
    ((hf k).comp (differentiable_apply k)).differentiableOn)

theorem canFn_rmul (a b : Fin g → ℝ) (x : Frame X.Ψ r) {u : Frame X.Ψ r} (hu : u ∈ Bor X.Ψ r)
    (z : Fin g → ℂ) :
    canFn X bas idx a b (rmul x u) ((borMat X u).submatrix idx idx *ᵥ z) =
      canFn X bas idx a b x z := by
  rw [canFn_eq_canTh, canFn_eq_canTh, mulVec_mulVec, hMat_rmul_mul bas idx x hu,
    tauMat_rmul bas idx x hu]

variable {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ} (a b : Fin n → Fin g → ℝ)
  {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ} {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}

theorem borMat_rowOf_eq_zero {u : Frame X.Ψ r} (hu : u ∈ Bor X.Ψ r)
    (i j : X.Ψ × (Fin q0 ⊕ Fin X.p0)) (hij : i ≠ j) (h : ¬ (i.1 = j.1 ∧ Harm.RowLT i.2 j.2)) :
    borMat X u (rowOf X hr i) (rowOf X hr j) = 0 := by
  obtain ⟨τ, i⟩ := i
  obtain ⟨σ, j⟩ := j
  by_cases e : σ = τ
  swap
  · exact borMat_of_ne X u e
  subst e
  rcases i with i | i <;> rcases j with j | j <;> have hi := i.isLt <;> have hj := j.isLt <;>
    simp only [Harm.RowLT, true_and, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Fin.lt_def,
      Fin.ext_iff] at h hij
  · exact borMat_eq_zero_of_le hu (by simp) (by simp only [Fin.lt_def, rowOf_apply, rowIdx_inl]; omega)
  · exact borMat_eq_zero_of_le hu (by simp)
      (by simp only [Fin.lt_def, rowOf_apply, rowIdx_inl, rowIdx_inr]; omega)
  · exact borMat_eq_zero_of_lt hu (by simp only [rowOf_apply, rowIdx_inr]; omega)
      (by simp only [Fin.lt_def, rowOf_apply, rowIdx_inl, rowIdx_inr]; omega)
  · exact borMat_eq_zero_of_lt hu (by simp only [rowOf_apply, rowIdx_inr]; omega)
      (by simp only [Fin.lt_def, rowOf_apply, rowIdx_inr]; omega)

theorem bchar_wtOf_mul {u : Frame X.Ψ r} (hu : u ∈ Bor X.Ψ r) (c : X.Ψ → Fin q0 → ℕ)
    (c' : X.Ψ → Fin X.p0 → ℕ) (n : ℕ) :
    bchar (wtOf X hr c c' n) u * ∏ j, rowFac X (fun τ a => u τ a a) (rowOf X hr j) ^
        Sum.elim (Harm.partOf (c j.1)) (Harm.partOf (c' j.1)) j.2 =
      (∏ p, (rowFac X (fun τ a => u τ a a) p)⁻¹) ^ (n / 2) := by
  rw [bchar, ← Fintype.prod_prod_type', ← (rowOf X hr).prod_comp, ← (rowOf X hr).prod_comp,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  rintro ⟨τ, i | i⟩ -
  · have h : u τ (rowIdx hr (.inl i)) (rowIdx hr (.inl i)) ≠ 0 := PerMove.bor_diag_ne hu τ _
    simp only [rowOf_apply, wtOf_inl, Sum.elim_inl]
    rw [rowFac, if_neg (by simp), zpow_add₀ h, zpow_natCast, zpow_natCast, inv_inv, inv_pow]
    field_simp
  · have h : u τ (rowIdx hr (.inr i)) (rowIdx hr (.inr i)) ≠ 0 := PerMove.bor_diag_ne hu τ _
    simp only [rowOf_apply, wtOf_inr, Sum.elim_inr]
    rw [rowFac, if_pos (by have := i.isLt; simp only [rowIdx_inr]; omega), zpow_sub₀ h,
      _root_.zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
    field_simp

theorem thFr_rmul (hs : IsSympl X bas) (hP : P ∈ Harm.rowHighest ℂ c c') {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {u : Frame X.Ψ r} (hu : u ∈ Bor X.Ψ r) :
    thFr X hr bas idx n a b P (rmul x u) =
      bchar (wtOf X hr c c' n) u * thFr X hr bas idx n a b P x := by
  let F : (Fin n → Fin g → ℂ) → ℂ := fun z => ∏ k, canFn X bas idx (a k) (b k) (rmul x u) (z k)
  have hF : Differentiable ℂ F := differentiable_prod_col fun k =>
    differentiable_canFn idx hs (PerMove.rmul_mem_GG hx hu) _ _
  let φ : (Fin n → Fin g → ℂ) →L[ℂ] (Fin n → Fin g → ℂ) := LinearMap.toContinuousLinearMap
    (LinearMap.pi fun k => ((borMat X u).submatrix idx idx).mulVecLin ∘ₗ LinearMap.proj k)
  have h1 : (fun z : Fin n → Fin g → ℂ => ∏ k, canFn X bas idx (a k) (b k) x (z k)) = F ∘ φ := by
    funext z
    exact Finset.prod_congr rfl fun k _ => (canFn_rmul idx _ _ x hu _).symm
  have h2 : φ ∘ letterDir X hr idx = fun l => ∑ i, borMat X u (rowOf X hr i)
      (rowOf X hr (l.1, l.2.1)) • letterDir X hr idx (i.1, i.2, l.2.2) := by
    funext l k j
    change ((borMat X u).submatrix idx idx *ᵥ letterDir X hr idx l k) j = _
    by_cases hk : k = l.2.2
    · simp only [letterDir, hk, Pi.single_eq_same, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        mulVec_single_one, col_apply, submatrix_apply, Equiv.apply_symm_apply, Prod.mk.eta]
      rw [Finset.sum_eq_single ((rowOf X hr).symm (idx j))]
      · simp
      · intro i _ hi
        rw [Pi.single_eq_of_ne, mul_zero]
        rintro rfl
        simp at hi
      · simp
    · simp [letterDir, hk, -rowOf_apply]
  rw [thFr, thFr, h1, Jet.polyDeriv_comp_clm P _ hF, map_zero, h2,
    polyDeriv_triangular (I2.contDiff_of_diff hF) hP (fun i j => borMat X u (rowOf X hr i) (rowOf X hr j))
      (borMat_rowOf_eq_zero hr hu), det_hMat_rmul bas idx x hu, mul_pow,
    ← bchar_wtOf_mul hr hu c c' n]
  simp only [borMat_diag hu]
  ring

theorem pnorm_thFr_rmul (hs : IsSympl X bas) (hP : P ∈ Harm.rowHighest ℂ c c') {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {u : Frame X.Ψ r} (hu : u ∈ Bor X.Ψ r) :
    X.pnorm (wtOf X hr c c' n) (thFr X hr bas idx n a b P) (rmul x u) =
      X.pnorm (wtOf X hr c c' n) (thFr X hr bas idx n a b P) x :=
  FrameDegreeData.pnorm_rmul X _ _ (fun _ hy _ hv => thFr_rmul idx hr a b hs hP hy hv) x hx u hu

section Torus

variable (X) in

def scaleUp : (Fin g → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin g) where
  toFun z := WithLp.toLp 2 fun i => (√(X.c (idx i).1) : ℂ) * z i
  invFun v := fun i => v i / (√(X.c (idx i).1) : ℂ)
  map_add' _ _ := by ext i; simp [mul_add]
  map_smul' _ _ := by ext i; simp [mul_left_comm]
  left_inv z := by
    funext i
    exact mul_div_cancel_left₀ _ (ofReal_ne_zero.2 (Real.sqrt_pos.2 (c_pos X _)).ne')
  right_inv v := by
    ext i
    exact mul_div_cancel₀ _ (ofReal_ne_zero.2 (Real.sqrt_pos.2 (c_pos X _)).ne')

theorem scaleUp_apply (z : Fin g → ℂ) (i : Fin g) :
    scaleUp X idx z i = (√(X.c (idx i).1) : ℂ) * z i := rfl

theorem Hf_scaleUp (z w : Fin g → ℂ) : Hf (scaleUp X idx z) (scaleUp X idx w) =
    hermForm (Matrix.diagonal fun i => (X.c (idx i).1 : ℂ)) z w := by
  simp only [Hf, hermForm, dotProduct, mulVec_diagonal, scaleUp_apply, map_mul, conj_ofReal,
    Pi.star_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (√(X.c (idx i).1) : ℂ) * √(X.c (idx i).1) = X.c (idx i).1 := by
    rw [← ofReal_mul, Real.mul_self_sqrt (c_pos X _).le]
  rw [← h]
  ring

variable (X bas) in

def canSec (a b : Fin g → ℝ) (x : Frame X.Ψ r) (v : EuclideanSpace ℂ (Fin g)) : ℂ :=
  canFn X bas idx a b x fun i => v i / (√(X.c (idx i).1) : ℂ)

theorem canSec_scaleUp (a b : Fin g → ℝ) (x : Frame X.Ψ r) (z : Fin g → ℂ) :
    canSec X bas idx a b x (scaleUp X idx z) = canFn X bas idx a b x z :=
  congrArg (canFn X bas idx a b x) ((scaleUp X idx).symm_apply_apply z)

theorem differentiable_canSec (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (a b : Fin g → ℝ) : Differentiable ℂ (canSec X bas idx a b x) :=
  (differentiable_canFn idx hs hx a b).comp
    (scaleUp X idx).symm.toContinuousLinearEquiv.differentiable

variable (hs : IsSympl X bas) {x : Frame X.Ψ r} (ho : X.IsOrtho x)

theorem mem_dom_of_isOrtho (ho : X.IsOrtho x) : x ∈ X.dom := PIW.FdPA.orthonormal_domain r X x ho

def normCoord : EuclideanSpace ℂ (Fin g) ≃ₗ[ℂ] (Fin g → ℂ) :=
  (scaleUp X idx).symm.trans (Matrix.toLin'OfInv (M := hMat X bas idx x)
    (M' := perMat X bas idx Sum.inl x)
    (nonsing_inv_mul _ (riemann_of_isOrtho idx hs ho).1)
    (mul_nonsing_inv _ (riemann_of_isOrtho idx hs ho).1)).symm

theorem normCoord_scaleUp (z : Fin g → ℂ) :
    normCoord idx hs ho (scaleUp X idx z) = hMat X bas idx x *ᵥ z := by
  rw [normCoord, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem Hf_eq_normCoord (v w : EuclideanSpace ℂ (Fin g)) :
    Hf v w = hermForm (CanTh.imInv (tauMat X bas idx x)) (normCoord idx hs ho v)
      (normCoord idx hs ho w) := by
  obtain ⟨v, rfl⟩ := (scaleUp X idx).surjective v
  obtain ⟨w, rfl⟩ := (scaleUp X idx).surjective w
  rw [normCoord_scaleUp, normCoord_scaleUp, Hf_scaleUp, ← Hm_of_isOrtho idx hs ho, hermForm_Hm]
  rfl

def frameTorus (a b : Fin g → ℝ) : GT (Fin g) :=
  CanTh.torus (riemann_of_isOrtho idx hs ho).2.1 (riemann_of_isOrtho idx hs ho).2.2.1
    (normCoord idx hs ho) (Hf_eq_normCoord idx hs ho) a b

variable (a b : Fin g → ℝ)

theorem mem_lat_frameTorus (y : EuclideanSpace ℂ (Fin g)) :
    y ∈ lat (frameTorus idx hs ho a b).b ↔ ∃ v ∈ X.Λ, y = scaleUp X idx (per X x v ∘ idx) := by
  have hx := mem_dom_of_isOrtho ho
  rw [frameTorus, CanTh.mem_lat_torus]
  constructor
  · rintro ⟨m, k, h⟩
    refine ⟨_, (bas (Sum.elim m k)).2, (normCoord idx hs ho).injective ?_⟩
    rw [h, normCoord_scaleUp, hMat_mulVec_per_bas idx hs hx]
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨m, hm⟩ := bas.surjective ⟨v, hv⟩
    obtain rfl : v = bas m := by rw [hm]
    exact ⟨fun i => m (.inl i), fun i => m (.inr i), by
      rw [normCoord_scaleUp, hMat_mulVec_per X bas idx (isUnit_det_perMat idx hs hx)]⟩

theorem frameTorus_ka (m k : Fin g → ℤ) :
    (frameTorus idx hs ho a b).ka (scaleUp X idx (per X x (bas (Sum.elim m k)) ∘ idx)) =
      CanTh.canMult a b m k :=
  CanTh.torus_ka _ _ _ _ a b (by
    rw [normCoord_scaleUp, hMat_mulVec_per_bas idx hs (mem_dom_of_isOrtho ho)])

theorem canSec_eq : canSec X bas idx a b x =
    fun v => CanTh.canTh (tauMat X bas idx x) a b (normCoord idx hs ho v) := by
  funext v
  obtain ⟨z, rfl⟩ := (scaleUp X idx).surjective v
  rw [normCoord_scaleUp, ← canFn_eq_canTh]
  exact canSec_scaleUp idx a b x z

theorem canSec_mem_Sec : canSec X bas idx a b x ∈ (frameTorus idx hs ho a b).Sec 1 := by
  rw [canSec_eq idx hs ho]
  exact CanTh.canTh_mem_Sec _ _ _ _ a b

theorem l2_canSec_eq_inv_sqrt_two_pow_mul_det_im : (frameTorus idx hs ho a b).l2 1 (canSec X bas idx a b x) =
    (√(2 ^ g * ((tauMat X bas idx x).map Complex.im).det))⁻¹ := by
  rw [canSec_eq idx hs ho]
  exact CanTh.l2_canTh_eq_inv_sqrt_two_pow_mul_det_im _ _ _ _ a b

theorem l2_canSec_pos : 0 < (frameTorus idx hs ho a b).l2 1 (canSec X bas idx a b x) := by
  have h := (riemann_of_isOrtho idx hs ho).2.2.1.det_pos
  rw [l2_canSec_eq_inv_sqrt_two_pow_mul_det_im]
  positivity

include ho in

theorem norm_scaleUp_per (v : Fin r → E) : ‖scaleUp X idx (per X x v ∘ idx)‖ =
    √(∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)) := by
  have h := Hf_scaleUp idx (per X x v ∘ idx) (per X x v ∘ idx)
  rw [hermForm_diagonal_c_self idx (mem_dom_of_isOrtho ho) ho, Jet.Hf_eq_inner,
    inner_self_eq_norm_sq_to_K] at h
  rw [← Real.sqrt_sq (norm_nonneg _)]
  congr 1
  exact ofReal_injective (by rw [← h, ofReal_pow]; rfl)

include hs ho in

theorem per_ne_zero {v : Fin r → E} (hv : v ∈ X.Λ) (h0 : v ≠ 0) : per X x v ∘ idx ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := bas.surjective ⟨v, hv⟩
  obtain rfl : v = bas m := by rw [hm]
  have h1 := hMat_mulVec_per X bas idx (riemann_of_isOrtho idx hs ho).1 m
  rw [h, mulVec_zero] at h1
  have h2 := CanTh.realPt_injective (riemann_of_isOrtho idx hs ho).2.1
    (riemann_of_isOrtho idx hs ho).2.2.1 (a₁ := fun j => (m j : ℝ)) (a₂ := 0)
    (by rw [map_zero, h1, CanTh.realPt_apply]; simp)
  obtain rfl : m = 0 := funext fun j => by simpa using congrFun h2 j
  simp at h0

theorem firstMinimum_principalTorusAtOrthonormalFrame : (frameTorus idx hs ho a b).la1 = X.la1 x := by
  set S := {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)} with hS
  have h1 : {t : ℝ | ∃ y ∈ lat (frameTorus idx hs ho a b).b, y ≠ 0 ∧ t = ‖y‖} = Real.sqrt '' S := by
    ext t
    simp only [mem_lat_frameTorus, hS, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, h0, rfl⟩
      refine ⟨_, ⟨v, hv, ?_, rfl⟩, (norm_scaleUp_per idx ho v).symm⟩
      rintro rfl
      exact h0 (by rw [per_zero]; exact map_zero _)
    · rintro ⟨_, ⟨v, hv, h0, rfl⟩, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, (map_ne_zero_iff _ (scaleUp X idx).injective).2
        (per_ne_zero idx hs ho hv h0), (norm_scaleUp_per idx ho v).symm⟩
  rw [GT.la1, h1, Data.la1, Data.firstMinimumSq, ← hS]
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  refine (Monotone.map_csInf_of_continuousAt Real.continuous_sqrt.continuousAt
    (fun _ _ => Real.sqrt_le_sqrt) h ⟨0, ?_⟩).symm
  rintro _ ⟨v, hv, h0, rfl⟩
  refine (Real.sqrt_pos.1 ?_).le
  rw [← norm_scaleUp_per idx ho v, norm_pos_iff]
  exact (map_ne_zero_iff _ (scaleUp X idx).injective).2 (per_ne_zero idx hs ho hv h0)

end Torus

variable (X) in

def orthoDir (l : Harm.Var X.Ψ q0 X.p0 (Fin n)) : Fin n → EuclideanSpace ℂ (Fin g) :=
  Pi.single l.2.2 (EuclideanSpace.single (idx.symm (rowOf X hr (l.1, l.2.1))) 1)

variable (X bas) in

def orthoJet (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r) : ℂ :=
  polyDeriv P (orthoDir X idx hr) (fun w => ∏ k, canSec X bas idx (a k) (b k) x (w k)) 0

theorem thFr_eq_orthoJet (hs : IsSympl X bas) (hP : P ∈ Harm.rowHighest ℂ c c') {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    thFr X hr bas idx n a b P x = (hMat X bas idx x).det ^ (n / 2) *
      (∏ τ, (√(X.c τ) : ℂ) ^ (Harm.partSize (c τ) + Harm.partSize (c' τ))) *
        orthoJet X bas idx hr a b P x := by
  let F : (Fin n → EuclideanSpace ℂ (Fin g)) → ℂ := fun w => ∏ k, canSec X bas idx (a k) (b k) x (w k)
  have hF : Differentiable ℂ F := differentiable_prod_col fun k => differentiable_canSec idx hs hx _ _
  let φ : (Fin n → Fin g → ℂ) →L[ℂ] (Fin n → EuclideanSpace ℂ (Fin g)) :=
    LinearMap.toContinuousLinearMap
      (LinearMap.pi fun k => (scaleUp X idx).toLinearMap ∘ₗ LinearMap.proj k)
  have h1 : (fun z : Fin n → Fin g → ℂ => ∏ k, canFn X bas idx (a k) (b k) x (z k)) = F ∘ φ := by
    funext z
    exact Finset.prod_congr rfl fun k _ => (canSec_scaleUp idx _ _ x _).symm
  have h2 : φ ∘ letterDir X hr idx = fun l => (√(X.c l.1) : ℂ) • orthoDir X idx hr l := by
    funext l k
    ext i
    change (√(X.c (idx i).1) : ℂ) * letterDir X hr idx l k i = √(X.c l.1) * orthoDir X idx hr l k i
    by_cases hk : k = l.2.2
    · by_cases hi : i = idx.symm (rowOf X hr (l.1, l.2.1))
      · simp [letterDir, orthoDir, hk, hi]
      · simp [letterDir, orthoDir, hk, hi, -rowOf_apply]
    · simp [letterDir, orthoDir, hk, -rowOf_apply]
  obtain ⟨-, hdx, hdy, -⟩ := Harm.mem_rowHighest_iff_support.1 hP
  rw [thFr, h1, Jet.polyDeriv_comp_clm P _ hF, map_zero, h2, mul_assoc,
    polyDeriv_smul_letter P _ _ fun m hm => ?_]
  · rfl
  · rw [Finsupp.prod_fintype _ _ (by simp)]
    simp only [Fintype.prod_prod_type, Finset.prod_pow_eq_pow_sum, Fintype.sum_prod_type,
      Fintype.sum_sum_type, hdx _ _ m hm, hdy _ _ m hm, Harm.sum_partOf]

theorem pnorm_thFr_of_isOrtho (hs : IsSympl X bas) (hn : Even n) (hP : P ∈ Harm.rowHighest ℂ c c')
    {x : Frame X.Ψ r} (ho : X.IsOrtho x) (la : Wt X.Ψ r) :
    X.pnorm la (thFr X hr bas idx n a b P) x =
      (∏ τ, (X.c τ / 2) ^ ((r * n : ℝ) / 4) *
          X.c τ ^ (((Harm.partSize (c τ) + Harm.partSize (c' τ) : ℕ) : ℝ) / 2)) *
        ‖orthoJet X bas idx hr a b P x‖ /
        ∏ k, √((frameTorus idx hs ho (a k) (b k)).l2 1 (canSec X bas idx (a k) (b k) x)) := by
  have hx := mem_dom_of_isOrtho ho
  obtain ⟨m, rfl⟩ := hn
  have hY := (tauMat_im_posDef idx hs hx).det_pos
  have hd := det_im_tauMat idx hs hx
  have hc := c_pos X
  rw [det_Hm_of_isOrtho idx hs ho, ofReal_re,
    eq_div_iff (Finset.prod_pos fun τ _ => pow_pos (hc τ) r).ne'] at hd
  have hg : (2 : ℝ) ^ g = ∏ _τ : X.Ψ, 2 ^ r := by
    rw [Finset.prod_const, ← pow_mul, mul_comm, Finset.card_univ]
    simpa using congrArg ((2 : ℝ) ^ ·) (Fintype.card_congr idx)
  have h1 : ‖(hMat X bas idx x).det‖ =
      (∏ τ, √((X.c τ / 2) ^ r)) * √(2 ^ g * ((tauMat X bas idx x).map Complex.im).det) := by
    rw [← Real.sqrt_prod _ fun τ _ => by have := hc τ; positivity, ← Real.sqrt_mul
      (Finset.prod_nonneg fun τ _ => by have := hc τ; positivity), hg, ← mul_assoc,
      ← Finset.prod_mul_distrib]
    simp only [← mul_pow, div_mul_cancel₀ _ (two_ne_zero (α := ℝ))]
    rw [mul_comm, hd, Real.sqrt_sq (norm_nonneg _)]
  have h2 (τ : X.Ψ) : (X.c τ / 2) ^ ((r * (m + m : ℕ) : ℝ) / 4) = √((X.c τ / 2) ^ r) ^ m := by
    have := hc τ
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ r, ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul_natCast (by positivity)]
    congr 1
    push_cast
    ring
  have h3 (τ : X.Ψ) (d : ℕ) : X.c τ ^ ((d : ℝ) / 2) = √(X.c τ) ^ d := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (hc τ).le]
    congr 1
    ring
  rw [AR.Up.IC.pnorm_orth X la _ ho, thFr_eq_orthoJet idx hr a b hs hP hx, norm_mul, norm_mul,
    norm_pow, norm_prod, h1, show (m + m) / 2 = m by omega]
  simp only [l2_canSec_eq_inv_sqrt_two_pow_mul_det_im, h2, h3, norm_pow, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
    Finset.prod_pow _ m]
  rw [pow_add, ← mul_pow (√_), Real.mul_self_sqrt (by positivity), inv_pow, div_inv_eq_mul, mul_pow]
  ring

theorem norm_orthoJet_le (hs : IsSympl X bas) {d : ℕ} (hP : P.IsHomogeneous d) {x : Frame X.Ψ r}
    (ho : X.IsOrtho x) :
    ‖orthoJet X bas idx hr a b P x‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * (π * Real.exp 1 * d) ^ ((d : ℝ) / 2) *
        (√2 * (1 + 4 * √(2 * g) / (√π * X.la1 x)) ^ g) ^ n *
        ∏ k, √((frameTorus idx hs ho (a k) (b k)).l2 1 (canSec X bas idx (a k) (b k) x)) := by
  classical
  have hx := mem_dom_of_isOrtho ho
  let F : (Fin n → EuclideanSpace ℂ (Fin g)) → ℂ := fun w => ∏ k, canSec X bas idx (a k) (b k) x (w k)
  have hF : Differentiable ℂ F := differentiable_prod_col fun k => differentiable_canSec idx hs hx _ _
  let e : Harm.Var X.Ψ q0 X.p0 (Fin n) ≃ Fin n × Fin g :=
    (Equiv.prodAssoc _ _ _).symm.trans ((Equiv.prodComm _ _).trans
      (Equiv.prodCongr (Equiv.refl _) ((rowOf X hr).trans idx.symm)))
  let φ : EuclideanSpace ℂ (Harm.Var X.Ψ q0 X.p0 (Fin n)) →L[ℂ] Fin n → EuclideanSpace ℂ (Fin g) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun w k => WithLp.toLp 2 fun i => w (e.symm (k, i))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have hφ (w k i) : φ w k i = w (e.symm (k, i)) := rfl
  have h2 : φ ∘ (fun l => EuclideanSpace.single l 1) = orthoDir X idx hr := by
    funext l k
    ext i
    have he : e l = (l.2.2, idx.symm (rowOf X hr (l.1, l.2.1))) := rfl
    rw [Function.comp_apply, hφ, EuclideanSpace.single_apply]
    simp only [Equiv.symm_apply_eq, he, Prod.mk.injEq]
    by_cases hk : k = l.2.2
    · simp [orthoDir, hk, -rowOf_apply]
    · simp [orthoDir, hk, -rowOf_apply]
  have hn (w) : ‖w‖ ^ 2 = ∑ k, ‖φ w k‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, hφ]
    rw [← Fintype.sum_prod_type', ← e.symm.sum_comp]
  have hla : 0 ≤ X.la1 x := Real.sqrt_nonneg _
  set K := √2 * (1 + 4 * √(2 * g) / (√π * X.la1 x)) ^ g with hK
  have hK0 : 0 ≤ K := by positivity
  have h := Jet.norm_polyDeriv_le 1 le_rfl (F ∘ φ) (hF.comp φ.differentiable)
    ((K ^ n * ∏ k, √((frameTorus idx hs ho (a k) (b k)).l2 1
      (canSec X bas idx (a k) (b k) x))) ^ 2) (fun w => ?_) P d hP
  · rw [Jet.polyDeriv_comp_clm P _ hF, map_zero, Real.sqrt_sq (by positivity), Nat.cast_one,
      one_mul] at h
    rw [orthoJet, ← h2]
    convert h using 1
    · congr!
    · ring
  · rw [hn, Finset.mul_sum, Real.exp_sum, Function.comp_apply, norm_prod, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib, ← Fin.prod_const n K, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_
    refine (sup_le_l2_principal_torus _ _ 1 le_rfl _ (canSec_mem_Sec idx hs ho (a k) (b k))
      (φ w k)).trans_eq ?_
    rw [firstMinimum_principalTorusAtOrthonormalFrame, mul_pow, Real.sq_sqrt (l2_canSec_pos idx hs ho _ _).le, hK, mul_pow,
      Real.sq_sqrt two_pos.le, ← pow_mul, mul_comm g 2]
    simp

theorem pnorm_thFr_le (hs : IsSympl X bas) (hn : Even n) (hP : P ∈ Harm.rowHighest ℂ c c')
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm (wtOf X hr c c' n) (thFr X hr bas idx n a b P) x ≤
      (∏ τ, (X.c τ / 2) ^ ((r * n : ℝ) / 4) *
          X.c τ ^ (((Harm.partSize (c τ) + Harm.partSize (c' τ) : ℕ) : ℝ) / 2)) *
        ((∑ m ∈ P.support, ‖P.coeff m‖) *
          (π * Real.exp 1 * Harm.typeDegree c c') ^ ((Harm.typeDegree c c' : ℝ) / 2) *
          (√2 * (1 + 4 * √(2 * g) / (√π * X.la1 x)) ^ g) ^ n) := by
  have hu := FrameDegreeData.bOf_mem X hx
  have ho := FrameDegreeData.ortho_bOf X hx
  have hl : X.la1 (rmul x (FrameDegreeData.bOf X x)) = X.la1 x := by
    simp only [Data.la1, Data.firstMinimumSq, MajInv.maj_rmul X hx hu]
  rw [← pnorm_thFr_rmul idx hr a b hs hP hx hu, pnorm_thFr_of_isOrtho idx hr a b hs hn hP ho,
    mul_div_assoc, ← hl]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun τ _ => by
    have := c_pos X τ; positivity)
  rw [div_le_iff₀ (Finset.prod_pos fun k _ => Real.sqrt_pos.2 (l2_canSec_pos idx hs ho _ _))]
  exact norm_orthoJet_le idx hr a b hs (Harm.isHomogeneous_of_mem_rowHighest hP) ho

theorem exists_pnorm_thFr_le (hs : IsSympl X bas) (hn : Even n) (hP : P ∈ Harm.rowHighest ℂ c c') :
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (wtOf X hr c c' n) (thFr X hr bas idx n a b P) x ≤
      C * (1 + 1 / X.la1 x) ^ (g * n) := by
  refine ⟨(∏ τ, (X.c τ / 2) ^ ((r * n : ℝ) / 4) *
      X.c τ ^ (((Harm.partSize (c τ) + Harm.partSize (c' τ) : ℕ) : ℝ) / 2)) *
    ((∑ m ∈ P.support, ‖P.coeff m‖) *
      (π * Real.exp 1 * Harm.typeDegree c c') ^ ((Harm.typeDegree c c' : ℝ) / 2) *
      (√2 * (1 + 4 * √(2 * g) / √π) ^ g) ^ n),
    fun x hx => (pnorm_thFr_le idx hr a b hs hn hP hx).trans ?_⟩
  have hla : 0 ≤ X.la1 x := Real.sqrt_nonneg _
  have h1 : 1 + 4 * √(2 * g) / (√π * X.la1 x) ≤ (1 + 4 * √(2 * g) / √π) * (1 + 1 / X.la1 x) := by
    have h2 : 0 ≤ 4 * √(2 * g) / √π := by positivity
    have h3 : 0 ≤ 1 / X.la1 x := by positivity
    rw [← div_div, div_eq_mul_one_div _ (X.la1 x)]
    nlinarith
  rw [mul_assoc _ _ (_ ^ (g * n)), mul_assoc _ (_ ^ n), pow_mul, ← mul_pow, mul_assoc √2, ← mul_pow]
  have : 0 ≤ ∏ τ, (X.c τ / 2) ^ ((r * n : ℝ) / 4) *
      X.c τ ^ (((Harm.partSize (c τ) + Harm.partSize (c' τ) : ℕ) : ℝ) / 2) :=
    Finset.prod_nonneg fun τ _ => by have := c_pos X τ; positivity
  gcongr

theorem isModerate_thFr (hs : IsSympl X bas) (hn : Even n) (hP : P ∈ Harm.rowHighest ℂ c c') :
    X.IsModerate (wtOf X hr c c' n) (thFr X hr bas idx n a b P) := by
  obtain ⟨C, hC⟩ := exists_pnorm_thFr_le idx hr a b hs hn hP
  exact FJZero.isModerate_of_le_one_add_inv X _ _ C (g * n : ℕ) fun x hx => by
    rw [Real.rpow_natCast]; exact hC x hx

theorem isModerate_sum_thFr (hs : IsSympl X bas) (hn : Even n) {J : Type*} (s : Finset J) (t : J → ℂ)
    (a b : J → Fin n → Fin g → ℝ) {P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c') :
    X.IsModerate (wtOf X hr c c' n)
      fun x => ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x := by
  choose! C hC using fun j hj => exists_pnorm_thFr_le idx hr (a j) (b j) hs hn (hP j hj)
  refine FJZero.isModerate_of_le_one_add_inv X _ _ (∑ j ∈ s, ‖t j‖ * C j) (g * n : ℕ) fun x hx => ?_
  rw [Real.rpow_natCast, Finset.sum_mul, Data.pnorm]
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [norm_mul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC j hj x hx) (norm_nonneg _)

example : HyperbolicCusp.flagData.IsModerate
    (wtOf HyperbolicCusp.flagData Gauss.hr (fun _ _ => 0) (fun _ _ => 0) 2)
    (thFr HyperbolicCusp.flagData Gauss.hr Gauss.bas Gauss.idx 2 0 0 1) ∧
    thFr HyperbolicCusp.flagData Gauss.hr Gauss.bas Gauss.idx 2 0 0 1 Gauss.one ≠ 0 :=
  ⟨isModerate_thFr _ _ _ _ Gauss.isSympl_bas even_two (by
    simpa [Harm.minorProd] using Harm.minorProd_mem_rowHighest (R := ℂ) (κ := Fin 2)
      (fun (_ : HyperbolicCusp.flagData.Ψ) (_ : Fin 1) => 0)
      (fun _ (_ : Fin HyperbolicCusp.flagData.p0) => 0) (ε := 0) (φ := 0)
      (fun _ _ _ => by simp)), Gauss.thFr_one_ne_zero 2⟩

end

end GlobalTheory.ThFr
