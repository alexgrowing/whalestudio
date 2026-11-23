import Mathlib
import GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option linter.unusedSectionVars false

namespace SecondKind

namespace UnitaryRecombination

section HS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hsVec (X : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι × ι) := WithLp.toLp 2 (fun ij => X ij.1 ij.2)

def hs (X : Matrix ι ι ℂ) : ℝ := ‖hsVec X‖

theorem hsVec_add (X Y : Matrix ι ι ℂ) : hsVec (X + Y) = hsVec X + hsVec Y := rfl
theorem hsVec_sub (X Y : Matrix ι ι ℂ) : hsVec (X - Y) = hsVec X - hsVec Y := rfl
theorem hsVec_smul (c : ℝ) (X : Matrix ι ι ℂ) : hsVec (c • X) = c • hsVec X := rfl

theorem hs_nonneg (X : Matrix ι ι ℂ) : 0 ≤ hs X := norm_nonneg _

theorem hs_add_le (X Y : Matrix ι ι ℂ) : hs (X + Y) ≤ hs X + hs Y := by
  rw [hs, hsVec_add]; exact norm_add_le _ _

theorem hs_smul (c : ℝ) (X : Matrix ι ι ℂ) : hs (c • X) = |c| * hs X := by
  rw [hs, hsVec_smul, norm_smul, Real.norm_eq_abs]; rfl

theorem hs_zero : hs (0 : Matrix ι ι ℂ) = 0 := by
  simpa using hs_smul (0 : ℝ) (0 : Matrix ι ι ℂ)

theorem hs_sq (X : Matrix ι ι ℂ) : hs X ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [hs, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]; rfl

def tInner (X Y : Matrix ι ι ℂ) : ℝ := (trace (X * Yᴴ)).re

theorem tInner_self (X : Matrix ι ι ℂ) : tInner X X = hs X ^ 2 := by
  rw [hs_sq, tInner, trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag, mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem hs_conjTranspose (X : Matrix ι ι ℂ) : hs Xᴴ = hs X := by
  have h : hs Xᴴ ^ 2 = hs X ^ 2 := by
    rw [hs_sq, hs_sq, Finset.sum_comm]
    simp [conjTranspose_apply]
  exact (sq_eq_sq₀ (hs_nonneg _) (hs_nonneg _)).1 h

theorem opNorm_le_hs (X : Matrix ι ι ℂ) : ‖X‖ ≤ hs X := by
  rw [← l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (hs_nonneg _) fun v => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by have := hs_nonneg X; positivity)).1 ?_
  rw [EuclideanSpace.norm_sq_eq, mul_pow, hs_sq, EuclideanSpace.norm_sq_eq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ofLp_toEuclideanCLM, mulVec, dotProduct]
  calc ‖∑ j, X i j * (WithLp.ofLp v) j‖ ^ 2 ≤ (∑ j, ‖X i j‖ * ‖(WithLp.ofLp v) j‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ (∑ j, ‖X i j‖ ^ 2) * ∑ j, ‖(WithLp.ofLp v) j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem hs_mul_left_le (A X : Matrix ι ι ℂ) : hs (A * X) ≤ ‖A‖ * hs X := by
  refine (sq_le_sq₀ (hs_nonneg _) (by have := hs_nonneg X; positivity)).1 ?_
  rw [hs_sq, mul_pow, hs_sq, Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have key := (toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 fun i => X i j)
  rw [l2_opNorm_toEuclideanCLM] at key
  have key2 := pow_le_pow_left₀ (norm_nonneg _) key 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at key2
  convert key2 using 2
  rw [ofLp_toEuclideanCLM]
  simp [mulVec, dotProduct, mul_apply]

theorem hs_mul_right_le (X B : Matrix ι ι ℂ) : hs (X * B) ≤ hs X * ‖B‖ := by
  rw [← hs_conjTranspose, conjTranspose_mul, ← hs_conjTranspose X, ← l2_opNorm_conjTranspose B,
    mul_comm]
  exact hs_mul_left_le _ _

end HS

section Inner

variable {f : ℕ} {p q : Fin f → ℕ}

theorem tInner_comm {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ) : tInner X Y = tInner Y X := by
  have h := trace_conjTranspose (X * Yᴴ)
  rw [conjTranspose_mul, conjTranspose_conjTranspose] at h
  rw [tInner, tInner, h, Complex.star_def, Complex.conj_re]

theorem hsInner_eq (X Y : MatProd p q) : hsInner X Y = ∑ τ, tInner (X τ) (Y τ) := rfl

theorem hsInner_comm (X Y : MatProd p q) : hsInner X Y = hsInner Y X := by
  simp only [hsInner_eq, tInner_comm (X _)]

def hsInnerR (X : MatProd p q) : MatProd p q →ₗ[ℝ] ℝ where
  toFun Y := hsInner X Y
  map_add' Y Z := by
    simp only [hsInner, Pi.add_apply, conjTranspose_add, Matrix.mul_add, trace_add, Complex.add_re,
      Finset.sum_add_distrib]
  map_smul' c Y := by
    simp only [hsInner, Pi.smul_apply, conjTranspose_smul, star_trivial, Matrix.mul_smul,
      trace_smul, Complex.smul_re, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]

theorem hsInnerR_apply (X Y : MatProd p q) : hsInnerR X Y = hsInner X Y := rfl

theorem hsInner_sum_right {κ : Type*} (s : Finset κ) (X : MatProd p q) (c : κ → ℝ)
    (Y : κ → MatProd p q) : hsInner X (∑ m ∈ s, c m • Y m) = ∑ m ∈ s, c m * hsInner X (Y m) := by
  rw [← hsInnerR_apply, map_sum]
  simp [hsInnerR_apply]

theorem hsInner_sum_left {κ : Type*} (s : Finset κ) (X : MatProd p q) (c : κ → ℝ)
    (Y : κ → MatProd p q) : hsInner (∑ m ∈ s, c m • Y m) X = ∑ m ∈ s, c m * hsInner (Y m) X := by
  rw [hsInner_comm, hsInner_sum_right]
  simp [hsInner_comm X]

theorem hsInner_sub_right (X Y Z : MatProd p q) : hsInner X (Y - Z) = hsInner X Y - hsInner X Z := by
  rw [← hsInnerR_apply, map_sub]; rfl

theorem hsInner_self (X : MatProd p q) : hsInner X X = ∑ τ, hs (X τ) ^ 2 := by
  simp only [hsInner_eq, tInner_self]

end Inner

section Frame

def coords (F : OrthoFrame) (X : MatProd F.p F.q) : Fin F.dim → ℝ := fun k => hsInner (F.E k) X

theorem coords_io (F : OrthoFrame) (v : Fin F.dim → ℝ) : coords F (F.io v) = v := by
  funext k
  simp only [coords, OrthoFrame.io, hsInner_sum_right, F.orthonormal, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem coords_E (F : OrthoFrame) (l : Fin F.dim) : coords F (F.E l) = Pi.single l 1 := by
  have : F.E l = F.io (Pi.single l 1) := by
    simp [OrthoFrame.io, Pi.single_apply]
  rw [this, coords_io]

theorem E_mem (F : OrthoFrame) (l : Fin F.dim) : F.E l ∈ lieProd F.p F.q := by
  rw [← F.span]; exact Submodule.subset_span ⟨l, rfl⟩

theorem E_mem_u (F : OrthoFrame) (l : Fin F.dim) (τ : Fin F.f) :
    F.E l τ ∈ indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ) :=
  (Submodule.mem_pi.1 (E_mem F l)) τ (Set.mem_univ _)

theorem io_coords (F : OrthoFrame) {X : MatProd F.p F.q} (hX : X ∈ lieProd F.p F.q) : F.io (coords F X) = X := by
  rw [← F.span, Submodule.mem_span_range_iff_exists_fun] at hX
  obtain ⟨c, rfl⟩ := hX
  have : (∑ i, c i • F.E i) = F.io c := rfl
  rw [this, coords_io]

theorem hsInner_io_io (F : OrthoFrame) (v w : Fin F.dim → ℝ) : hsInner (F.io v) (F.io w) = ∑ l, v l * w l := by
  rw [OrthoFrame.io, hsInner_sum_left]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := congrFun (coords_io F w) l
  rw [coords] at this
  rw [this]

theorem hsInner_self_eq_sum_sq (F : OrthoFrame) {X : MatProd F.p F.q} (hX : X ∈ lieProd F.p F.q) :
    hsInner X X = ∑ k, coords F X k ^ 2 := by
  conv_lhs => rw [← io_coords F hX]
  rw [hsInner_io_io]
  simp [sq]

theorem E_apply_of_ne (F : OrthoFrame) {l : Fin F.dim} {τ : Fin F.f} (h : τ ≠ F.place l) : F.E l τ = 0 :=
  F.supp l τ h

end Frame

theorem ioIsometry : IoIsometry.Statement := fun F v w => hsInner_io_io F v w

end UnitaryRecombination

namespace UnitaryRecombination

section ExpBound

theorem norm_exp_sub_one_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (x : 𝔸) : ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have hs : Summable (fun n : ℕ => ‖((n.factorial : ℝ)⁻¹) • x ^ n‖) :=
    NormedSpace.norm_expSeries_summable' x
  have hr : Summable (fun n : ℕ => ‖x‖ ^ n / (n.factorial : ℝ)) := Real.summable_pow_div_factorial _
  have he : NormedSpace.exp x = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • x ^ n := by
    rw [NormedSpace.exp_eq_tsum ℝ]
  have hR : Real.exp ‖x‖ = ∑' n : ℕ, ‖x‖ ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hs1 : Summable (fun n : ℕ => ‖(((n + 1).factorial : ℝ)⁻¹) • x ^ (n + 1)‖) :=
    (summable_nat_add_iff 1).2 hs
  have hr1 : Summable (fun n : ℕ => ‖x‖ ^ (n + 1) / ((n + 1).factorial : ℝ)) :=
    (summable_nat_add_iff 1).2 hr
  rw [he, hR, hs.of_norm.tsum_eq_zero_add, hr.tsum_eq_zero_add]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul, div_one,
    add_sub_cancel_left]
  refine (norm_tsum_le_tsum_norm hs1).trans (hs1.tsum_le_tsum (fun n => ?_) hr1)
  rw [norm_smul, div_eq_inv_mul, Real.norm_of_nonneg (by positivity)]
  gcongr
  exact norm_pow_le' x n.succ_pos

theorem norm_exp_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have := norm_exp_sub_one_le x
  calc ‖NormedSpace.exp x‖ = ‖(NormedSpace.exp x - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖NormedSpace.exp x - 1‖ + ‖(1 : 𝔸)‖ := norm_add_le _ _
    _ ≤ Real.exp ‖x‖ := by linarith

end ExpBound

section Dim

variable (p q : ℕ)

def dag (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  indefJ p q * Xᴴ * indefJ p q

theorem J_mul_J_mul (Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    indefJ p q * (indefJ p q * Y) = Y := by
  rw [← Matrix.mul_assoc, indefJ_mul_self, Matrix.one_mul]

theorem dag_dag (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : dag p q (dag p q X) = X := by
  simp only [dag, conjTranspose_mul, conjTranspose_conjTranspose, indefJ_conjTranspose,
    Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
  rw [J_mul_J_mul]

theorem dag_add (X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    dag p q (X + Y) = dag p q X + dag p q Y := by
  simp only [dag, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem dag_sub (X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    dag p q (X - Y) = dag p q X - dag p q Y := by
  simp only [dag, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem dag_smul (c : ℂ) (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    dag p q (c • X) = (starRingEnd ℂ c) • dag p q X := by
  simp only [dag, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Complex.star_def]

theorem dag_real_smul (c : ℝ) (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    dag p q (c • X) = c • dag p q X := by
  simp only [dag, conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]

theorem mem_u_iff_dag {X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} :
    X ∈ indefiniteUnitaryLieAlgebra p q ↔ dag p q X = -X := by
  rw [mem_indefiniteUnitaryLieAlgebra_iff]
  constructor
  · intro h
    rw [dag, h]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
    rw [J_mul_J_mul]
  · intro h
    have : Xᴴ = indefJ p q * dag p q X * indefJ p q := by
      rw [dag]
      simp only [Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
      rw [J_mul_J_mul]
    rw [this, h, Matrix.mul_neg, Matrix.neg_mul]

def skewPartU : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ →ₗ[ℝ] indefiniteUnitaryLieAlgebra p q where
  toFun X := ⟨(1 / 2 : ℂ) • (X - dag p q X), by
    rw [mem_u_iff_dag, dag_smul, dag_sub, dag_dag]
    simp only [map_div₀, map_one, map_ofNat]
    rw [← smul_neg, neg_sub]⟩
  map_add' X Y := by
    ext1
    simp only [dag_add, Submodule.coe_add]
    rw [← smul_add]; congr 1; abel
  map_smul' c X := by
    ext1
    simp only [dag_real_smul, RingHom.id_apply, SetLike.val_smul]
    rw [← smul_sub, smul_comm]

def hermPartU : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ →ₗ[ℝ] indefiniteUnitaryLieAlgebra p q where
  toFun X := ⟨(Complex.I / 2 : ℂ) • (X + dag p q X), by
    rw [mem_u_iff_dag, dag_smul, dag_add, dag_dag]
    simp only [map_div₀, Complex.conj_I, map_ofNat]
    rw [add_comm, neg_div, neg_smul]⟩
  map_add' X Y := by
    ext1
    simp only [dag_add, Submodule.coe_add]
    rw [← smul_add]; congr 1; abel
  map_smul' c X := by
    ext1
    simp only [dag_real_smul, RingHom.id_apply, SetLike.val_smul]
    rw [← smul_add, smul_comm]

def recombineU : (indefiniteUnitaryLieAlgebra p q × indefiniteUnitaryLieAlgebra p q) →ₗ[ℝ]
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ where
  toFun AB := (AB.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) - Complex.I • (AB.2 : Matrix _ _ ℂ)
  map_add' AB CD := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]; abel
  map_smul' c AB := by
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, RingHom.id_apply, smul_sub]
    rw [smul_comm]

def matEquivU : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ ≃ₗ[ℝ]
    (indefiniteUnitaryLieAlgebra p q × indefiniteUnitaryLieAlgebra p q) :=
  { (skewPartU p q).prod (hermPartU p q) with
    invFun := recombineU p q
    left_inv := fun X => by
      change (1 / 2 : ℂ) • (X - dag p q X) - Complex.I • ((Complex.I / 2) • (X + dag p q X)) = X
      rw [smul_smul, show Complex.I * (Complex.I / 2) = - (1 / 2) by
          rw [mul_div_assoc', Complex.I_mul_I]; ring]
      module
    right_inv := fun AB => by
      obtain ⟨A, B⟩ := AB
      have hA := (mem_u_iff_dag p q).1 A.2
      have hB := (mem_u_iff_dag p q).1 B.2
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change (1 / 2 : ℂ) • (((A : Matrix _ _ ℂ) - Complex.I • (B : Matrix _ _ ℂ)) -
          dag p q ((A : Matrix _ _ ℂ) - Complex.I • (B : Matrix _ _ ℂ))) = (A : Matrix _ _ ℂ)
        rw [dag_sub, dag_smul, hA, hB, Complex.conj_I]
        module
      · change (Complex.I / 2) • (((A : Matrix _ _ ℂ) - Complex.I • (B : Matrix _ _ ℂ)) +
          dag p q ((A : Matrix _ _ ℂ) - Complex.I • (B : Matrix _ _ ℂ))) = (B : Matrix _ _ ℂ)
        rw [dag_sub, dag_smul, hA, hB, Complex.conj_I]
        match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring }

theorem finrank_u : Module.finrank ℝ (indefiniteUnitaryLieAlgebra p q) = (p + q) ^ 2 := by
  have h := (matEquivU p q).finrank_eq
  rw [Module.finrank_prod, Module.finrank_matrix, Complex.finrank_real_complex] at h
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  nlinarith [h]

end Dim

end UnitaryRecombination

namespace UnitaryRecombination

section Places

variable {ι : Type*} [Fintype ι]

def tInnerR (X : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℝ] ℝ where
  toFun Y := tInner X Y
  map_add' Y Z := by simp only [tInner, conjTranspose_add, Matrix.mul_add, trace_add, Complex.add_re]
  map_smul' c Y := by
    simp only [tInner, conjTranspose_smul, star_trivial, Matrix.mul_smul, trace_smul,
      Complex.smul_re, RingHom.id_apply, smul_eq_mul]

theorem tInnerR_apply (X Y : Matrix ι ι ℂ) : tInnerR X Y = tInner X Y := rfl

theorem tInner_zero_left (Y : Matrix ι ι ℂ) : tInner 0 Y = 0 := by simp [tInner]

theorem tInner_zero_right (Y : Matrix ι ι ℂ) : tInner Y 0 = 0 := by simp [tInner]

theorem tInner_sum_right {κ : Type*} (s : Finset κ) (X : Matrix ι ι ℂ) (c : κ → ℝ)
    (Y : κ → Matrix ι ι ℂ) : tInner X (∑ m ∈ s, c m • Y m) = ∑ m ∈ s, c m * tInner X (Y m) := by
  rw [← tInnerR_apply, map_sum]
  simp [tInnerR_apply]

variable (F : OrthoFrame)

theorem hsInner_eq_tInner {k : Fin F.dim} {τ : Fin F.f} (hk : F.place k = τ) (X : MatProd F.p F.q) :
    hsInner (F.E k) X = tInner (F.E k τ) (X τ) := by
  rw [hsInner_eq, Finset.sum_eq_single τ]
  · intro τ' _ h
    rw [E_apply_of_ne F (fun h' => h (h'.trans hk)), tInner_zero_left]
  · simp

theorem tInner_E_E {k : Fin F.dim} {τ : Fin F.f} (hk : F.place k = τ) (l : Fin F.dim) :
    tInner (F.E k τ) (F.E l τ) = if k = l then 1 else 0 := by
  rw [← hsInner_eq_tInner F hk, F.orthonormal]

theorem sum_place_eq {τ : Fin F.f} {X : Matrix (Fin (F.p τ) ⊕ Fin (F.q τ)) (Fin (F.p τ) ⊕ Fin (F.q τ)) ℂ}
    (hX : X ∈ indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ)) :
    ∑ l : {l // F.place l = τ}, tInner (F.E l τ) X • F.E l τ = X := by
  classical
  set Xs : MatProd F.p F.q := Pi.single τ X with hXs
  have hmem : Xs ∈ lieProd F.p F.q := by
    rw [lieProd, Submodule.mem_pi]
    intro τ' _
    by_cases h : τ' = τ
    · subst h; simpa [hXs] using hX
    · simp [hXs, h]
  have hc : ∀ l, coords F Xs l = tInner (F.E l τ) X := by
    intro l
    rw [coords, hsInner_eq, Finset.sum_eq_single τ]
    · simp [hXs]
    · intro τ' _ h; simp [hXs, h, tInner_zero_right]
    · simp
  have h := congrFun (io_coords F hmem) τ
  simp only [OrthoFrame.io, Finset.sum_apply, Pi.smul_apply, hc] at h
  rw [hXs, Pi.single_eq_same] at h
  have hz : ∑ l : {l // ¬ F.place l = τ}, tInner (F.E l τ) X • F.E (l : Fin F.dim) τ = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [E_apply_of_ne F (fun h' => l.2 h'.symm), smul_zero]
  calc ∑ l : {l // F.place l = τ}, tInner (F.E l τ) X • F.E l τ
      = ∑ l, tInner (F.E l τ) X • F.E l τ := by
        rw [← Fintype.sum_subtype_add_sum_subtype (fun l => F.place l = τ), hz, add_zero]
    _ = X := h

theorem card_place (τ : Fin F.f) : Fintype.card {l // F.place l = τ} = F.r ^ 2 := by
  classical
  let toC : indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ) →ₗ[ℝ] ({l // F.place l = τ} → ℝ) :=
    { toFun := fun X l => tInner (F.E l τ) X
      map_add' := fun X Y => by
        funext l; simp only [Submodule.coe_add, Pi.add_apply, ← tInnerR_apply, map_add]
      map_smul' := fun c X => by
        funext l
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply, ← tInnerR_apply, map_smul] }
  let e : indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ) ≃ₗ[ℝ] ({l // F.place l = τ} → ℝ) :=
    { toC with
      invFun := fun c => ⟨∑ l : {l // F.place l = τ}, c l • F.E l τ,
        Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (E_mem_u F l τ)⟩
      left_inv := fun X => Subtype.ext (sum_place_eq F X.2)
      right_inv := fun c => by
        funext k
        change tInner (F.E k τ) (∑ l : {l // F.place l = τ}, c l • F.E l τ) = c k
        rw [tInner_sum_right, Finset.sum_eq_single k]
        · rw [tInner_E_E F k.2, if_pos rfl, mul_one]
        · intro l _ hl
          rw [tInner_E_E F k.2, if_neg (fun h => hl (Subtype.ext h).symm), mul_zero]
        · simp }
  have h := e.finrank_eq
  rw [finrank_u, F.sig, Module.finrank_fintype_fun_eq_card] at h
  exact h.symm

end Places

theorem factors : Factors.Statement := by
  intro F
  refine ⟨fun k l hkl s t => ?_, fun τ => card_place F τ⟩
  have h0 : (s • F.E k) * (t • F.E l) = 0 := by
    funext τ
    by_cases hk : τ = F.place k
    · have : τ ≠ F.place l := fun h => hkl (hk.symm.trans h)
      simp [Pi.mul_apply, E_apply_of_ne F this]
    · simp [Pi.mul_apply, E_apply_of_ne F hk]
  have h1 : (t • F.E l) * (s • F.E k) = 0 := by
    funext τ
    by_cases hk : τ = F.place k
    · have : τ ≠ F.place l := fun h => hkl (hk.symm.trans h)
      simp [Pi.mul_apply, E_apply_of_ne F this]
    · simp [Pi.mul_apply, E_apply_of_ne F hk]
  have hc : Commute (s • F.E k) (t • F.E l) := h0.trans h1.symm
  exact hc.exp.eq

end UnitaryRecombination

namespace UnitaryRecombination

section Products

variable (F : OrthoFrame)

abbrev Mat (τ : Fin F.f) : Type :=
  Matrix (Fin (F.p τ) ⊕ Fin (F.q τ)) (Fin (F.p τ) ⊕ Fin (F.q τ)) ℂ

def Evec (τ : Fin F.f) (m : ℕ) : Mat F τ := if h : m < F.dim then F.E ⟨m, h⟩ τ else 0

def yy (y : Fin F.dim → ℝ) (m : ℕ) : ℝ := if h : m < F.dim then y ⟨m, h⟩ else 0

def G (y : Fin F.dim → ℝ) (τ : Fin F.f) : ℕ → Mat F τ
  | 0 => 1
  | m + 1 => NormedSpace.exp (yy F y m • Evec F τ m) * G y τ m

def Gi (y : Fin F.dim → ℝ) (τ : Fin F.f) : ℕ → Mat F τ
  | 0 => 1
  | m + 1 => Gi y τ m * NormedSpace.exp (-(yy F y m • Evec F τ m))

theorem Evec_val (τ : Fin F.f) (l : Fin F.dim) : Evec F τ l = F.E l τ := by
  simp [Evec, l.2]

theorem yy_val (y : Fin F.dim → ℝ) (l : Fin F.dim) : yy F y l = y l := by
  simp [yy, l.2]

theorem Evec_mem (τ : Fin F.f) (m : ℕ) : Evec F τ m ∈ indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ) := by
  unfold Evec; split_ifs
  · exact E_mem_u F _ τ
  · exact Submodule.zero_mem _

theorem G_mul_Gi (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) : G F y τ k * Gi F y τ k = 1 := by
  induction k with
  | zero => simp [G, Gi]
  | succ m ih =>
    simp only [G, Gi]
    rw [show NormedSpace.exp (yy F y m • Evec F τ m) * G F y τ m *
        (Gi F y τ m * NormedSpace.exp (-(yy F y m • Evec F τ m))) =
        NormedSpace.exp (yy F y m • Evec F τ m) * (G F y τ m * Gi F y τ m) *
        NormedSpace.exp (-(yy F y m • Evec F τ m)) by simp only [Matrix.mul_assoc], ih,
      Matrix.mul_one, exp_mul_exp_neg]

theorem Gi_mul_G (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) : Gi F y τ k * G F y τ k = 1 := by
  induction k with
  | zero => simp [G, Gi]
  | succ m ih =>
    simp only [G, Gi]
    rw [show Gi F y τ m * NormedSpace.exp (-(yy F y m • Evec F τ m)) *
        (NormedSpace.exp (yy F y m • Evec F τ m) * G F y τ m) =
        Gi F y τ m * (NormedSpace.exp (-(yy F y m • Evec F τ m)) *
        NormedSpace.exp (yy F y m • Evec F τ m)) * G F y τ m by simp only [Matrix.mul_assoc],
      exp_neg_mul_exp, Matrix.mul_one, ih]

theorem inv_G (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) : (G F y τ k)⁻¹ = Gi F y τ k :=
  Matrix.inv_eq_right_inv (G_mul_Gi F y τ k)

theorem reverse_ofFn_prod (y : Fin F.dim → ℝ) (τ : Fin F.f) (n : ℕ) :
    ((List.ofFn fun l : Fin n => NormedSpace.exp (yy F y l • Evec F τ l)).reverse).prod =
      G F y τ n := by
  induction n with
  | zero => simp [G]
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.prod_cons]
    simp only [Fin.val_castSucc, Fin.val_last] at ih ⊢
    rw [ih]; rfl

theorem coordMap_eq (y : Fin F.dim → ℝ) (τ : Fin F.f) : F.coordMap y τ = G F y τ F.dim := by
  rw [← reverse_ofFn_prod, OrthoFrame.coordMap]
  congr 3
  funext l
  rw [yy_val, Evec_val]

def IsU {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Prop :=
  gᴴ * indefJ p q * g = indefJ p q

theorem isU_exp {p q : ℕ} {X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hX : X ∈ indefiniteUnitaryLieAlgebra p q) : IsU (NormedSpace.exp X) := by
  have := (mem_indefiniteUnitaryGroup_iff p q).1
    ((isExpLieAlgebra_indefiniteUnitary p q).expUnit_mem X hX)
  simpa [IsU] using this

theorem isU_mul {p q : ℕ} {g h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : IsU g)
    (hh : IsU h) : IsU (g * h) := by
  unfold IsU at *
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * indefJ p q * (g * h) = hᴴ * (gᴴ * indefJ p q * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = indefJ p q := by rw [hg, hh]

theorem isU_G (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) : IsU (G F y τ k) := by
  induction k with
  | zero => simp [IsU, G]
  | succ m ih => exact isU_mul (isU_exp (Submodule.smul_mem _ _ (Evec_mem F τ m))) ih

theorem conj_mem_u {p q : ℕ} {g h X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : IsU g)
    (hgh : g * h = 1) (hX : X ∈ indefiniteUnitaryLieAlgebra p q) :
    h * X * g ∈ indefiniteUnitaryLieAlgebra p q := by
  rw [mem_indefiniteUnitaryLieAlgebra_iff] at hX ⊢
  unfold IsU at hg
  have e1 : gᴴ * indefJ p q = indefJ p q * h := by
    calc gᴴ * indefJ p q = gᴴ * indefJ p q * (g * h) := by rw [hgh, Matrix.mul_one]
      _ = (gᴴ * indefJ p q * g) * h := by simp only [Matrix.mul_assoc]
      _ = indefJ p q * h := by rw [hg]
  have e2 : hᴴ = indefJ p q * g * indefJ p q := by
    have h3 := congrArg conjTranspose e1
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      indefJ_conjTranspose] at h3
    calc hᴴ = hᴴ * indefJ p q * indefJ p q := by
          rw [Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
      _ = indefJ p q * g * indefJ p q := by rw [← h3]
  rw [conjTranspose_mul, conjTranspose_mul, hX, e2]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  rw [J_mul_J_mul, ← Matrix.mul_assoc gᴴ, e1]
  simp only [Matrix.mul_assoc]

theorem norm_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
  rw [← l2_opNorm_toEuclideanCLM, map_one]
  exact ContinuousLinearMap.norm_id_le

def cc (y : Fin F.dim → ℝ) (τ : Fin F.f) (m : ℕ) : ℝ :=
  if h : m < F.dim then (if F.place ⟨m, h⟩ = τ then |y ⟨m, h⟩| else 0) else 0

theorem cc_nonneg (y : Fin F.dim → ℝ) (τ : Fin F.f) (m : ℕ) : 0 ≤ cc F y τ m := by
  unfold cc; split_ifs <;> simp

theorem norm_Evec_le (τ : Fin F.f) (m : ℕ) : ‖Evec F τ m‖ ≤ 1 := by
  unfold Evec; split_ifs with h
  · refine (opNorm_le_hs _).trans ?_
    have h1 : hsInner (F.E ⟨m, h⟩) (F.E ⟨m, h⟩) = 1 := by simp [F.orthonormal]
    rw [hsInner_self] at h1
    have h2 : hs (F.E ⟨m, h⟩ τ) ^ 2 ≤ 1 := by
      rw [← h1]
      exact Finset.single_le_sum (f := fun τ' => hs (F.E ⟨m, h⟩ τ') ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ τ)
    nlinarith [hs_nonneg (F.E ⟨m, h⟩ τ)]
  · simp

theorem norm_factor_le (y : Fin F.dim → ℝ) (τ : Fin F.f) (m : ℕ) :
    ‖yy F y m • Evec F τ m‖ ≤ cc F y τ m := by
  rw [norm_smul]
  unfold yy cc Evec
  split_ifs with h h'
  · rw [Real.norm_eq_abs]
    have := norm_Evec_le F τ m
    rw [Evec, dif_pos h] at this
    nlinarith [abs_nonneg (y ⟨m, h⟩)]
  · rw [E_apply_of_ne F (Ne.symm h')]; simp
  · simp

theorem norm_G_sub_one_le (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) :
    ‖G F y τ k - 1‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) - 1 ∧
      ‖G F y τ k‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) := by
  induction k with
  | zero => simp [G, norm_one_le]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set A := NormedSpace.exp (yy F y m • Evec F τ m) with hA
    have hx := norm_factor_le F y τ m
    have hA1 : ‖A - 1‖ ≤ Real.exp (cc F y τ m) - 1 :=
      (norm_exp_sub_one_le _).trans (by gcongr)
    have hA2 : ‖A‖ ≤ Real.exp (cc F y τ m) :=
      (norm_exp_le norm_one_le _).trans (Real.exp_le_exp.2 hx)
    have e : G F y τ (m + 1) - 1 = A * (G F y τ m - 1) + (A - 1) := by
      simp only [G, hA, Matrix.mul_sub, Matrix.mul_one]; abel
    rw [Finset.sum_range_succ, Real.exp_add]
    set S := ∑ x ∈ Finset.range m, cc F y τ x
    have hS : 1 ≤ Real.exp S := Real.one_le_exp (Finset.sum_nonneg fun i _ => cc_nonneg F y τ i)
    have hc : 1 ≤ Real.exp (cc F y τ m) := Real.one_le_exp (cc_nonneg F y τ m)
    constructor
    · rw [e]
      calc ‖A * (G F y τ m - 1) + (A - 1)‖ ≤ ‖A‖ * ‖G F y τ m - 1‖ + ‖A - 1‖ :=
            (norm_add_le _ _).trans (add_le_add_left (norm_mul_le _ _) _)
        _ ≤ Real.exp (cc F y τ m) * (Real.exp S - 1) + (Real.exp (cc F y τ m) - 1) := by
            gcongr
        _ = Real.exp S * Real.exp (cc F y τ m) - 1 := by ring
    · calc ‖G F y τ (m + 1)‖ = ‖A * G F y τ m‖ := rfl
        _ ≤ ‖A‖ * ‖G F y τ m‖ := norm_mul_le _ _
        _ ≤ Real.exp (cc F y τ m) * Real.exp S := by gcongr
        _ = Real.exp S * Real.exp (cc F y τ m) := by ring

theorem norm_Gi_sub_one_le (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) :
    ‖Gi F y τ k - 1‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) - 1 ∧
      ‖Gi F y τ k‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) := by
  induction k with
  | zero => simp [Gi, norm_one_le]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set B := NormedSpace.exp (-(yy F y m • Evec F τ m)) with hB
    have hx : ‖-(yy F y m • Evec F τ m)‖ ≤ cc F y τ m := by
      rw [norm_neg]; exact norm_factor_le F y τ m
    have hB1 : ‖B - 1‖ ≤ Real.exp (cc F y τ m) - 1 :=
      (norm_exp_sub_one_le _).trans (by gcongr)
    have hB2 : ‖B‖ ≤ Real.exp (cc F y τ m) :=
      (norm_exp_le norm_one_le _).trans (Real.exp_le_exp.2 hx)
    have e : Gi F y τ (m + 1) - 1 = (Gi F y τ m - 1) * B + (B - 1) := by
      simp only [Gi, hB, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [Finset.sum_range_succ, Real.exp_add]
    set S := ∑ x ∈ Finset.range m, cc F y τ x
    have hS : 1 ≤ Real.exp S := Real.one_le_exp (Finset.sum_nonneg fun i _ => cc_nonneg F y τ i)
    have hc : 1 ≤ Real.exp (cc F y τ m) := Real.one_le_exp (cc_nonneg F y τ m)
    constructor
    · rw [e]
      calc ‖(Gi F y τ m - 1) * B + (B - 1)‖ ≤ ‖Gi F y τ m - 1‖ * ‖B‖ + ‖B - 1‖ :=
            (norm_add_le _ _).trans (add_le_add_left (norm_mul_le _ _) _)
        _ ≤ (Real.exp S - 1) * Real.exp (cc F y τ m) + (Real.exp (cc F y τ m) - 1) := by
            gcongr
        _ = Real.exp S * Real.exp (cc F y τ m) - 1 := by ring
    · calc ‖Gi F y τ (m + 1)‖ = ‖Gi F y τ m * B‖ := rfl
        _ ≤ ‖Gi F y τ m‖ * ‖B‖ := norm_mul_le _ _
        _ ≤ Real.exp S * Real.exp (cc F y τ m) := by gcongr

theorem sum_cc_le (y : Fin F.dim → ℝ) (τ : Fin F.f) {a : ℝ} (hy : ∀ l, |y l| ≤ a) {k : ℕ}
    (hk : k ≤ F.dim) : ∑ m ∈ Finset.range k, cc F y τ m ≤ (F.r : ℝ) ^ 2 * a := by
  classical
  calc ∑ m ∈ Finset.range k, cc F y τ m ≤ ∑ m ∈ Finset.range F.dim, cc F y τ m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk)
          (fun i _ _ => cc_nonneg F y τ i)
    _ = ∑ l : Fin F.dim, (if F.place l = τ then |y l| else 0) := by
        rw [Finset.sum_range]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp [cc, l.2]
    _ = ∑ l ∈ Finset.univ.filter (fun l => F.place l = τ), |y l| := by
        rw [Finset.sum_filter]
    _ ≤ (Finset.univ.filter (fun l => F.place l = τ)).card • a :=
        Finset.sum_le_card_nsmul _ _ _ fun l _ => hy l
    _ = (F.r : ℝ) ^ 2 * a := by
        rw [nsmul_eq_mul, ← Fintype.card_subtype, card_place]; push_cast; ring

end Products

end UnitaryRecombination

end SecondKind

end

end GroundTheory.Heights₂.Theta
