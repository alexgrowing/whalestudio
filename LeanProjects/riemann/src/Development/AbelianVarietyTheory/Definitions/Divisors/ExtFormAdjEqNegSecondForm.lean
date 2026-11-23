import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.HermFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}

def mdel (A : E → Matrix m n ℂ) (z ξ : E) : Matrix m n ℂ :=
  of fun a b => del (fun x => A x a b) z ξ

def mdbar (A : E → Matrix m n ℂ) (z η : E) : Matrix m n ℂ :=
  of fun a b => dbar (fun x => A x a b) z η

def mddbar (A : E → Matrix m n ℂ) (z ξ η : E) : Matrix m n ℂ :=
  of fun a b => ddbar (fun x => A x a b) z ξ η

def MContDiffAt (k : WithTop ℕ∞) (A : E → Matrix m n ℂ) (z : E) : Prop :=
  ∀ a b, ContDiffAt ℝ k (fun x => A x a b) z

section Calculus

variable {A B : E → Matrix m n ℂ} {z : E} {j k : WithTop ℕ∞}

@[simp] theorem mdel_apply (A : E → Matrix m n ℂ) (z ξ : E) (a : m) (b : n) :
    mdel A z ξ a b = del (fun x => A x a b) z ξ := rfl

@[simp] theorem mdbar_apply (A : E → Matrix m n ℂ) (z η : E) (a : m) (b : n) :
    mdbar A z η a b = dbar (fun x => A x a b) z η := rfl

@[simp] theorem mddbar_apply (A : E → Matrix m n ℂ) (z ξ η : E) (a : m) (b : n) :
    mddbar A z ξ η a b = ddbar (fun x => A x a b) z ξ η := rfl

theorem mdel_add_mdbar (A : E → Matrix m n ℂ) (z ξ : E) :
    mdel A z ξ + mdbar A z ξ = of fun a b => fderiv ℝ (fun x => A x a b) z ξ := by
  ext a b; exact del_add_dbar _ _ _

theorem mdel_congr (h : A =ᶠ[𝓝 z] B) (ξ : E) : mdel A z ξ = mdel B z ξ := by
  ext a b
  rw [mdel_apply, mdel_apply, del_congr (h.mono fun x hx => congrFun (congrFun hx a) b)]

theorem mdbar_congr (h : A =ᶠ[𝓝 z] B) (ξ : E) : mdbar A z ξ = mdbar B z ξ := by
  ext a b
  rw [mdbar_apply, mdbar_apply, dbar_congr (h.mono fun x hx => congrFun (congrFun hx a) b)]

@[simp] theorem mdel_const (C : Matrix m n ℂ) (z ξ : E) : mdel (fun _ => C) z ξ = 0 := by
  ext a b; simp

@[simp] theorem mdbar_const (C : Matrix m n ℂ) (z ξ : E) : mdbar (fun _ => C) z ξ = 0 := by
  ext a b; simp

theorem mdel_add_vec (A : E → Matrix m n ℂ) (z ξ ξ' : E) :
    mdel A z (ξ + ξ') = mdel A z ξ + mdel A z ξ' := by ext a b; simp

theorem mdel_smul_vec (A : E → Matrix m n ℂ) (z : E) (c : ℂ) (ξ : E) :
    mdel A z (c • ξ) = c • mdel A z ξ := by ext a b; simp

theorem mdbar_add_vec (A : E → Matrix m n ℂ) (z η η' : E) :
    mdbar A z (η + η') = mdbar A z η + mdbar A z η' := by ext a b; simp

theorem mdbar_smul_vec (A : E → Matrix m n ℂ) (z : E) (c : ℂ) (η : E) :
    mdbar A z (c • η) = conj c • mdbar A z η := by ext a b; simp

theorem isSesq_mddbar (A : E → Matrix m n ℂ) (z : E) : IsSesq (mddbar A z) := by
  constructor <;> intros <;> ext a b <;> simp

theorem mdel_transpose (A : E → Matrix m n ℂ) (z ξ : E) :
    mdel (fun x => (A x)ᵀ) z ξ = (mdel A z ξ)ᵀ := rfl

theorem mdbar_transpose (A : E → Matrix m n ℂ) (z ξ : E) :
    mdbar (fun x => (A x)ᵀ) z ξ = (mdbar A z ξ)ᵀ := rfl

theorem mdel_conjTranspose (A : E → Matrix m n ℂ) (z ξ : E) :
    mdel (fun x => (A x)ᴴ) z ξ = (mdbar A z ξ)ᴴ := by
  ext a b; exact del_conj (fun x => A x b a) z ξ

theorem mdbar_conjTranspose (A : E → Matrix m n ℂ) (z ξ : E) :
    mdbar (fun x => (A x)ᴴ) z ξ = (mdel A z ξ)ᴴ := by
  ext a b; exact dbar_conj (fun x => A x b a) z ξ

theorem mdel_neg (A : E → Matrix m n ℂ) (z ξ : E) : mdel (fun x => -A x) z ξ = -mdel A z ξ := by
  ext a b; simp [del_neg]

theorem mdbar_neg (A : E → Matrix m n ℂ) (z ξ : E) : mdbar (fun x => -A x) z ξ = -mdbar A z ξ := by
  ext a b; simp [dbar_neg]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.of_le (h : MContDiffAt k A z) (hjk : j ≤ k) : MContDiffAt j A z :=
  fun a b => (h a b).of_le hjk

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.diff (h : MContDiffAt 1 A z) (a : m) (b : n) :
    DifferentiableAt ℝ (fun x => A x a b) z := (h a b).differentiableAt one_ne_zero

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem mContDiffAt_const (C : Matrix m n ℂ) : MContDiffAt k (fun _ : E => C) z :=
  fun _ _ => contDiffAt_const

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.add (h : MContDiffAt k A z) (h' : MContDiffAt k B z) :
    MContDiffAt k (fun x => A x + B x) z := fun a b => (h a b).add (h' a b)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.sub (h : MContDiffAt k A z) (h' : MContDiffAt k B z) :
    MContDiffAt k (fun x => A x - B x) z := fun a b => (h a b).sub (h' a b)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.neg (h : MContDiffAt k A z) : MContDiffAt k (fun x => -A x) z :=
  fun a b => (h a b).neg

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.smul {f : E → ℂ} (hf : ContDiffAt ℝ k f z) (h : MContDiffAt k A z) :
    MContDiffAt k (fun x => f x • A x) z := fun a b => hf.mul (h a b)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.transpose (h : MContDiffAt k A z) : MContDiffAt k (fun x => (A x)ᵀ) z :=
  fun a b => h b a

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.conjTranspose (h : MContDiffAt k A z) : MContDiffAt k (fun x => (A x)ᴴ) z :=
  fun a b => conjCLE.contDiff.contDiffAt.comp z (h b a)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.submatrix {m' n' : Type*} (h : MContDiffAt k A z) (f : m' → m) (g : n' → n) :
    MContDiffAt k (fun x => (A x).submatrix f g) z := fun a b => h (f a) (g b)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.mul [Fintype n] {B : E → Matrix n l ℂ} (h : MContDiffAt k A z)
    (h' : MContDiffAt k B z) : MContDiffAt k (fun x => A x * B x) z := fun a b => by
  simp only [mul_apply]
  exact ContDiffAt.sum fun c _ => (h a c).mul (h' c b)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.det [Fintype n] [DecidableEq n] {A : E → Matrix n n ℂ}
    (h : MContDiffAt k A z) : ContDiffAt ℝ k (fun x => (A x).det) z := by
  simp only [det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun c _ => h _ _)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.inv [Fintype n] [DecidableEq n] {A : E → Matrix n n ℂ}
    (h : MContDiffAt k A z) (hu : IsUnit (A z).det) : MContDiffAt k (fun x => (A x)⁻¹) z := by
  intro a b
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, adjugate_apply]
  refine (h.det.inv hu.ne_zero).mul (MContDiffAt.det (A := fun x => (A x).updateRow b (Pi.single a 1))
    fun c d => ?_)
  simp only [updateRow_apply]
  split_ifs
  exacts [contDiffAt_const, h c d]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.eventually_isUnit [Fintype n] [DecidableEq n] {A : E → Matrix n n ℂ}
    (h : MContDiffAt k A z) (hu : IsUnit (A z).det) : ∀ᶠ x in 𝓝 z, IsUnit (A x).det :=
  (h.det.continuousAt.eventually_ne hu.ne_zero).mono fun _ hx => hx.isUnit

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.eventually_two [Finite m] [Finite n] (h : MContDiffAt 2 A z) :
    ∀ᶠ x in 𝓝 z, MContDiffAt 2 A x :=
  eventually_all.2 fun a => eventually_all.2 fun b => (h a b).eventually (by simp)

theorem MContDiffAt.mdel (h : MContDiffAt k A z) (hjk : j + 1 ≤ k) (ξ : E) :
    MContDiffAt j (fun x => mdel A x ξ) z := fun a b => by
  have h1 := (h a b).fderiv_right hjk
  simp only [mdel_apply, del_apply]
  exact ((h1.clm_apply contDiffAt_const).sub
    ((h1.clm_apply contDiffAt_const).const_smul I)).const_smul (1 / 2 : ℂ)

theorem MContDiffAt.mdbar (h : MContDiffAt k A z) (hjk : j + 1 ≤ k) (η : E) :
    MContDiffAt j (fun x => mdbar A x η) z := fun a b => by
  have h1 := (h a b).fderiv_right hjk
  simp only [mdbar_apply, dbar_apply]
  exact ((h1.clm_apply contDiffAt_const).add
    ((h1.clm_apply contDiffAt_const).const_smul I)).const_smul (1 / 2 : ℂ)

theorem mdel_add (h : MContDiffAt 1 A z) (h' : MContDiffAt 1 B z) (ξ : E) :
    mdel (fun x => A x + B x) z ξ = mdel A z ξ + mdel B z ξ := by
  ext a b; simp [del_add (h.diff a b) (h'.diff a b)]

theorem mdbar_add (h : MContDiffAt 1 A z) (h' : MContDiffAt 1 B z) (ξ : E) :
    mdbar (fun x => A x + B x) z ξ = mdbar A z ξ + mdbar B z ξ := by
  ext a b; simp [dbar_add (h.diff a b) (h'.diff a b)]

theorem mdel_smul {f : E → ℂ} (hf : DifferentiableAt ℝ f z) (h : MContDiffAt 1 A z) (ξ : E) :
    mdel (fun x => f x • A x) z ξ = f z • mdel A z ξ + del f z ξ • A z := by
  ext a b; simp [del_mul hf (h.diff a b)]

theorem mdbar_smul {f : E → ℂ} (hf : DifferentiableAt ℝ f z) (h : MContDiffAt 1 A z) (ξ : E) :
    mdbar (fun x => f x • A x) z ξ = f z • mdbar A z ξ + dbar f z ξ • A z := by
  ext a b; simp [dbar_mul hf (h.diff a b)]

theorem mdel_mul [Fintype n] {B : E → Matrix n l ℂ} (h : MContDiffAt 1 A z)
    (h' : MContDiffAt 1 B z) (ξ : E) :
    mdel (fun x => A x * B x) z ξ = A z * mdel B z ξ + mdel A z ξ * B z := by
  ext a b
  simp only [mdel_apply, mul_apply, Matrix.add_apply]
  rw [del_sum fun c _ => (h.diff a c).fun_mul (h'.diff c b), ← Finset.sum_add_distrib,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun c _ => del_mul (h.diff a c) (h'.diff c b) ξ

theorem mdbar_mul [Fintype n] {B : E → Matrix n l ℂ} (h : MContDiffAt 1 A z)
    (h' : MContDiffAt 1 B z) (ξ : E) :
    mdbar (fun x => A x * B x) z ξ = A z * mdbar B z ξ + mdbar A z ξ * B z := by
  ext a b
  simp only [mdbar_apply, mul_apply, Matrix.add_apply]
  rw [dbar_sum fun c _ => (h.diff a c).fun_mul (h'.diff c b), ← Finset.sum_add_distrib,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun c _ => dbar_mul (h.diff a c) (h'.diff c b) ξ

theorem mdel_inv [Fintype n] [DecidableEq n] {A : E → Matrix n n ℂ} (h : MContDiffAt 1 A z)
    (hu : IsUnit (A z).det) (ξ : E) :
    mdel (fun x => (A x)⁻¹) z ξ = -((A z)⁻¹ * mdel A z ξ * (A z)⁻¹) := by
  have h1 := mdel_mul h (h.inv hu) ξ
  rw [mdel_congr (B := fun _ => 1) ((h.eventually_isUnit hu).mono fun x hx => mul_nonsing_inv _ hx),
    mdel_const, eq_comm, add_eq_zero_iff_eq_neg] at h1
  rw [Matrix.mul_assoc, ← Matrix.mul_neg, ← h1, nonsing_inv_mul_cancel_left _ _ hu]

theorem mdbar_inv [Fintype n] [DecidableEq n] {A : E → Matrix n n ℂ} (h : MContDiffAt 1 A z)
    (hu : IsUnit (A z).det) (ξ : E) :
    mdbar (fun x => (A x)⁻¹) z ξ = -((A z)⁻¹ * mdbar A z ξ * (A z)⁻¹) := by
  have h1 := mdbar_mul h (h.inv hu) ξ
  rw [mdbar_congr (B := fun _ => 1)
      ((h.eventually_isUnit hu).mono fun x hx => mul_nonsing_inv _ hx),
    mdbar_const, eq_comm, add_eq_zero_iff_eq_neg] at h1
  rw [Matrix.mul_assoc, ← Matrix.mul_neg, ← h1, nonsing_inv_mul_cancel_left _ _ hu]

theorem mdbar_mdel (h : MContDiffAt 2 A z) (ξ η : E) :
    mdbar (fun x => mdel A x ξ) z η = mddbar A z ξ η := by
  ext a b; exact (ddbar_eq_dbar_del (h a b) ξ η).symm

theorem mdel_mdbar (h : MContDiffAt 2 A z) (ξ η : E) :
    mdel (fun x => mdbar A x η) z ξ = mddbar A z ξ η := by
  ext a b; exact (ddbar_eq_del_dbar (h a b) ξ η).symm

theorem conjTranspose_mdel {A : E → Matrix n n ℂ} (h : ∀ᶠ x in 𝓝 z, (A x).IsHermitian) (ξ : E) :
    (mdel A z ξ)ᴴ = mdbar A z ξ := by
  rw [← mdbar_conjTranspose]; exact mdbar_congr (h.mono fun x hx => hx.eq) ξ

theorem conjTranspose_mddbar {A : E → Matrix n n ℂ} (h2 : MContDiffAt 2 A z)
    (h : ∀ᶠ x in 𝓝 z, (A x).IsHermitian) (ξ η : E) : (mddbar A z ξ η)ᴴ = mddbar A z η ξ := by
  ext a b
  rw [conjTranspose_apply, mddbar_apply, mddbar_apply, star_def, ← ddbar_conj (h2 b a),
    ddbar_congr (u := fun x => conj (A x b a)) (u' := fun x => A x a b)
      (h.mono fun x hx => hx.apply a b)]

end Calculus

section Frame

variable [Fintype n] [DecidableEq n]

structure IsHermFrame (U : Set E) (H : E → Matrix n n ℂ) : Prop where

  isOpen : IsOpen U

  smooth : ∀ a b, ContDiffOn ℝ ∞ (fun x => H x a b) U

  herm : ∀ z ∈ U, (H z).IsHermitian

  isUnit : ∀ z ∈ U, IsUnit (H z).det

structure IsPosFrame (U : Set E) (H : E → Matrix n n ℂ) : Prop where

  isOpen : IsOpen U

  smooth : ∀ a b, ContDiffOn ℝ ∞ (fun x => H x a b) U

  posDef : ∀ z ∈ U, (H z).PosDef

def conn (H : E → Matrix n n ℂ) (z ξ : E) : Matrix n n ℂ := (H z)ᵀ⁻¹ * (mdel H z ξ)ᵀ

def curv (H : E → Matrix n n ℂ) (z ξ η : E) : Matrix n n ℂ := -mdbar (fun x => conn H x ξ) z η

def covDel (H : E → Matrix n n ℂ) (s : E → n → ℂ) (z ξ : E) : n → ℂ :=
  (fun a => del (fun x => s x a) z ξ) + conn H z ξ *ᵥ s z

def dualGram (H : Matrix n n ℂ) : Matrix n n ℂ := H⁻¹ᵀ

variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsPosFrame.isHermFrame (h : IsPosFrame U H) : IsHermFrame U H :=
  ⟨h.isOpen, h.smooth, fun z hz => (h.posDef z hz).isHermitian,
    fun z hz => (isUnit_iff_isUnit_det _).1 (h.posDef z hz).isUnit⟩

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsHermFrame.mContDiffAt (h : IsHermFrame U H) (hz : z ∈ U) : MContDiffAt ∞ H z :=
  fun a b => (h.smooth a b).contDiffAt (h.isOpen.mem_nhds hz)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsHermFrame.two (h : IsHermFrame U H) (hz : z ∈ U) : MContDiffAt 2 H z :=
  (h.mContDiffAt hz).of_le (by norm_cast)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsHermFrame.one (h : IsHermFrame U H) (hz : z ∈ U) : MContDiffAt 1 H z :=
  (h.mContDiffAt hz).of_le (by norm_cast)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsHermFrame.eventually_herm (h : IsHermFrame U H) (hz : z ∈ U) :
    ∀ᶠ x in 𝓝 z, (H x).IsHermitian := mem_of_superset (h.isOpen.mem_nhds hz) h.herm

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsHermFrame.of_mContDiffAt (hU : IsOpen U) (h : ∀ z ∈ U, MContDiffAt ∞ H z)
    (h1 : ∀ z ∈ U, (H z).IsHermitian) (h2 : ∀ z ∈ U, IsUnit (H z).det) : IsHermFrame U H :=
  ⟨hU, fun a b z hz => (h z hz a b).contDiffWithinAt, h1, h2⟩

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsHermFrame.isPosFrame (h : IsHermFrame U H) (h' : ∀ z ∈ U, (H z).PosDef) :
    IsPosFrame U H := ⟨h.isOpen, h.smooth, h'⟩

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsHermFrame.dual (h : IsHermFrame U H) : IsHermFrame U fun x => dualGram (H x) :=
  .of_mContDiffAt h.isOpen (fun z hz => ((h.mContDiffAt hz).inv (h.isUnit z hz)).transpose)
    (fun z hz => (h.herm z hz).inv.transpose)
    fun z hz => by
      rw [dualGram, det_transpose]; exact isUnit_nonsing_inv_det _ (h.isUnit z hz)

theorem conn_eq_of_isSymm (h : ∀ᶠ x in 𝓝 z, (H x).IsSymm) (ξ : E) :
    conn H z ξ = (H z)⁻¹ * mdel H z ξ := by
  rw [conn, h.self_of_nhds.eq, ← mdel_transpose, mdel_congr (h.mono fun x hx => hx.eq)]

theorem conn_transpose_mul (hu : IsUnit (H z).det) (ξ : E) :
    (conn H z ξ)ᵀ * H z = mdel H z ξ := by
  rw [conn, transpose_mul, transpose_transpose, ← transpose_nonsing_inv, transpose_transpose,
    nonsing_inv_mul_cancel_right _ _ hu]

theorem transpose_mul_conn (hu : IsUnit (H z).det) (ξ : E) :
    (H z)ᵀ * conn H z ξ = (mdel H z ξ)ᵀ := by
  rw [conn, mul_nonsing_inv_cancel_left _ _ (by rwa [det_transpose])]

theorem eq_conn_of_compatible (hu : IsUnit (H z).det) {ξ : E} {T : Matrix n n ℂ}
    (h : Tᵀ * H z = mdel H z ξ) : T = conn H z ξ := by
  rw [conn, ← h, transpose_mul, transpose_transpose,
    nonsing_inv_mul_cancel_left _ _ (by rwa [det_transpose])]

theorem del_form (hH : MContDiffAt 1 H z) (hu : IsUnit (H z).det) {s t : E → n → ℂ}
    (hs : ∀ a, ContDiffAt ℝ 1 (fun x => s x a) z) (ht : ∀ a, ContDiffAt ℝ 1 (fun x => t x a) z)
    (ξ : E) : del (fun x => form (H x) (s x) (t x)) z ξ =
      form (H z) (covDel H s z ξ) (t z) + form (H z) (s z) fun a => dbar (fun x => t x a) z ξ := by
  let S : E → Matrix n Unit ℂ := fun x => replicateCol Unit (s x)
  let T : E → Matrix n Unit ℂ := fun x => replicateCol Unit (t x)
  have hS : MContDiffAt 1 S z := fun a _ => hs a
  have hT : MContDiffAt 1 T z := fun a _ => ht a
  have e : ∀ (K : Matrix n n ℂ) (P Q : Matrix n Unit ℂ),
      (Pᵀ * K * Qᴴᵀ) () () = form K (fun a => P a ()) fun a => Q a () := fun K P Q => by
    rw [form_eq_sum, Finset.sum_comm]
    simp [mul_apply, Finset.sum_mul]
  have h := congrFun (congrFun (mdel_mul (hS.transpose.mul hH) hT.conjTranspose.transpose ξ) ()) ()
  rw [mdel_mul hS.transpose hH, mdel_transpose (fun x => (T x)ᴴ), mdel_conjTranspose,
    mdel_transpose, Matrix.add_mul, ← conn_transpose_mul hu, ← Matrix.mul_assoc, ← transpose_mul,
    mdel_apply] at h
  simp only [Matrix.add_apply, e] at h
  refine h.trans ?_
  rw [covDel, form_add_left]
  have : (fun a => (conn H z ξ * S z) a ()) = conn H z ξ *ᵥ s z := rfl
  rw [this]
  change _ + (_ + form (H z) (fun a => del (fun x => s x a) z ξ) (t z)) = _
  change form (H z) (s z) (fun a => dbar (fun x => t x a) z ξ) +
    (form (H z) (conn H z ξ *ᵥ s z) (t z) + _) = _
  ring

theorem conn_add_vec (H : E → Matrix n n ℂ) (z ξ ξ' : E) :
    conn H z (ξ + ξ') = conn H z ξ + conn H z ξ' := by
  rw [conn, mdel_add_vec, transpose_add, Matrix.mul_add]; rfl

theorem conn_smul_vec (H : E → Matrix n n ℂ) (z : E) (c : ℂ) (ξ : E) :
    conn H z (c • ξ) = c • conn H z ξ := by
  rw [conn, mdel_smul_vec, transpose_smul, Matrix.mul_smul]; rfl

theorem conn_congr (h : H =ᶠ[𝓝 z] H') (ξ : E) : conn H z ξ = conn H' z ξ := by
  rw [conn, conn, mdel_congr h, h.self_of_nhds]

theorem curv_congr (h : H =ᶠ[𝓝 z] H') (ξ η : E) : curv H z ξ η = curv H' z ξ η := by
  rw [curv, curv, mdbar_congr (h.eventuallyEq_nhds.mono fun x hx => conn_congr hx ξ)]

theorem MContDiffAt.conn (h : MContDiffAt k H z) (hu : IsUnit (H z).det) (hjk : j + 1 ≤ k)
    (ξ : E) : MContDiffAt j (fun x => conn H x ξ) z :=
  ((h.of_le (le_self_add.trans hjk)).transpose.inv (by rwa [det_transpose])).mul
    (h.mdel hjk ξ).transpose

theorem MContDiffAt.curv (h : MContDiffAt k H z) (hu : IsUnit (H z).det) (hjk : j + 2 ≤ k)
    (ξ η : E) : MContDiffAt j (fun x => curv H x ξ η) z :=
  ((h.conn hu (j := j + 1) (by rwa [add_assoc, one_add_one_eq_two]) ξ).mdbar le_rfl η).neg

@[simp] theorem conn_const (C : Matrix n n ℂ) (z ξ : E) : conn (fun _ => C) z ξ = 0 := by
  simp [conn]

@[simp] theorem curv_const (C : Matrix n n ℂ) (z ξ η : E) : curv (fun _ => C) z ξ η = 0 := by
  simp [curv]

theorem curv_eq (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    curv H z ξ η = (H z)ᵀ⁻¹ * (mdbar H z η)ᵀ * (H z)ᵀ⁻¹ * (mdel H z ξ)ᵀ
      - (H z)ᵀ⁻¹ * (mddbar H z ξ η)ᵀ := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hu' : IsUnit (H z)ᵀ.det := by rwa [det_transpose]
  simp only [curv, conn]
  rw [mdbar_mul (h1.transpose.inv hu') (h.mdel (by norm_num) ξ).transpose,
    mdbar_inv h1.transpose hu', mdbar_transpose (fun x => mdel H x ξ), mdbar_mdel h,
    mdbar_transpose, Matrix.neg_mul]
  abel

theorem isSesq_curv (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) : IsSesq (curv H z) := by
  have hs := isSesq_mddbar H z
  constructor <;> intros <;>
    simp only [curv_eq h hu, mdel_add_vec, mdbar_add_vec, mdel_smul_vec, mdbar_smul_vec,
      hs.add_left, hs.add_right, hs.smul_left, hs.smul_right, transpose_add, transpose_smul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub] <;> abel

theorem adj_curv (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (ξ η : E) : adj (H z) (H z) (curv H z ξ η) = curv H z η ξ := by
  have hu' : IsUnit (H z)ᵀ.det := by rwa [det_transpose]
  have e : ∀ M : Matrix n n ℂ, Mᵀᴴ = Mᴴᵀ := fun _ => rfl
  have e1 : (mdbar H z η)ᴴ = mdel H z η := by
    rw [← conjTranspose_mdel hh, conjTranspose_conjTranspose]
  rw [adj, curv_eq h hu, curv_eq h hu]
  simp only [conjTranspose_sub, conjTranspose_mul, hh.self_of_nhds.transpose.inv.eq, e, e1,
    conjTranspose_mdel hh, conjTranspose_mddbar h hh, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, nonsing_inv_mul _ hu', Matrix.mul_one]

theorem form_curv (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (ξ η : E) (v w : n → ℂ) :
    form (H z) (curv H z ξ η *ᵥ v) w = form (H z) v (curv H z η ξ *ᵥ w) := by
  rw [form_adj hh.self_of_nhds hu hh.self_of_nhds, adj_curv h hh hu]

theorem conn_smul {f : E → ℝ} (hf : DifferentiableAt ℝ f z) (hf0 : f z ≠ 0)
    (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det) (ξ : E) :
    conn (fun x => (f x : ℂ) • H x) z ξ =
      conn H z ξ + del (fun x => (Real.log (f x) : ℂ)) z ξ • (1 : Matrix n n ℂ) := by
  have hf0' : (f z : ℂ) ≠ 0 := by exact_mod_cast hf0
  refine (eq_conn_of_compatible ?_ ?_).symm
  · rw [det_smul]; exact (pow_ne_zero _ hf0').isUnit.mul hu
  · rw [mdel_smul (f := fun x => (f x : ℂ)) (ofRealCLM.differentiableAt.comp z hf) h,
      del_ofReal_comp (Real.hasDerivAt_log hf0) hf, ← conn_transpose_mul hu]
    simp only [transpose_add, transpose_smul, transpose_one, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul]
    congr 2
    push_cast; field_simp

theorem curv_smul {f : E → ℝ} (hf : ContDiffAt ℝ 2 f z) (hf0 : f z ≠ 0)
    (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    curv (fun x => (f x : ℂ) • H x) z ξ η =
      curv H z ξ η - leviForm (fun x => Real.log (f x)) z ξ η • (1 : Matrix n n ℂ) := by
  have hl : ContDiffAt ℝ 2 (fun x => (Real.log (f x) : ℂ)) z := contDiffAt_ofReal_comp (hf.log hf0)
  have hl' : MContDiffAt 2 (fun x => (of fun _ _ => (Real.log (f x) : ℂ) : Matrix Unit Unit ℂ)) z :=
    fun _ _ => hl
  have hd : ContDiffAt ℝ 1 (fun x => del (fun x => (Real.log (f x) : ℂ)) x ξ) z :=
    hl'.mdel (by norm_num) ξ () ()
  have he : (fun x => conn (fun x => (f x : ℂ) • H x) x ξ) =ᶠ[𝓝 z] fun x =>
      conn H x ξ + del (fun x => (Real.log (f x) : ℂ)) x ξ • (1 : Matrix n n ℂ) := by
    filter_upwards [hf.eventually (by simp), hf.continuousAt.eventually_ne hf0, h.eventually_two,
      h.eventually_isUnit hu] with x h1 h2 h3 h4
    exact conn_smul (h1.differentiableAt two_ne_zero) h2 (h3.of_le one_le_two) h4 ξ
  rw [curv, mdbar_congr he, mdbar_add (h.conn hu (by norm_num) ξ)
    (MContDiffAt.smul hd (mContDiffAt_const _)),
    mdbar_smul (hd.differentiableAt one_ne_zero) (mContDiffAt_const _), mdbar_const, leviForm,
    ddbar_eq_dbar_del hl, curv]
  simp only [smul_zero, zero_add, neg_add, sub_eq_add_neg]

theorem curv_line [Unique n] {f : E → ℝ} (hf : ContDiffAt ℝ 2 f z) (hf0 : f z ≠ 0)
    (hH : ∀ᶠ x in 𝓝 z, H x default default = f x) (ξ η : E) (a b : n) :
    curv H z ξ η a b = -leviForm (fun x => Real.log (f x)) z ξ η := by
  have he : H =ᶠ[𝓝 z] fun x => (f x : ℂ) • (1 : Matrix n n ℂ) := hH.mono fun x hx => by
    ext a b; rw [Subsingleton.elim a default, Subsingleton.elim b default, hx]; simp
  rw [curv_congr he, curv_smul hf hf0 (mContDiffAt_const _) (by simp), Subsingleton.elim a b]
  simp

theorem conn_dual (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det) (ξ : E) :
    conn (fun x => dualGram (H x)) z ξ = -(conn H z ξ)ᵀ := by
  simp only [dualGram]
  rw [conn, mdel_transpose (fun x => (H x)⁻¹), transpose_transpose, transpose_transpose,
    mdel_inv h hu, nonsing_inv_nonsing_inv _ hu, ← conn_transpose_mul hu, Matrix.mul_neg,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu, mul_nonsing_inv_cancel_right _ _ hu]

theorem curv_dual (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    curv (fun x => dualGram (H x)) z ξ η = -(curv H z ξ η)ᵀ := by
  have he : (fun x => conn (fun x => dualGram (H x)) x ξ) =ᶠ[𝓝 z] fun x => -(conn H x ξ)ᵀ := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu] with x h3 h4
    exact conn_dual (h3.of_le one_le_two) h4 ξ
  rw [curv, mdbar_congr he, mdbar_neg, curv, mdbar_transpose (fun x => conn H x ξ), transpose_neg]

theorem conn_changeFrame {A : E → Matrix n n ℂ} (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 1 A z) (hAu : IsUnit (A z).det) (hA0 : ∀ η, mdbar A z η = 0) (ξ : E) :
    conn (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) z ξ =
      (A z)⁻¹ * (conn H z ξ * A z + mdel A z ξ) := by
  refine (eq_conn_of_compatible ?_ ?_).symm
  · simp only [det_mul, det_transpose, det_conjTranspose]
    exact (hAu.mul hu).mul hAu.star
  · rw [mdel_mul (hA.transpose.mul h) hA.conjTranspose.transpose, mdel_mul hA.transpose h,
      mdel_transpose (fun x => (A x)ᴴ), mdel_conjTranspose, hA0, ← conn_transpose_mul hu,
      mdel_transpose, transpose_mul, transpose_nonsing_inv]
    simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ (by rwa [det_transpose] :
      IsUnit (A z)ᵀ.det), transpose_add, transpose_mul, Matrix.add_mul, conjTranspose_zero,
      transpose_zero, Matrix.mul_zero, zero_add]

theorem curv_changeFrame {A : E → Matrix n n ℂ} (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 2 A z) (hAu : IsUnit (A z).det) (hA0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar A x η = 0)
    (ξ η : E) : curv (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) z ξ η = (A z)⁻¹ * curv H z ξ η * A z := by
  have he : (fun x => conn (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) x ξ) =ᶠ[𝓝 z]
      fun x => (A x)⁻¹ * (conn H x ξ * A x + mdel A x ξ) := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu, hA.eventually_two,
      hA.eventually_isUnit hAu, hA0] with x h1 h2 h3 h4 h5
    exact conn_changeFrame (h1.of_le one_le_two) h2 (h3.of_le one_le_two) h4 h5 ξ
  have hA1 : MContDiffAt 1 A z := hA.of_le one_le_two
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have hd : MContDiffAt 1 (fun x => mdel A x ξ) z := hA.mdel (by norm_num) ξ
  have h0 : mddbar A z ξ η = 0 := by
    rw [← mdel_mdbar hA, mdel_congr (B := fun _ => 0) (hA0.mono fun x hx => hx η), mdel_const]
  rw [curv, mdbar_congr he, mdbar_mul (hA1.inv hAu) ((hc.mul hA1).add hd), mdbar_inv hA1 hAu,
    mdbar_add (hc.mul hA1) hd, mdbar_mul hc hA1, mdbar_mdel hA, h0, hA0.self_of_nhds, curv]
  simp [Matrix.mul_assoc]

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E'] {φ : E' → E} {w : E'}

theorem conn_comp_holo (h : MContDiffAt 1 H (φ w)) (hφ : DifferentiableAt ℂ φ w) (ξ : E') :
    conn (fun x => H (φ x)) w ξ = conn H (φ w) (fderiv ℂ φ w ξ) := by
  rw [conn, conn]
  congr 2
  ext a b
  exact del_comp_holo (u := fun y => H y a b) (h.diff a b) hφ ξ

theorem curv_comp_holo (h : MContDiffAt 2 H (φ w)) (hu : IsUnit (H (φ w)).det)
    (hφ : ContDiffAt ℂ 2 φ w) (ξ η : E') :
    curv (fun x => H (φ x)) w ξ η = curv H (φ w) (fderiv ℂ φ w ξ) (fderiv ℂ φ w η) := by
  have hφ1 := hφ.differentiableAt two_ne_zero
  have h1 : MContDiffAt 1 H (φ w) := h.of_le one_le_two
  have hc : MContDiffAt 2 (fun x => H (φ x)) w :=
    fun a b => (h a b).comp w (hφ.restrict_scalars ℝ)
  have e1 : mdel (fun x => H (φ x)) w ξ = mdel H (φ w) (fderiv ℂ φ w ξ) := by
    ext a b; exact del_comp_holo (u := fun y => H y a b) (h1.diff a b) hφ1 ξ
  have e2 : mdbar (fun x => H (φ x)) w η = mdbar H (φ w) (fderiv ℂ φ w η) := by
    ext a b; exact dbar_comp_holo (u := fun y => H y a b) (h1.diff a b) hφ1 η
  have e3 : mddbar (fun x => H (φ x)) w ξ η =
      mddbar H (φ w) (fderiv ℂ φ w ξ) (fderiv ℂ φ w η) := by
    ext a b; exact ddbar_comp_holo (u := fun y => H y a b) (h a b) hφ ξ η
  rw [curv_eq hc hu, curv_eq h hu, e1, e2, e3]

end Pullback

end Frame

def kappa : ℂ := I / (2 * Real.pi)

def ddc (u : E → ℝ) (z ξ η : E) : ℂ := kappa * leviForm u z ξ η

def diagVal {V : Type*} (α : V → V → ℂ) (ξ : V) : ℝ := (-I * α ξ ξ).re

def FormLe {V : Type*} (α β : V → V → ℂ) : Prop := ∀ ξ, diagVal α ξ ≤ diagVal β ξ

def FormAbsLe {V : Type*} (α : V → V → ℂ) (C : ℝ) (β : V → V → ℂ) : Prop :=
  FormLe (fun ξ η => -C * β ξ η) α ∧ FormLe α fun ξ η => C * β ξ η

theorem formAbsLe_iff {V : Type*} {α β : V → V → ℂ} {C : ℝ} :
    FormAbsLe α C β ↔ ∀ ξ, |diagVal α ξ| ≤ C * diagVal β ξ := by
  have h : ∀ (c : ℝ) ξ, diagVal (fun ξ η => c * β ξ η) ξ = c * diagVal β ξ := fun c ξ => by
    rw [diagVal, diagVal, mul_left_comm, re_ofReal_mul]
  simp only [FormAbsLe, FormLe, ← ofReal_neg, h, abs_le, forall_and, neg_mul]

section Tangent

variable {ι : Type*} [Fintype ι]

def formOf (G : Matrix ι ι ℂ) (ξ η : ι → ℂ) : ℂ := I * form G ξ η

theorem diagVal_formOf (G : Matrix ι ι ℂ) (ξ : ι → ℂ) :
    diagVal (formOf G) ξ = (form G ξ ξ).re := by
  rw [diagVal, formOf, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]

theorem diagVal_formOf_eq_gnorm_sq {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (ξ : ι → ℂ) :
    diagVal (formOf G) ξ = gnorm G ξ ^ 2 := by rw [diagVal_formOf, gnorm_sq hG]

theorem leviForm_self_eq_levi {u : (ι → ℂ) → ℝ} {z : ι → ℂ} (hu : ContDiffAt ℝ 2 u z)
    (ξ : ι → ℂ) : leviForm u z ξ ξ = ReciprocityTheory.AnForm.levi u z ξ := by
  rw [leviForm_apply_self hu, ReciprocityTheory.AnForm.levi]; congr 1; ring

theorem diagVal_ddc {u : (ι → ℂ) → ℝ} {z : ι → ℂ} (hu : ContDiffAt ℝ 2 u z) (ξ : ι → ℂ) :
    diagVal (ddc u z) ξ = ReciprocityTheory.AnForm.levi u z ξ / (2 * Real.pi) := by
  have : -I * (kappa * (ReciprocityTheory.AnForm.levi u z ξ : ℂ)) =
      ((ReciprocityTheory.AnForm.levi u z ξ / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa]; push_cast; linear_combination (-(ReciprocityTheory.AnForm.levi u z ξ : ℂ) /
      (2 * Real.pi)) * I_mul_I
  rw [diagVal, ddc, leviForm_self_eq_levi hu, this, ofReal_re]

theorem leviForm_eq_form_hessC {D : ℕ} {u : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (hu : ContDiffAt ℝ 2 u z) (ξ η : Fin D → ℂ) :
    leviForm u z ξ η = form (ReciprocityTheory.AnForm.hessC u z) ξ η := by
  have h : ∀ i j, ReciprocityTheory.AnForm.hessC u z i j =
      leviForm u z (Pi.single i 1) (Pi.single j 1) := fun i j => by
    rw [leviForm_apply hu, ReciprocityTheory.AnForm.hessC]; push_cast; ring
  have e : ∀ v : Fin D → ℂ, v = ∑ i, v i • (Pi.single i 1 : Fin D → ℂ) := fun v => by
    ext j; simp [Pi.single_apply]
  conv_lhs => rw [e ξ, e η]
  simp only [form_eq_sum, h, map_sum, map_smul, map_smulₛₗ, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable [Fintype n]

def OneFormBound (U : Set (ι → ℂ)) (H : (ι → ℂ) → Matrix n n ℂ) (G : (ι → ℂ) → Matrix ι ι ℂ)
    (A : (ι → ℂ) → (ι → ℂ) → Matrix n n ℂ) (C : ℝ) : Prop :=
  ∀ z ∈ U, (H z).PosDef ∧ (G z).PosSemidef ∧
    ∀ ξ, opNorm (H z) (H z) (A z ξ) ≤ C * gnorm (G z) ξ

def TwoFormBound (U : Set (ι → ℂ)) (H : (ι → ℂ) → Matrix n n ℂ) (G : (ι → ℂ) → Matrix ι ι ℂ)
    (F : (ι → ℂ) → (ι → ℂ) → (ι → ℂ) → Matrix n n ℂ) (C : ℝ) : Prop :=
  ∀ z ∈ U, (H z).PosDef ∧ (G z).PosSemidef ∧
    ∀ ξ η, opNorm (H z) (H z) (F z ξ η) ≤ C * gnorm (G z) ξ * gnorm (G z) η

variable {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix n n ℂ} {G : (ι → ℂ) → Matrix ι ι ℂ} {C C' : ℝ}

theorem OneFormBound.mono {A : (ι → ℂ) → (ι → ℂ) → Matrix n n ℂ} (h : OneFormBound U H G A C)
    (hC : C ≤ C') : OneFormBound U H G A C' := fun z hz =>
  ⟨(h z hz).1, (h z hz).2.1, fun ξ => ((h z hz).2.2 ξ).trans
    (mul_le_mul_of_nonneg_right hC (gnorm_nonneg _ _))⟩

theorem TwoFormBound.mono {F : (ι → ℂ) → (ι → ℂ) → (ι → ℂ) → Matrix n n ℂ}
    (h : TwoFormBound U H G F C) (hC : C ≤ C') : TwoFormBound U H G F C' := fun z hz =>
  ⟨(h z hz).1, (h z hz).2.1, fun ξ η => ((h z hz).2.2 ξ η).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (gnorm_nonneg _ _))
      (gnorm_nonneg _ _))⟩

theorem TwoFormBound.norm_form_le {F : (ι → ℂ) → (ι → ℂ) → (ι → ℂ) → Matrix n n ℂ}
    (h : TwoFormBound U H G F C) {z : ι → ℂ} (hz : z ∈ U) (ξ : ι → ℂ) (v : n → ℂ) :
    ‖form (H z) (F z ξ ξ *ᵥ v) v‖ ≤ C * gnorm (G z) ξ ^ 2 * gnorm (H z) v ^ 2 :=
  (norm_form_mulVec_le (h z hz).1 _ v).trans (mul_le_mul_of_nonneg_right
    (((h z hz).2.2 ξ ξ).trans_eq (by ring)) (sq_nonneg _))

theorem twoFormBound_curv_two_mul [DecidableEq n] (hH : IsPosFrame U H)
    (hG : ∀ z ∈ U, (G z).PosSemidef) (hC : 0 ≤ C)
    (h : ∀ z ∈ U, ∀ ξ v, ‖form (H z) (curv H z ξ ξ *ᵥ v) v‖ ≤
      C * gnorm (G z) ξ ^ 2 * gnorm (H z) v ^ 2) : TwoFormBound U H G (curv H) (2 * C) :=
  fun z hz =>
    have h' := hH.isHermFrame
    ⟨hH.posDef z hz, hG z hz, opNorm_le_of_diagonal (hH.posDef z hz) (hG z hz)
      (isSesq_curv (h'.two hz) (h'.isUnit z hz))
      (fun ξ => form_curv (h'.two hz) (h'.eventually_herm hz) (h'.isUnit z hz) ξ ξ) hC (h z hz)⟩

end Tangent

def wedge {V : Type*} (α β : V → V → ℂ) (ξ₁ η₁ ξ₂ η₂ : V) : ℂ :=
  α ξ₁ η₁ * β ξ₂ η₂ + α ξ₂ η₂ * β ξ₁ η₁ - α ξ₁ η₂ * β ξ₂ η₁ - α ξ₂ η₁ * β ξ₁ η₂

theorem wedge_comm {V : Type*} (α β : V → V → ℂ) : wedge α β = wedge β α := by
  ext; simp only [wedge]; ring

def ddcForm (α : E → E → E → ℂ) (z ξ₁ η₁ ξ₂ η₂ : E) : ℂ :=
  kappa * (ddbar (fun x => α x ξ₂ η₂) z ξ₁ η₁ + ddbar (fun x => α x ξ₁ η₁) z ξ₂ η₂
    - ddbar (fun x => α x ξ₂ η₁) z ξ₁ η₂ - ddbar (fun x => α x ξ₁ η₂) z ξ₂ η₁)

section Chern

variable [Fintype n] [DecidableEq n]

def chernOne (H : E → Matrix n n ℂ) (z ξ η : E) : ℂ := kappa * (curv H z ξ η).trace

def curvMinor (H : E → Matrix n n ℂ) (z : E) (a b : n) (ξ₁ η₁ ξ₂ η₂ : E) : ℂ :=
  wedge (fun ξ η => curv H z ξ η a a) (fun ξ η => curv H z ξ η b b) ξ₁ η₁ ξ₂ η₂
    - wedge (fun ξ η => curv H z ξ η a b) (fun ξ η => curv H z ξ η b a) ξ₁ η₁ ξ₂ η₂

def chernTwo (H : E → Matrix n n ℂ) (z ξ₁ η₁ ξ₂ η₂ : E) : ℂ :=
  kappa ^ 2 * (1 / 2 * ∑ a, ∑ b, curvMinor H z a b ξ₁ η₁ ξ₂ η₂)

def chTwo (H : E → Matrix n n ℂ) (z ξ₁ η₁ ξ₂ η₂ : E) : ℂ :=
  kappa ^ 2 / 2 *
    ∑ a, ∑ b, wedge (fun ξ η => curv H z ξ η a b) (fun ξ η => curv H z ξ η b a) ξ₁ η₁ ξ₂ η₂

def lineCurv (H : E → Matrix n n ℂ) (z : E) (w : n → ℂ) (ξ η : E) : ℂ :=
  kappa * (form (H z) (curv H z ξ η *ᵥ w) w / form (H z) w w)

theorem lineCurv_smul (H : E → Matrix n n ℂ) (z : E) (w : n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    lineCurv H z (c • w) = lineCurv H z w := by
  ext ξ η
  have hc' : conj c ≠ 0 := by simpa using hc
  simp only [lineCurv, mulVec_smul, form_smul_left, form_smul_right, mul_div_mul_left _ _ hc,
    mul_div_mul_left _ _ hc']

theorem curvMinor_comm (H : E → Matrix n n ℂ) (z : E) (a b : n) :
    curvMinor H z a b = curvMinor H z b a := by
  ext; simp only [curvMinor, wedge]; ring

theorem curvMinor_self (H : E → Matrix n n ℂ) (z : E) (a : n) (ξ₁ η₁ ξ₂ η₂ : E) :
    curvMinor H z a a ξ₁ η₁ ξ₂ η₂ = 0 := sub_self _

theorem chTwo_eq (H : E → Matrix n n ℂ) (z ξ₁ η₁ ξ₂ η₂ : E) :
    chTwo H z ξ₁ η₁ ξ₂ η₂ =
      (wedge (chernOne H z) (chernOne H z) ξ₁ η₁ ξ₂ η₂ - 2 * chernTwo H z ξ₁ η₁ ξ₂ η₂) / 2 := by
  have h : wedge (chernOne H z) (chernOne H z) ξ₁ η₁ ξ₂ η₂ = kappa ^ 2 * ∑ a, ∑ b,
      wedge (fun ξ η => curv H z ξ η a a) (fun ξ η => curv H z ξ η b b) ξ₁ η₁ ξ₂ η₂ := by
    simp only [wedge, chernOne, trace, diag_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul_sum]
    ring
  simp only [h, chTwo, chernTwo, curvMinor, Finset.sum_sub_distrib]
  ring

theorem chernOne_line [Unique n] {H : E → Matrix n n ℂ} {z : E} {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f z) (hf0 : f z ≠ 0) (hH : ∀ᶠ x in 𝓝 z, H x default default = f x)
    (ξ η : E) : chernOne H z ξ η = -ddc (fun x => Real.log (f x)) z ξ η := by
  rw [chernOne, trace, Fintype.sum_unique, diag_apply, curv_line hf hf0 hH, ddc, mul_neg]

end Chern

section Sub

variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

def secondForm (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : E) : Matrix l m ℂ :=
  blockQS (conn H z ξ)

def secondFormAdj (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : E) : Matrix m l ℂ :=
  adj (subGram (H z)) (quotGram (H z)) (secondForm H z η)

def extForm (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : E) : Matrix m l ℂ :=
  orthProj (H z) * mdbar (fun x => orthLift (H x)) z η

def extFormAdj (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : E) : Matrix l m ℂ :=
  adj (quotGram (H z)) (subGram (H z)) (extForm H z ξ)

def extTrace (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ η : E) : ℂ :=
  kappa * (extFormAdj H z ξ * extForm H z η).trace

variable {U : Set E} {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} {k : WithTop ℕ∞}

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype m] [Fintype l] [DecidableEq m]
  [DecidableEq l] in

theorem MContDiffAt.subGram (h : MContDiffAt k H z) : MContDiffAt k (fun x => subGram (H x)) z :=
  h.submatrix Sum.inl Sum.inl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype l] [DecidableEq l] in

theorem MContDiffAt.quotGram (h : MContDiffAt k H z) (hu : IsUnit (HermFrame.subGram (H z)).det) :
    MContDiffAt k (fun x => quotGram (H x)) z :=
  (h.submatrix Sum.inr Sum.inr).sub (((h.submatrix Sum.inr Sum.inl).mul (h.subGram.inv hu)).mul
    (h.submatrix Sum.inl Sum.inr))

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsHermFrame.sub (h : IsHermFrame U H) (hu : ∀ z ∈ U, IsUnit (subGram (H z)).det) :
    IsHermFrame U fun x => subGram (H x) :=
  .of_mContDiffAt h.isOpen (fun _ hz => (h.mContDiffAt hz).subGram)
    (fun z hz => isHermitian_subGram (h.herm z hz)) hu

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsHermFrame.quot (h : IsHermFrame U H) (hu : ∀ z ∈ U, IsUnit (subGram (H z)).det) :
    IsHermFrame U fun x => quotGram (H x) :=
  .of_mContDiffAt h.isOpen (fun z hz => (h.mContDiffAt hz).quotGram (hu z hz))
    (fun z hz => isHermitian_quotGram (h.herm z hz))
    fun z hz => isUnit_det_quotGram (h.isUnit z hz) (hu z hz)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsPosFrame.sub (h : IsPosFrame U H) : IsPosFrame U fun x => subGram (H x) :=
  (h.isHermFrame.sub fun z hz =>
    (isUnit_iff_isUnit_det _).1 (posDef_subGram (h.posDef z hz)).isUnit).isPosFrame
    fun z hz => posDef_subGram (h.posDef z hz)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsPosFrame.quot (h : IsPosFrame U H) : IsPosFrame U fun x => quotGram (H x) :=
  (h.isHermFrame.quot fun z hz =>
    (isUnit_iff_isUnit_det _).1 (posDef_subGram (h.posDef z hz)).isUnit).isPosFrame
    fun z hz => posDef_quotGram (h.posDef z hz)

theorem secondForm_eq (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : E) :
    secondForm H z ξ = (conn H z ξ).toBlocks₂₁ := blockQS_eq _

theorem form_secondForm (hh : (H z).IsHermitian) (hu : IsUnit (subGram (H z)).det) (ξ : E)
    (s : m → ℂ) (q : l → ℂ) : form (quotGram (H z)) (secondForm H z ξ *ᵥ s) q =
      form (subGram (H z)) s (secondFormAdj H z ξ *ᵥ q) :=
  form_adj (isHermitian_subGram hh) hu (isHermitian_quotGram hh) _ s q

theorem form_secondFormAdj_mul (hh : (H z).IsHermitian) (hu : IsUnit (subGram (H z)).det) (ξ : E)
    (s : m → ℂ) : form (subGram (H z)) (-(secondFormAdj H z ξ * secondForm H z ξ) *ᵥ s) s =
      -form (quotGram (H z)) (secondForm H z ξ *ᵥ s) (secondForm H z ξ *ᵥ s) := by
  rw [← conj_form (isHermitian_quotGram hh), form_secondForm hh hu,
    conj_form (isHermitian_subGram hh), mulVec_mulVec, neg_mulVec, form, form, neg_dotProduct]

theorem extForm_eq_neg_mdbar (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : E) :
    extForm H z η = -mdbar (fun x => orthCoeff (H x)) z η := by
  have h : mdbar (fun x => orthLift (H x)) z η =
      fromRows (-mdbar (fun x => orthCoeff (H x)) z η) 0 := by
    ext (a | a) b <;> simp [orthLift, dbar_neg]
  rw [extForm, h, orthProj, fromCols_mul_fromRows]; simp

theorem extForm_eq_neg_secondFormAdj (h : MContDiffAt 1 H z)
    (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (η : E) : extForm H z η = -secondFormAdj H z η := by
  have hz := hh.self_of_nhds
  have hs' : IsUnit (H z).toBlocks₁₁ᵀ.det := by rwa [det_transpose]

  have h1 : (H z)ᵀ * orthLift (H z) = fromRows 0 (quotGram (H z))ᵀ := by
    have := congrArg transpose (orthLift_transpose_mul hs)
    rwa [transpose_mul, transpose_transpose, transpose_fromCols, transpose_zero] at this

  have h2 : (conn H z η)ᴴ * (H z)ᵀ = (mdbar H z η)ᵀ := by
    have := congrArg conjTranspose (transpose_mul_conn hu η)
    rwa [conjTranspose_mul, hz.transpose.eq,
      show (mdel H z η)ᵀᴴ = (mdel H z η)ᴴᵀ from rfl, conjTranspose_mdel hh] at this
  have h3 : (conn H z η)ᴴ * fromRows (0 : Matrix m l ℂ) (quotGram (H z))ᵀ =
      (mdbar H z η)ᵀ * orthLift (H z) := by
    rw [← h1, ← Matrix.mul_assoc, h2]
  rw [← fromBlocks_toBlocks (conn H z η)ᴴ, ← fromBlocks_toBlocks (mdbar H z η)ᵀ, orthLift,
    fromBlocks_mul_fromRows, fromBlocks_mul_fromRows] at h3
  have h4 := congrArg toRows₁ h3
  simp only [toRows₁_fromRows, Matrix.mul_zero, zero_add, Matrix.mul_one] at h4
  have h11 : MContDiffAt 1 (fun x => (H x).toBlocks₁₁ᵀ) z := h.subGram.transpose
  have h21 : MContDiffAt 1 (fun x => (H x).toBlocks₂₁ᵀ) z :=
    (h.submatrix Sum.inr Sum.inl).transpose
  rw [extForm_eq_neg_mdbar, secondFormAdj, adj, secondForm_eq, Matrix.mul_assoc,
    show (conn H z η).toBlocks₂₁ᴴ = (conn H z η)ᴴ.toBlocks₁₂ from rfl, h4]
  simp only [orthCoeff]
  rw [mdbar_mul (h11.inv hs') h21, mdbar_inv h11 hs',
    show mdbar (fun x => (H x).toBlocks₂₁ᵀ) z η = (mdbar H z η)ᵀ.toBlocks₁₂ from rfl,
    show mdbar (fun x => (H x).toBlocks₁₁ᵀ) z η = (mdbar H z η)ᵀ.toBlocks₁₁ from rfl, subGram]
  simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

theorem adj_adj {A : Matrix m m ℂ} {B : Matrix l l ℂ} (hA : A.IsHermitian) (hAu : IsUnit A.det)
    (hB : B.IsHermitian) (hBu : IsUnit B.det) (T : Matrix l m ℂ) : adj B A (adj A B T) = T := by
  have hA' : IsUnit Aᵀ.det := by rwa [det_transpose]
  have hB' : IsUnit Bᵀ.det := by rwa [det_transpose]
  simp only [adj, conjTranspose_mul, conjTranspose_conjTranspose, hB.transpose.eq,
    hA.transpose.inv.eq, Matrix.mul_assoc, nonsing_inv_mul _ hA', Matrix.mul_one,
    nonsing_inv_mul_cancel_left _ _ hB']

theorem extFormAdj_eq_neg_secondForm (h : MContDiffAt 1 H z)
    (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ : E) : extFormAdj H z ξ = -secondForm H z ξ := by
  have hz := hh.self_of_nhds
  rw [extFormAdj, extForm_eq_neg_secondFormAdj h hh hu hs, secondFormAdj,
    ← adj_adj (isHermitian_subGram hz) hs (isHermitian_quotGram hz) (isUnit_det_quotGram hu hs)
      (secondForm H z ξ),
    adj_adj (isHermitian_quotGram hz) (isUnit_det_quotGram hu hs) (isHermitian_subGram hz) hs]
  simp [adj]

theorem conn_submatrix_equiv [Fintype n] [DecidableEq n] (K : E → Matrix n n ℂ) (e : m ≃ n)
    (z ξ : E) : conn (fun x => (K x).submatrix e e) z ξ = (conn K z ξ).submatrix e e := by
  rw [conn, conn, ← submatrix_mul_equiv _ _ _ e, transpose_submatrix, inv_submatrix_equiv]
  rfl

theorem curv_submatrix_equiv [Fintype n] [DecidableEq n] (K : E → Matrix n n ℂ) (e : m ≃ n)
    (z ξ η : E) : curv (fun x => (K x).submatrix e e) z ξ η = (curv K z ξ η).submatrix e e := by
  simp only [curv, conn_submatrix_equiv]
  rfl

def firstSecondForm {N j : ℕ} (hj : j ≤ N) (K : E → Matrix (Fin N) (Fin N) ℂ) (z ξ : E) :
    Matrix (Fin (N - j)) (Fin j) ℂ := secondForm (fun x => adapt hj (K x)) z ξ

end Sub

section Examples

def tautGram (e : ℕ) (z : Fin e → ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  of fun _ _ => ((1 + ∑ k, ‖z k‖ ^ 2 : ℝ) : ℂ)

theorem contDiff_one_add_normSq (e : ℕ) :
    ContDiff ℝ ∞ fun z : Fin e → ℂ => 1 + ∑ k, ‖z k‖ ^ 2 :=
  contDiff_const.add (ContDiff.sum fun k _ => (contDiff_apply ℝ ℂ k).norm_sq ℂ)

theorem isPosFrame_tautGram (e : ℕ) : IsPosFrame Set.univ (tautGram e) := by
  refine ⟨isOpen_univ, fun _ _ =>
    (ofRealCLM.contDiff.comp (contDiff_one_add_normSq e)).contDiffOn, fun z _ => ?_⟩
  have : tautGram e z = diagonal fun _ => ((1 + ∑ k, ‖z k‖ ^ 2 : ℝ) : ℂ) := by
    ext a b; rw [Subsingleton.elim a b]; simp [tautGram]
  rw [this, posDef_diagonal_iff]
  intro _
  exact_mod_cast (by positivity : (0 : ℝ) < 1 + ∑ k, ‖z k‖ ^ 2)

theorem curv_tautGram_zero (e : ℕ) (ξ η : Fin e → ℂ) :
    curv (tautGram e) 0 ξ η = -(∑ k, ξ k * conj (η k)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b
  rw [curv_line (f := fun z : Fin e → ℂ => 1 + ∑ k, ‖z k‖ ^ 2)
    ((contDiff_one_add_normSq e).contDiffAt.of_le (by norm_cast)) (by simp)
    (Eventually.of_forall fun _ => rfl), Subsingleton.elim a b]
  let φ : (Fin e → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin e) := (EuclideanSpace.equiv (Fin e) ℂ).symm
  have h : (fun x : Fin e → ℂ => Real.log (1 + ∑ k, ‖x k‖ ^ 2)) =
      fun x => Real.log (‖φ x‖ ^ 2 + 1) := by
    funext x; rw [EuclideanSpace.norm_sq_eq, add_comm]; rfl
  rw [h, leviForm_log_normSq_add_comp φ.contDiff.contDiffAt (by simp), φ.fderiv]
  simp [φ, PiLp.inner_apply]

example (ξ : Fin 1 → ℂ) :
    diagVal (chernOne (tautGram 1) 0) ξ = -‖ξ 0‖ ^ 2 / (2 * Real.pi) := by
  have : -I * chernOne (tautGram 1) 0 ξ ξ = ((-‖ξ 0‖ ^ 2 / (2 * Real.pi) : ℝ) : ℂ) := by
    simp only [chernOne, curv_tautGram_zero, kappa, Fin.sum_univ_one, mul_conj', trace_smul,
      trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast
    linear_combination ((‖ξ 0‖ : ℂ) ^ 2 / (2 * Real.pi)) * I_mul_I
  rw [diagVal, this, ofReal_re]

example : ¬ TwoFormBound {0} (tautGram 1) (fun _ => 1) (curv (tautGram 1)) 0 := fun h => by
  have := h.norm_form_le rfl (fun _ => 1) fun _ => 1
  simp [curv_tautGram_zero, form_eq_sum, tautGram, neg_mulVec] at this
  exact absurd this (by norm_num)

example : IsHermFrame Set.univ (fun z => -tautGram 1 z) ∧
    ¬ IsPosFrame Set.univ (fun z => -tautGram 1 z) := by
  have h := (isPosFrame_tautGram 1).isHermFrame
  refine ⟨⟨isOpen_univ, fun a b => (h.smooth a b).neg, fun z hz => (h.herm z hz).neg,
    fun z hz => ?_⟩, fun h' => ?_⟩
  · rw [det_neg]; exact (isUnit_one.neg.pow _).mul (h.isUnit z hz)
  · have := (h'.posDef 0 trivial).diag_pos (i := 0)
    simp [tautGram] at this
    exact absurd this (by norm_num)

def tautPairGram (z : ℂ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  fromBlocks (of fun _ _ => 1 + z * conj z) (of fun _ _ => z) (of fun _ _ => conj z) 1

example (ξ : ℂ) : secondForm tautPairGram 0 ξ () () = ξ := by
  have h : tautPairGram 0 = 1 := by
    rw [← fromBlocks_one]; ext (a | a) (b | b) <;> simp [tautPairGram]
  rw [secondForm_eq, conn, h, transpose_one, inv_one, Matrix.one_mul]
  change del (fun x : ℂ => x) 0 ξ = ξ
  rw [del_eq_fderiv differentiableAt_fun_id]; simp

end Examples

end GlobalTheory.HermFrame
