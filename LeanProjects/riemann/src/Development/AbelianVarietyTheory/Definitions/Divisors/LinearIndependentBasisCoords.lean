import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermTools

open ReciprocityTheory.GeometryOfNumbersTheory Matrix NumberField
open scoped ComplexOrder ComplexConjugate

variable {K E : Type*} [Field K] [Field E] {V V' : Type*} [AddCommGroup V] [Module K V]

def biadd (h : HermFam K V) (σ : K →+* ℂ) : V →+ V →+ ℂ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (h.form σ x) (h.add_right σ x))
    fun x x' => AddMonoidHom.ext fun y => h.form_add_left σ x x' y

theorem ext_form {h h' : HermFam K V} (e : ∀ σ x y, h.form σ x y = h'.form σ x y) : h = h' := by
  obtain ⟨f, _⟩ := h
  obtain ⟨f', _⟩ := h'
  obtain rfl : f = f' := funext fun σ => funext₂ (e σ)
  rfl

section Complex

variable (h : HermFam K V) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]

def csq (c : ι → ℂ) (v : ι → V) : ℝ := (∑ i, ∑ k, conj (c i) * c k * h.form σ (v i) (v k)).re

def cnrm (c : ι → ℂ) (v : ι → V) : ℝ := Real.sqrt (csq h σ c v)

theorem csq_map (a : ι → K) (v : ι → V) :
    csq h σ (fun i => σ (a i)) v = (h.form σ (∑ i, a i • v i) (∑ i, a i • v i)).re := by
  rw [csq, h.form_sum_left]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [h.form_sum_right]
  exact Finset.sum_congr rfl fun k _ => by rw [h.form_smul_left, h.smul_right, mul_assoc]

theorem cnrm_map (a : ι → K) (v : ι → V) : cnrm h σ (fun i => σ (a i)) v = h.nrm σ (∑ i, a i • v i) :=
  congrArg Real.sqrt (csq_map h σ a v)

theorem cnrm_one (x : V) : cnrm h σ (fun _ : Unit => 1) (fun _ => x) = h.nrm σ x := by
  simp [cnrm, csq, HermFam.nrm]

theorem csq_comb {κ : Type*} [Fintype κ] (c : ι → ℂ) (a : ι → κ → K) (b : κ → V) :
    csq h σ c (fun i => ∑ k, a i k • b k) = csq h σ (fun k => ∑ i, c i * σ (a i k)) b := by
  simp only [csq, h.form_sum_left, h.form_sum_right, h.form_smul_left, h.smul_right, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine congrArg _ ?_
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ⟨fun t => (t.2.2.1, t.2.2.2, t.2.1, t.1), fun t => (t.2.2.2, t.2.2.1, t.1, t.2.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ fun t => by simp only [Equiv.coe_fn_mk]; ring

theorem csq_nonneg (c : ι → ℂ) (v : ι → V) : 0 ≤ csq h σ c v := by
  let S := Submodule.span K (Set.range v)
  have : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range v)
  let b := Module.finBasis K S
  have e : v = fun i => ∑ k, b.repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ k • (b k : V) := funext fun i => by
    exact (congrArg S.subtype (b.sum_repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩).symm).trans (map_sum _ _ _)
  rw [e, csq_comb]
  generalize (fun k => ∑ i, c i * σ _) = x
  have := (h.posDef σ _ _ (b.linearIndependent.map' S.subtype S.ker_subtype)).posSemidef.dotProduct_mulVec_nonneg x
  refine (Complex.nonneg_iff.1 this).1.trans_eq (congrArg _ ?_)
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

theorem cnrm_sq (c : ι → ℂ) (v : ι → V) : cnrm h σ c v ^ 2 = csq h σ c v := Real.sq_sqrt (csq_nonneg h σ c v)

theorem nrm_pos {x : V} (hx : x ≠ 0) : 0 < h.nrm σ x := by
  have := (h.posDef σ 1 ![x] (by simpa using hx)).diag_pos (i := 0)
  exact Real.sqrt_pos.2 (Complex.pos_iff.1 this).1

end Complex

def ofCoords {P : (K →+* ℂ) → Type*} [∀ σ, Fintype (P σ)] (φ : ∀ σ, V →ₛₗ[σ] (P σ → ℂ))
    (G : ∀ σ, Matrix (P σ) (P σ) ℂ) (hG : ∀ σ, (G σ).PosDef)
    (hφ : ∀ σ n (v : Fin n → V), LinearIndependent K v → LinearIndependent ℂ fun i => φ σ (v i)) :
    HermFam K V where
  form σ x y := star (φ σ x) ⬝ᵥ G σ *ᵥ φ σ y
  add_right σ x y z := by rw [map_add, mulVec_add, dotProduct_add]
  smul_right σ a x y := by rw [map_smulₛₗ, mulVec_smul, dotProduct_smul, smul_eq_mul]
  conj_symm σ x y := by
    rw [starRingEnd_apply, ← star_dotProduct_star, star_star, star_mulVec, (hG σ).1.eq, ← dotProduct_mulVec]
  posDef σ n v hv := by
    classical
    have := (hG σ).conjTranspose_mul_mul_same (B := Matrix.of fun p i => φ σ (v i) p)
      (Matrix.mulVec_injective_iff.2 (hφ σ n v hv))
    convert this using 1
    ext i j
    simp [dotProduct, mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

def comap [AddCommGroup V'] [Module K V'] (h : HermFam K V) (f : V' →ₗ[K] V) (hf : Function.Injective f) :
    HermFam K V' where
  form σ x y := h.form σ (f x) (f y)
  add_right σ x y z := by rw [map_add, h.add_right]
  smul_right σ a x y := by rw [map_smul, h.smul_right]
  conj_symm σ x y := h.conj_symm σ _ _
  posDef σ n v hv := h.posDef σ n _ (hv.map' f (LinearMap.ker_eq_bot.2 hf))

@[simp] theorem nrm_comap [AddCommGroup V'] [Module K V'] (h : HermFam K V) (f : V' →ₗ[K] V)
    (hf : Function.Injective f) (σ : K →+* ℂ) (x : V') : (comap h f hf).nrm σ x = h.nrm σ (f x) := rfl

theorem isConjInv_comap [AddCommGroup V'] [Module K V'] {h : HermFam K V} (hh : h.IsConjInv) (f : V' →ₗ[K] V)
    (hf : Function.Injective f) : (comap h f hf).IsConjInv := fun σ _ _ => hh σ _ _

def scale (h : HermFam K V) (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) : HermFam K V where
  form σ x y := (c σ ^ 2 : ℝ) * h.form σ x y
  add_right σ x y z := by rw [h.add_right, mul_add]
  smul_right σ a x y := by rw [h.smul_right, mul_left_comm]
  conj_symm σ x y := by rw [map_mul, h.conj_symm, Complex.conj_ofReal]
  posDef σ n v hv := (h.posDef σ n v hv).smul (a := ((c σ ^ 2 : ℝ) : ℂ))
    (Complex.zero_lt_real.2 (pow_pos (hc σ) 2))

@[simp] theorem nrm_scale (h : HermFam K V) (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) (σ : K →+* ℂ) (x : V) :
    (scale h c hc).nrm σ x = c σ * h.nrm σ x := by
  rw [HermFam.nrm, scale, Complex.re_ofReal_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hc σ).le, HermFam.nrm]

def basisCoords {n : Type*} [Finite n] (b : Module.Basis n K V) (σ : K →+* ℂ) : V →ₛₗ[σ] (n → ℂ) where
  toFun x i := σ (b.repr x i)
  map_add' x y := funext fun i => by simp
  map_smul' a x := funext fun i => by simp

theorem linearIndependent_basisCoords {n ι : Type*} [Finite n] (b : Module.Basis n K V) (σ : K →+* ℂ) {v : ι → V}
    (hv : LinearIndependent K v) : LinearIndependent ℂ fun i => basisCoords b σ (v i) :=
  letI := σ.toAlgebra
  linearIndependent_algebraMap_comp_iff.2 (hv.map' b.equivFun.toLinearMap b.equivFun.ker)

def ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) (G : (K →+* ℂ) → Matrix n n ℂ)
    (hG : ∀ σ, (G σ).PosDef) : HermFam K V :=
  ofCoords (P := fun _ => n) (basisCoords b) G hG fun σ _ _ => linearIndependent_basisCoords b σ

theorem form_ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) (G : (K →+* ℂ) → Matrix n n ℂ)
    (hG : ∀ σ, (G σ).PosDef) (σ : K →+* ℂ) (i j : n) : (ofGram b G hG).form σ (b i) (b j) = G σ i j := by
  classical
  simp [ofGram, ofCoords, basisCoords, dotProduct, mulVec, Finsupp.single_apply, apply_ite]

theorem isConjInv_ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) {G : (K →+* ℂ) → Matrix n n ℂ}
    (hG : ∀ σ, (G σ).PosDef) (hc : ∀ σ i j, G (ComplexEmbedding.conjugate σ) i j = conj (G σ i j)) :
    (ofGram b G hG).IsConjInv := fun σ x y => by
  simp [ofGram, ofCoords, basisCoords, dotProduct, mulVec, hc]

def ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) : HermFam K V :=
  ofGram b (fun _ => 1) fun _ => PosDef.one

theorem nrm_ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) (σ : K →+* ℂ) (i : n) :
    (ofBasis b).nrm σ (b i) = 1 := by
  simp [HermFam.nrm, ofBasis, form_ofGram]

theorem isConjInv_ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) :
    (ofBasis b).IsConjInv := isConjInv_ofGram b _ fun _ i j => by simp [Matrix.one_apply, apply_ite]

section Extend

variable [AddCommGroup V'] [Module E V'] {j : K →+* E}

structure IsExtension (ι : V →ₛₗ[j] V') : Prop where

  indep : ∀ (n : ℕ) (v : Fin n → V), LinearIndependent K v → LinearIndependent E fun i => ι (v i)

  span : Submodule.span E (Set.range ι) = ⊤

variable {ι : V →ₛₗ[j] V'} (hι : IsExtension ι)

def IsExtension.basis {n : ℕ} (b : Module.Basis (Fin n) K V) : Module.Basis (Fin n) E V' :=
  Module.Basis.mk (hι.indep n b b.linearIndependent) (hι.span.ge.trans (Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))))

@[simp] theorem IsExtension.basis_apply {n : ℕ} (b : Module.Basis (Fin n) K V) (i : Fin n) :
    hι.basis b i = ι (b i) := Module.Basis.mk_apply _ _ _

variable [FiniteDimensional K V]

include hι in

theorem IsExtension.finrank_eq : Module.finrank E V' = Module.finrank K V :=
  (Module.finrank_eq_card_basis (hι.basis (Module.finBasis K V))).trans (Fintype.card_fin _)

def extend (h : HermFam K V) : HermFam E V' :=
  ofGram (hι.basis (Module.finBasis K V)) (fun τ => h.gram (τ.comp j) (Module.finBasis K V))
    fun _ => h.posDef _ _ _ (Module.finBasis K V).linearIndependent

theorem form_extend (h : HermFam K V) (τ : E →+* ℂ) (x y : V) :
    (extend hι h).form τ (ι x) (ι y) = h.form (τ.comp j) x y := by
  let b := Module.finBasis K V
  have e (i k) : (extend hι h).form τ (ι (b i)) (ι (b k)) = h.form (τ.comp j) (b i) (b k) := by
    rw [← hι.basis_apply, ← hι.basis_apply]
    exact form_ofGram _ _ _ τ i k
  rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smulₛₗ, HermFam.form_sum_left, HermFam.form_sum_right, HermFam.form_smul_left,
    HermFam.smul_right, e, RingHom.comp_apply]

theorem nrm_extend (h : HermFam K V) (τ : E →+* ℂ) (x : V) : (extend hι h).nrm τ (ι x) = h.nrm (τ.comp j) x :=
  congrArg (fun z : ℂ => Real.sqrt z.re) (form_extend hι h τ x x)

theorem isConjInv_extend {h : HermFam K V} (hh : h.IsConjInv) : (extend hι h).IsConjInv :=
  isConjInv_ofGram _ _ fun τ _ _ => hh (τ.comp j) _ _

end Extend

example (σ : ℚ →+* ℂ) : csq (ofBasis (Pi.basisFun ℚ (Fin 2))) σ ![Complex.I, 2] (Pi.basisFun ℚ (Fin 2)) = 5 := by
  simp only [csq, ofBasis, form_ofGram, Fin.sum_univ_two]
  simp
  norm_num

end GlobalTheory.HermTools
