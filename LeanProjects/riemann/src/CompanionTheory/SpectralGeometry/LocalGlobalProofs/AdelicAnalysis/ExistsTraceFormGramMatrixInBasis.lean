import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TraceCoord

section Abstract

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d M : ℕ}

def coord (β : Module.Basis (Fin d) R A) (x : Fin M → A) : Fin M × Fin d → R :=
  fun p => β.repr (x p.1) p.2

def gramB (s : A →+* A) (β : Module.Basis (Fin d) R A) (J : Matrix (Fin M) (Fin M) A) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) R :=
  fun p q => Algebra.trace R A (s (β p.2) * J p.1 q.1 * β q.2)

theorem trace_hform (s : A →+* A) (hs : ∀ (r : R) (a : A), s (r • a) = r • s a)
    (β : Module.Basis (Fin d) R A) (J : Matrix (Fin M) (Fin M) A) (x y : Fin M → A) :
    Algebra.trace R A (hform s J x y) = coord β x ⬝ᵥ (gramB s β J *ᵥ coord β y) := by
  have hx : ∀ i, s (x i) = ∑ k, β.repr (x i) k • s (β k) := by
    intro i
    calc s (x i) = s (∑ k, β.repr (x i) k • β k) := by rw [β.sum_repr]
      _ = ∑ k, β.repr (x i) k • s (β k) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => hs _ _
  have hy : ∀ j, y j = ∑ l, β.repr (y j) l • β l := fun j => (β.sum_repr (y j)).symm
  have term : ∀ i j, Algebra.trace R A (s (x i) * J i j * y j) =
      ∑ k, ∑ l, β.repr (x i) k *
        (Algebra.trace R A (s (β k) * J i j * β l) * β.repr (y j) l) := by
    intro i j
    rw [hx i]
    conv_lhs => rw [hy j]
    rw [Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  unfold hform coord gramB dotProduct Matrix.mulVec dotProduct
  simp only [map_sum, term, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_comm

theorem coord_mulVec (β : Module.Basis (Fin d) R A) (H : Matrix (Fin M) (Fin M) A)
    (g : Matrix (Fin M × Fin d) (Fin M × Fin d) R)
    (hg : ∀ p q, g p q = β.repr (H p.1 q.1 * β q.2) p.2) (x : Fin M → A) :
    coord β (H *ᵥ x) = g *ᵥ coord β x := by
  funext p
  have hterm : ∀ j, H p.1 j * x j = ∑ l, β.repr (x j) l • (H p.1 j * β l) := by
    intro j
    conv_lhs => rw [← β.sum_repr (x j)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => mul_smul_comm _ _ _
  simp only [coord, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, hg]
  simp only [hterm, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem coord_surj (β : Module.Basis (Fin d) R A) (u : Fin M × Fin d → R) :
    ∃ x : Fin M → A, coord β x = u := by
  refine ⟨fun i => ∑ k, u (i, k) • β k, ?_⟩
  funext p
  change β.repr (∑ k, u (p.1, k) • β k) p.2 = u p
  rw [Module.Basis.repr_sum_self]

theorem hform_eq (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (x y : Fin M → A) :
    hform s J x y = (s ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum, mul_assoc]

theorem dot_mulVec_left {n : Type} [Fintype n] (P : Matrix n n R) (u w : n → R) :
    (P *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Pᵀ *ᵥ w) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem hform_mulVec (s : A →+* A) (J H : Matrix (Fin M) (Fin M) A)
    (hH : cT s H * J * H = J) (x y : Fin M → A) :
    hform s J (H *ᵥ x) (H *ᵥ y) = hform s J x y := by
  have h1 : s ∘ (H *ᵥ x) = (H.map s) *ᵥ (s ∘ x) := by
    funext i
    exact RingHom.map_mulVec s H x i
  have h2 : (H.map s)ᵀ * J * H = J := hH
  rw [hform_eq, hform_eq, h1, dot_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2]

theorem mat_ext {n : Type} [Fintype n] [DecidableEq n] (P Q : Matrix n n R)
    (h : ∀ u v : n → R, u ⬝ᵥ (P *ᵥ v) = u ⬝ᵥ (Q *ᵥ v)) : P = Q := by
  ext p q
  simpa using h (Pi.single p 1) (Pi.single q 1)

end Abstract

section Concrete

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_smul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (r : R) (a : R ⊗[F] E) :
    sigR R σ (r • a) = r • sigR R σ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [sigR, TensorProduct.smul_tmul']
  | add a c ha hc => simp only [smul_add, map_add, ha, hc]

theorem trace_one_tmul (R : Type) [CommRing R] [Algebra F R] [Module.Finite F E] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  have h : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) =
      LinearMap.baseChange R (Algebra.lmul F E e) := by
    ext y
    simp
  rw [Algebra.trace_apply, Algebra.trace_apply, h]
  exact LinearMap.trace_baseChange _ _

theorem gramB_tensor (R : Type) [CommRing R] [Algebra F R] [Module.Finite F E] {d M : ℕ}
    (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) :
    gramB (sigR R σ) (Algebra.TensorProduct.basis R b) (JR R J) =
      (gramB (σ : E →+* E) b J).map (algebraMap F R) := by
  ext p q
  have h : sigR R σ ((1 : R) ⊗ₜ[F] b p.2) * inclR R (J p.1 q.1) * ((1 : R) ⊗ₜ[F] b q.2) =
      (1 : R) ⊗ₜ[F] (σ (b p.2) * J p.1 q.1 * b q.2) := by
    simp [sigR, inclR]
  simp only [gramB, Matrix.map_apply, Algebra.TensorProduct.basis_apply, JR]
  rw [h, trace_one_tmul]
  rfl

end Concrete

section Number

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_smul (σ : E →ₐ[F] E) (r : F) (a : E) :
    (σ : E →+* E) (r • a) = r • (σ : E →+* E) a := by
  simp only [Algebra.smul_def]
  rw [map_mul]
  congr 1
  exact σ.commutes r

theorem sig_sig (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hσ.2.2.2, hσ.2.2.2, star_star]

theorem gramB_symm (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (gramB (σ : E →+* E) b J).IsSymm := by
  haveI : Module.Finite F E := Module.Finite.of_basis b
  ext p q
  let e : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  change Algebra.trace F E (σ (b q.2) * J q.1 p.1 * b p.2) =
    Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)
  rw [← Algebra.trace_eq_of_algEquiv e (σ (b q.2) * J q.1 p.1 * b p.2)]
  congr 1
  change σ (σ (b q.2) * J q.1 p.1 * b p.2) = _
  rw [map_mul, map_mul, sig_sig σ hσ, hJ.1 p.1 q.1]
  ring

theorem gramB_det (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (gramB (σ : E →+* E) b J).det ≠ 0 := by
  haveI : Module.Finite F E := Module.Finite.of_basis b
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  obtain ⟨y, rfl⟩ := coord_surj (M := M) b v
  have hz : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun a => ?_
    have h1 := trace_hform (σ : E →+* E) (sig_smul σ) b J (Pi.single i (σ a)) y
    rw [hv, dotProduct_zero, hform_eq] at h1
    have h2 : ((σ : E →+* E) ∘ (Pi.single i (σ a) : Fin M → E)) ⬝ᵥ (J *ᵥ y) = a * (J *ᵥ y) i := by
      have h3 : ((σ : E →+* E) ∘ (Pi.single i (σ a) : Fin M → E)) = Pi.single i a := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [sig_sig σ hσ]
        · simp [Pi.single_eq_of_ne hj]
      rw [h3, single_dotProduct]
    rw [h2] at h1
    rw [Algebra.traceForm_apply, mul_comm]
    exact h1
  have hy : y = 0 := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hz
  apply hv0
  funext p
  simp [hy, coord]

end Number

theorem exists_trace_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2)) ∧ ∀ h : HA R σ J, ∀ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, (∀ p q, g p q = (Algebra.TensorProduct.basis R b).repr ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) p.1 q.1 * inclR R (b q.2)) p.2) → gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ x : Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  haveI : Module.Finite F E := Module.Finite.of_basis b
  refine ⟨gramB (σ : E →+* E) b J, gramB_symm σ hσ J hJ b, gramB_det σ hσ J hJ b, fun x => ?_,
    fun R _ _ => ?_⟩
  · exact trace_hform (σ : E →+* E) (sig_smul σ) b J x x
  · have key : ∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
        coord (Algebra.TensorProduct.basis R b) x ⬝ᵥ
          ((gramB (σ : E →+* E) b J).map (algebraMap F R) *ᵥ
            coord (Algebra.TensorProduct.basis R b) y) := fun x y => by
      rw [← gramB_tensor]
      exact trace_hform (sigR R σ) (sigR_smul R σ) _ (JR R J) x y
    refine ⟨key, fun h g hg => ?_⟩
    have hact := coord_mulVec (Algebra.TensorProduct.basis R b)
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) g (fun p q => by
        rw [hg, Algebra.TensorProduct.basis_apply]
        rfl)
    refine ⟨?_, hact⟩
    have hU : cT (sigR R σ) (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J :=
      (show HR R σ J from h).2
    apply mat_ext
    intro u v
    obtain ⟨x, rfl⟩ := coord_surj (M := M) (Algebra.TensorProduct.basis R b) u
    obtain ⟨y, rfl⟩ := coord_surj (M := M) (Algebra.TensorProduct.basis R b) v
    have h1 := key ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y)
    have h2 : hR R σ J ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
        ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y :=
      hform_mulVec _ _ _ hU x y
    rw [h2, key x y, hact x, hact y, dot_mulVec_left, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec] at h1
    exact h1.symm

end GlobalTheory.CompanionTheory.SW.TraceCoord
