import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CoordMat

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_one_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

def traceGram (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) F :=
  fun p q => Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)

def coordL (R : Type) [CommRing R] [Algebra F R] (M : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin M → R ⊗[F] E) ≃ₗ[R] (Fin M × Fin d → R) :=
  (LinearEquiv.piCongrRight fun _ => (Algebra.TensorProduct.basis R b).equivFun).trans
    (LinearEquiv.curry R R (Fin M) (Fin d)).symm

theorem coordL_apply (R : Type) [CommRing R] [Algebra F R] (M : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (x : Fin M → R ⊗[F] E) (p : Fin M × Fin d) :
    coordL R M b x p = (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := rfl

theorem trace_expand [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (u v : R ⊗[F] E) (e : E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * inclR R e * v) =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr u k *
        (algebraMap F R (Algebra.trace F E (σ (b k) * e * b l)) *
          (Algebra.TensorProduct.basis R b).repr v l) := by
  have hx : ∀ z : R ⊗[F] E, z = ∑ k, (Algebra.TensorProduct.basis R b).repr z k • ((1 : R) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hs : ∀ (r : R) (w : R ⊗[F] E), sigR R σ (r • w) = r • sigR R σ w := by
    intro r w
    exact map_smul (Algebra.TensorProduct.map (AlgHom.id R R) (σ : E →ₐ[F] E)) r w
  generalize hcu : (Algebra.TensorProduct.basis R b).repr u = cu
  generalize hcv : (Algebra.TensorProduct.basis R b).repr v = cv
  have hu : u = ∑ k, cu k • ((1 : R) ⊗ₜ[F] b k) := by rw [← hcu]; exact hx u
  have hv : v = ∑ k, cv k • ((1 : R) ⊗ₜ[F] b k) := by rw [← hcv]; exact hx v
  rw [hu, hv, map_sum, Finset.sum_mul, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 : sigR R σ ((1 : R) ⊗ₜ[F] b k) = (1 : R) ⊗ₜ[F] σ (b k) := by simp [sigR]
  have h2 : inclR R e = (1 : R) ⊗ₜ[F] e := rfl
  rw [hs, h1, h2, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, map_smul, map_smul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul,
    trace_one_tmul, smul_eq_mul, smul_eq_mul]
  ring

theorem trace_hR [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (x y : Fin M → R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
      coordL R M b x ⬝ᵥ (traceGram σ J b).map (algebraMap F R) *ᵥ coordL R M b y := by
  simp only [hR, hform, map_sum, JR, Matrix.map_apply, trace_expand R σ b]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, coordL_apply, traceGram, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem hform_mulVec {A : Type} [CommRing A] (s : A →+* A) {M : ℕ} (J g : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s (cT s g * J * g) x y := by
  have h : ∀ (K : Matrix (Fin M) (Fin M) A) (u v : Fin M → A), hform s K u v = (s ∘ u) ⬝ᵥ (K *ᵥ v) := by
    intro K u v
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hc : s ∘ (g *ᵥ x) = (g.map s) *ᵥ (s ∘ x) := by
    funext i
    exact RingHom.map_mulVec s g x i
  rw [h, h, hc, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  simp only [cT, Matrix.mul_assoc]

theorem matrix_ext_dot {ι A : Type} [Fintype ι] [DecidableEq ι] [CommRing A] (P Q : Matrix ι ι A)
    (h : ∀ u v : ι → A, u ⬝ᵥ P *ᵥ v = u ⬝ᵥ Q *ᵥ v) : P = Q := by
  ext p q
  simpa using h (Pi.single p 1) (Pi.single q 1)

theorem dot_conj {ι A : Type} [Fintype ι] [CommRing A] (g P : Matrix ι ι A) (u v : ι → A) :
    u ⬝ᵥ (gᵀ * P * g) *ᵥ v = (g *ᵥ u) ⬝ᵥ P *ᵥ (g *ᵥ v) := by
  rw [← Matrix.vecMul_transpose g u, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem traceGram_isSymm [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j) (b : Module.Basis (Fin d) F E) :
    (traceGram σ J b).IsSymm := by
  let e : E ≃ₐ[F] E := AlgEquiv.ofBijective σ
    ⟨σ.toRingHom.injective, fun x => ⟨σ x, hσ x⟩⟩
  refine Matrix.IsSymm.ext fun p q => ?_
  simp only [traceGram]
  have hm : e (σ (b q.2) * J q.1 p.1 * b p.2) = σ (b p.2) * J p.1 q.1 * b q.2 := by
    change σ (σ (b q.2) * J q.1 p.1 * b p.2) = _
    rw [map_mul, map_mul, hσ, hJ]
    ring
  exact (Algebra.trace_eq_of_algEquiv e _).symm.trans (congrArg _ hm)

theorem traceGram_det_ne_zero [FiniteDimensional F E] [Algebra.IsSeparable F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (b : Module.Basis (Fin d) F E) : (traceGram σ J b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hv
  let y : Fin M → E := fun j => ∑ l, v (j, l) • b l
  have h1 : ∀ i k, Algebra.trace F E (σ (b k) * (J *ᵥ y) i) = 0 := by
    intro i k
    have h := congrFun hBv (i, k)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, traceGram, Pi.zero_apply] at h
    rw [← h]
    simp only [Matrix.mulVec, dotProduct, y, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm, mul_assoc]
  have h2 : ∀ i z, Algebra.trace F E (z * (J *ᵥ y) i) = 0 := by
    intro i z
    have hz : z = ∑ k, b.repr (σ z) k • σ (b k) := by
      have h := congrArg σ (b.sum_repr (σ z))
      rw [hσ, map_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun k _ => map_smul σ _ _)
    rw [hz, Finset.sum_mul, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_mul_assoc, map_smul, h1, smul_zero]
  have h3 : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun z => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact h2 i z
  have h4 := Matrix.eq_zero_of_mulVec_eq_zero hJ h3
  funext p
  exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun l => v (p.1, l)) (congrFun h4 p.1) p.2

theorem hR_mat (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y := by
  have hm : cT (sigR R σ) (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := (show HR R σ J from h).2
  rw [hR, hform_mulVec, hm, hR]

end Alg

theorem coord_orthogonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (h : HA R σ J), ∃ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ X : Fin 1 → Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (actW R σ J h X 0 p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2 := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  refine ⟨traceGram σ J b, traceGram_isSymm σ hσ J hJ.1 b, traceGram_det_ne_zero σ hσ J hJ.2 b,
    fun R _ _ h => ?_⟩
  let c := coordL (F := F) (E := E) R M b
  let T : (Fin M → R ⊗[F] E) →ₗ[R] (Fin M → R ⊗[F] E) :=
    (Matrix.mulVecLin (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E))).restrictScalars R
  let g : Matrix (Fin M × Fin d) (Fin M × Fin d) R :=
    LinearMap.toMatrix' (c.toLinearMap ∘ₗ T ∘ₗ c.symm.toLinearMap)
  have hg : ∀ x, g *ᵥ c x = c ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) := by
    intro x
    simp [g, T, LinearMap.toMatrix'_mulVec]
  refine ⟨g, ?_, fun X => (hg (X 0)).symm⟩
  refine matrix_ext_dot _ _ fun u v => ?_
  obtain ⟨x, rfl⟩ := c.surjective u
  obtain ⟨y, rfl⟩ := c.surjective v
  rw [dot_conj, hg, hg]
  have hx := trace_hR R σ J b x y
  have hy := trace_hR R σ J b ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
    ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y)
  rw [hR_mat] at hy
  exact hy.symm.trans hx

end GlobalTheory.CompanionTheory.SW.CoordMat
