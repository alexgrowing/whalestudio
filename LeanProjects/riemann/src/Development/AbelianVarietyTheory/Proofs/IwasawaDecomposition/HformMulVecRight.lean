import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

namespace GlobalTheory.GaugeEx.GramPair

section Ring

variable {A : Type} [CommRing A] (s : A →+* A) {M N : ℕ} (G : Matrix (Fin M) (Fin M) A)

theorem hform_eq_dot (x y : Fin M → A) :
    Formalism.UG.hform s G x y = (fun i => s (x i)) ⬝ᵥ G *ᵥ y := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (P : Matrix (Fin M) (Fin N) A) (x y : Fin N → A) :
    Formalism.UG.hform s G (P *ᵥ x) (P *ᵥ y) = Formalism.UG.hform s (Formalism.UG.cT s P * G * P) x y := by
  have e : (fun i => s ((P *ᵥ x) i)) = (fun i => s (x i)) ᵥ* Formalism.UG.cT s P := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose]
    exact RingHom.map_mulVec _ _ _ i
  rw [hform_eq_dot, hform_eq_dot, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

theorem hform_mulVec_right (P : Matrix (Fin M) (Fin N) A) (x : Fin M → A) (w : Fin N → A) :
    Formalism.UG.hform s G x (P *ᵥ w) = ∑ j, Formalism.UG.hform s G x (fun i => P i j) * w j := by
  simp only [Formalism.UG.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem hform_symm (hs : ∀ a, s (s a) = a) (hG : ∀ i j, s (G j i) = G i j) (x y : Fin M → A) :
    Formalism.UG.hform s G y x = s (Formalism.UG.hform s G x y) := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hG]
  ring

theorem hform_lin (a b c d : A) (x y : Fin M → A) :
    Formalism.UG.hform s G (a • x + b • y) (c • x + d • y) =
      s a * c * Formalism.UG.hform s G x x + s a * d * Formalism.UG.hform s G x y +
        s b * c * Formalism.UG.hform s G y x + s b * d * Formalism.UG.hform s G y y := by
  simp only [Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, map_add, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Ring

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]

theorem conj_conj (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [conj_conj σ h]

omit [NumberField F] [NumberField E] in
theorem sigR_alg (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  show r ⊗ₜ[F] σ 1 = r ⊗ₜ[F] 1
  rw [map_one]

omit [NumberField F] [NumberField E] in
theorem hR_rat {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x z : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (z i)) = inclR R (hE σ J x z) := by
  simp [hR, hE, Formalism.UG.hform, sigR, JR, inclR, TensorProduct.tmul_sum]

theorem half_trace (h : IsCMExt F E σ) (k : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (algebraMap R (R ⊗[F] E) k) = k := by
  have h2 : Algebra.trace F E 1 = 2 := by
    have := Algebra.trace_algebraMap (R := F) (S := E) 1
    rw [map_one, h.2.2.1] at this
    rw [this]; norm_num
  have h1 : Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] (1 : E)) = algebraMap F R 2 := by
    rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange,
      ← Algebra.trace_apply, h2]
  rw [Algebra.algebraMap_eq_smul_one k, map_smul, Algebra.TensorProduct.one_def, h1, smul_eq_mul,
    mul_left_comm, ← map_mul, show (1 / 2 * 2 : F) = 1 by norm_num, map_one, mul_one]

omit [NumberField F] [NumberField E] in
theorem JR_cT {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M) (Fin N) E) :
    Formalism.UG.cT (sigR R σ) (B.map (inclR (F := F) R)) * JR (F := F) R J * B.map (inclR (F := F) R) =
      JR (F := F) R (Formalism.UG.cT (σ : E →+* E) B * J * B) := by
  rw [JR, JR, Matrix.map_mul, Matrix.map_mul]
  rfl

end Tens

theorem gram_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → Continuous (gram3 R σ J) ∧ ∃ n : R ⊗[F] E → R, Continuous n ∧ n 0 = 0 ∧ ∀ (g : HA R σ J) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (y' : Fin 1 → Fin M → R ⊗[F] E) (r r' : R) (t : R ⊗[F] E), g • ratTup (F := F) R x = y → gram3 R σ J ![algebraMap R (R ⊗[F] E) r • y 0, t • y 0 + algebraMap R (R ⊗[F] E) r' • pairOf R σ J B y g y' 1] = (r * r * algebraMap F R a, algebraMap R (R ⊗[F] E) (r * algebraMap F R a) * t, n t + r' * r' * qR R σ J' (y' 0)) := by
  intro F E _ _ _ _ _ σ h R _ _ _ _ _ _ _ _ _ M J x a B J' hS
  obtain ⟨hJ, -, hx, hB, hJ', -⟩ := hS
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  have hc : ∀ i j : Fin 2, Continuous fun X : Fin 2 → Fin (M + 1) → R ⊗[F] E =>
      hR R σ J (X i) (X j) := by
    intro i j
    unfold hR Formalism.UG.hform
    fun_prop
  refine ⟨(continuous_const.mul (h1.comp (hc 0 0))).prodMk
    ((hc 0 1).prodMk (continuous_const.mul (h1.comp (hc 1 1)))),
    fun t => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (sigR R σ t * t * algebraMap R (R ⊗[F] E) (algebraMap F R a)),
    continuous_const.mul (h1.comp ((h2.mul continuous_id).mul continuous_const)), by simp, ?_⟩
  intro g y y' r r' t hy
  set G : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) := (HA.mat R σ J g).1 with hG
  have hk : Formalism.UG.cT (sigR R σ) G * JR R J * G = JR R J := (show HR R σ J from g).2
  have hact : ∀ u v, hR R σ J (G *ᵥ u) (G *ᵥ v) = hR R σ J u v := fun u v => by
    rw [hR, hform_mulVec, hk, hR]
  have hy0 : y 0 = G *ᵥ (fun i => inclR R (x 0 i)) := by rw [← hy]; rfl
  set z := pairOf R σ J B y g y' 1 with hz
  have hz0 : z = G *ᵥ (B.map (inclR (F := F) R) *ᵥ y' 0) := rfl
  have e00 : hR R σ J (y 0) (y 0) = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    rw [hy0, hact, hR_rat, hx, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes a
  have e01 : hR R σ J (y 0) z = 0 := by
    rw [hy0, hz0, hact, hR, hform_mulVec_right]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := hR_rat σ R J (x 0) (fun i => B i j)
    rw [hB, map_zero] at this
    exact mul_eq_zero_of_left this _
  have hJs : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  have e10 : hR R σ J z (y 0) = 0 := by
    rw [hR, hform_symm _ _ (sigR_sigR σ R h) hJs, ← hR, e01, map_zero]
  have e11 : hR R σ J z z = hR R σ J' (y' 0) (y' 0) := by
    rw [hz0, hact, hR, hform_mulVec, JR_cT, ← hJ', hR]
  have lin : ∀ p q u v : R ⊗[F] E, hR R σ J (p • y 0 + q • z) (u • y 0 + v • z) =
      sigR R σ p * u * algebraMap R (R ⊗[F] E) (algebraMap F R a) +
        sigR R σ q * v * hR R σ J' (y' 0) (y' 0) := by
    intro p q u v
    rw [hR, hform_lin, ← hR, ← hR, ← hR, ← hR, e00, e01, e10, e11]
    ring
  have f0 : algebraMap R (R ⊗[F] E) r • y 0 =
      algebraMap R (R ⊗[F] E) r • y 0 + (0 : R ⊗[F] E) • z := by simp
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show qR R σ J (algebraMap R (R ⊗[F] E) r • y 0) = r * r * algebraMap F R a
    rw [qR, f0, lin, sigR_alg, mul_zero, zero_mul, add_zero, ← map_mul, ← map_mul, half_trace σ R h]
  · show hR R σ J (algebraMap R (R ⊗[F] E) r • y 0) (t • y 0 + algebraMap R (R ⊗[F] E) r' • z) =
      algebraMap R (R ⊗[F] E) (r * algebraMap F R a) * t
    rw [f0, lin, sigR_alg, map_zero, map_mul]
    ring
  · show qR R σ J (t • y 0 + algebraMap R (R ⊗[F] E) r' • z) =
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (sigR R σ t * t * algebraMap R (R ⊗[F] E) (algebraMap F R a)) + r' * r' * qR R σ J' (y' 0)
    rw [qR, lin, sigR_alg, ← map_mul, ← Algebra.smul_def (r' * r'), map_add, map_smul, qR, smul_eq_mul]
    ring

end GlobalTheory.GaugeEx.GramPair
