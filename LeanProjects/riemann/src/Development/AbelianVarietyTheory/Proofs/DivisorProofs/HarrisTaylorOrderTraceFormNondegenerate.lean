import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open NumberField
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HTOrderTrace

theorem trace_tmul_padic {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (z : ℤ_[p]) (a : R) :
    Algebra.trace ℤ_[p] (ℤ_[p] ⊗[ℤ] R) (z ⊗ₜ a) = (Algebra.trace ℤ R a : ℤ_[p]) * z := by
  have h1 : (z ⊗ₜ a : ℤ_[p] ⊗[ℤ] R) = z • (1 ⊗ₜ a) := by simp [TensorProduct.smul_tmul']
  have h2 : Algebra.lmul ℤ_[p] (ℤ_[p] ⊗[ℤ] R) (1 ⊗ₜ a) =
      (Algebra.lmul ℤ R a).baseChange ℤ_[p] := by
    ext c
    simp
  rw [h1, map_smul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, smul_eq_mul, mul_comm]
  rfl

theorem trace_form_padic_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (u : ℤ_[p] ⊗[ℤ] 𝓞 E),
    (∀ w, Algebra.trace ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) (u * w) = 0) → u = 0 := by
  intro E _ _ p _ u hu
  classical
  let b0 := RingOfIntegers.basis E
  let b1 := b0.baseChange ℤ_[p]
  have h1 : Algebra.discr ℤ_[p] b1 = (NumberField.discr E : ℤ_[p]) := by
    rw [NumberField.discr, Algebra.discr_def, Algebra.discr_def]
    rw [show ((Algebra.traceMatrix ℤ (RingOfIntegers.basis E)).det : ℤ_[p]) =
      Int.castRingHom ℤ_[p] (Algebra.traceMatrix ℤ (RingOfIntegers.basis E)).det from rfl,
      RingHom.map_det]
    congr 1
    ext i j
    simp [b1, b0, Algebra.traceForm_apply, trace_tmul_padic]
  have h0 : (NumberField.discr E : ℤ_[p]) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero E)
  have hnd : (Algebra.traceForm ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)).Nondegenerate := by
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b1]
    have : LinearMap.BilinForm.toMatrix b1 (Algebra.traceForm ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)) =
        Algebra.traceMatrix ℤ_[p] b1 := by
      ext i j; simp [Algebra.traceMatrix_apply]
    rw [this, ← Algebra.discr_def, h1]; exact h0
  exact hnd.1 u (fun w => by simpa [Algebra.traceForm_apply] using hu w)

theorem ringHom_padic_eq_algebraMap : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [Ring B] [Algebra ℤ_[p] B] [Module.Free ℤ_[p] B]
    (f : ℤ_[p] →+* B), f = algebraMap ℤ_[p] B := by
  intro p _ B _ _ _ f
  ext c
  rw [← sub_eq_zero]
  set b := Module.Free.chooseBasis ℤ_[p] B
  have hdiv : ∀ n : ℕ, ∃ v : B, f c - algebraMap ℤ_[p] B c = (p : ℤ_[p]) ^ n • v := by
    intro n
    obtain ⟨μ, hμ⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n c)
    have hc : c = (c.appr n : ℤ_[p]) + (p : ℤ_[p]) ^ n * μ := by rw [← hμ]; ring
    refine ⟨f μ - algebraMap ℤ_[p] B μ, ?_⟩
    conv_lhs => rw [hc]
    rw [smul_sub, Algebra.smul_def, Algebra.smul_def, map_add, map_add, map_mul, map_mul, map_pow, map_pow,
      map_natCast, map_natCast, map_natCast, map_natCast]
    noncomm_ring
  apply b.repr.injective
  ext i
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  obtain ⟨v, hv⟩ := hdiv ((b.repr (f c - algebraMap ℤ_[p] B c) i).valuation + 1)
  have hmem : b.repr (f c - algebraMap ℤ_[p] B c) i ∈
      Ideal.span {(p : ℤ_[p]) ^ ((b.repr (f c - algebraMap ℤ_[p] B c) i).valuation + 1)} := by
    rw [Ideal.mem_span_singleton]
    conv_rhs => rw [hv]
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have := (PadicInt.mem_span_pow_iff_le_valuation _ hne _).1 hmem
  omega

theorem matrix_basis_repr {ι R A : Type} [CommRing R] [AddCommGroup A] [Module R A] (m : ℕ) (b : Module.Basis ι R A)
    (M : Matrix (Fin m) (Fin m) A) (i j : Fin m) (k : ι) :
    (b.matrix (Fin m) (Fin m)).repr M (i, j, k) = b.repr (M i j) k := by
  simp only [Module.Basis.matrix, Module.Basis.map_repr, Module.Basis.repr_reindex_apply, LinearEquiv.trans_apply]
  rfl

theorem trace_mulLeft_matrix_eq : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (m : ℕ) (Z : Matrix (Fin m) (Fin m) A),
    LinearMap.trace R (Matrix (Fin m) (Fin m) A) (LinearMap.mulLeft R Z) = (m : R) * Algebra.trace R A Z.trace := by
  intro R A _ _ _ _ _ m Z
  classical
  let b := Module.Free.chooseBasis R A
  rw [LinearMap.trace_eq_matrix_trace R (b.matrix (Fin m) (Fin m)), Matrix.trace, Matrix.trace, map_sum,
    Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, Algebra.trace_eq_matrix_trace b, Matrix.trace]
  have key : ∀ j : Fin m, ∑ k, ((LinearMap.toMatrix (b.matrix (Fin m) (Fin m)) (b.matrix (Fin m) (Fin m)))
      (LinearMap.mulLeft R Z)).diag (i, j, k) = ∑ k, ((Algebra.leftMulMatrix b) (Z.diag i)).diag k := by
    intro j
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [LinearMap.toMatrix_apply, matrix_basis_repr, Algebra.leftMulMatrix_eq_repr_mul, Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem trace_mulLeft_baseChange_eq_zero : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (R : Type) [CommRing R] (x : O),
    (∀ y, LinearMap.trace ℤ O (LinearMap.mulLeft ℤ (x * y)) = 0) →
    ∀ Y : R ⊗[ℤ] O, LinearMap.trace R (R ⊗[ℤ] O) (LinearMap.mulLeft R ((1 ⊗ₜ x) * Y)) = 0 := by
  intro O _ _ _ R _ x hx Y
  have hb : ∀ z : O, LinearMap.mulLeft R ((1 : R) ⊗ₜ[ℤ] z) = (LinearMap.mulLeft ℤ z).baseChange R := by
    intro z; ext c w; simp
  induction Y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb' =>
    rw [mul_add, show LinearMap.mulLeft R ((1 ⊗ₜ x) * a + (1 ⊗ₜ x) * b) =
      LinearMap.mulLeft R ((1 ⊗ₜ x) * a) + LinearMap.mulLeft R ((1 ⊗ₜ x) * b) from
      map_add (LinearMap.mul R (R ⊗[ℤ] O)) _ _, map_add, ha, hb', add_zero]
  | tmul r y =>
    have h1 : ((1 : R) ⊗ₜ[ℤ] x) * (r ⊗ₜ y) = r • ((1 : R) ⊗ₜ[ℤ] (x * y)) := by
      simp [TensorProduct.smul_tmul']
    rw [h1, show LinearMap.mulLeft R (r • ((1 : R) ⊗ₜ[ℤ] (x * y))) =
      r • LinearMap.mulLeft R ((1 : R) ⊗ₜ[ℤ] (x * y)) from
      map_smul (LinearMap.mul R (R ⊗[ℤ] O)) _ _, map_smul, hb, LinearMap.trace_baseChange, hx, map_zero, smul_zero]

theorem inj_tmul (p : ℕ) [Fact p.Prime] (O : Type) [Ring O] [Module.Free ℤ O] (x : O)
    (h : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = 0) : x = 0 := by
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ ℤ_[p]) (RingHom.injective_int (algebraMap ℤ ℤ_[p]))
  have h1 : (Algebra.linearMap ℤ ℤ_[p]).rTensor O ((1 : ℤ) ⊗ₜ x) = 0 := by simpa using h
  have h2 := hinj (h1.trans (map_zero _).symm)
  simpa using congrArg (TensorProduct.lid ℤ O) h2

theorem trace_order_nondeg : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O),
    (∀ y : D.O, LinearMap.trace ℤ D.O (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  intro p _ D x hx
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨φ⟩ := D.splitP
  set A' := ℤ_[p] ⊗[ℤ] 𝓞 D.F
  let Φ : (ℤ_[p] ⊗[ℤ] D.O) ≃+* Matrix (Fin D.m) (Fin D.m) A' :=
    (Algebra.TensorProduct.comm ℤ ℤ_[p] D.O).toRingEquiv.trans
      (φ.toRingEquiv.trans (Algebra.TensorProduct.comm ℤ (𝓞 D.F) ℤ_[p]).toRingEquiv.mapMatrix)
  have hψ : Φ.toRingHom.comp (algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] D.O)) =
      algebraMap ℤ_[p] (Matrix (Fin D.m) (Fin D.m) A') := ringHom_padic_eq_algebraMap p _ _
  have hΦs : ∀ (c : ℤ_[p]) (X : ℤ_[p] ⊗[ℤ] D.O), Φ (c • X) = c • Φ X := by
    intro c X
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr 1
    exact congrArg (fun f => f c) hψ
  let e : (ℤ_[p] ⊗[ℤ] D.O) ≃ₗ[ℤ_[p]] Matrix (Fin D.m) (Fin D.m) A' :=
    { Φ.toAddEquiv with map_smul' := hΦs }
  have hconj : ∀ W : ℤ_[p] ⊗[ℤ] D.O, LinearMap.mulLeft ℤ_[p] (Φ W) = e.conj (LinearMap.mulLeft ℤ_[p] W) := by
    intro W
    ext V
    simp [LinearEquiv.conj_apply, e]
  set Z := Φ (1 ⊗ₜ x)
  have hZ : ∀ Y, Algebra.trace ℤ_[p] A' (Z * Y).trace = 0 := by
    intro Y
    have h1 := trace_mulLeft_baseChange_eq_zero D.O ℤ_[p] x hx (Φ.symm Y)
    rw [← LinearMap.trace_conj' _ e, ← hconj, map_mul, RingEquiv.apply_symm_apply, trace_mulLeft_matrix_eq] at h1
    have hm : (D.m : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 D.m_pos.ne'
    exact (mul_eq_zero.1 h1).resolve_left hm
  have hZ0 : Z = 0 := by
    ext i j
    apply trace_form_padic_eq_zero D.F p
    intro a
    have := hZ (Matrix.single j i a)
    rwa [Matrix.trace_mul_single, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at this
  have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = 0 := by
    rw [← map_eq_zero_iff Φ Φ.injective]; exact hZ0
  exact inj_tmul p D.O x h1

end GlobalTheory.HTOrderTrace
