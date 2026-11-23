import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem map_trace_tensor {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    p (Algebra.trace A (A ⊗[F] E) z) =
      Algebra.trace B (B ⊗[F] E) (Algebra.TensorProduct.map p (AlgHom.id F E) z) := by
  have key : ∀ (C : Type) [CommRing C] [Algebra F C] (c : C) (e : E),
      Algebra.trace C (C ⊗[F] E) (c ⊗ₜ[F] e) = c * algebraMap F C (Algebra.trace F E e) := by
    intro C _ _ c e
    have h1 : (c ⊗ₜ[F] e : C ⊗[F] E) = c • ((1 : C) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, smul_eq_mul]
    congr 1
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
    congr 1
    ext x
    simp
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e => rw [Algebra.TensorProduct.map_tmul, key, key, map_mul, AlgHom.commutes]; rfl

theorem map_sesq_sum_eq_zero {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (q : A →+* B) (σ : A →+* A)
    (hσ : ∀ z, q z = 0 → q (σ z) = 0) (a : Fin m → Fin m → A) (b : Fin n → Fin n → A)
    (x y : Matrix (Fin m) (Fin n) A) (h : x.map q = 0 ∨ y.map q = 0) :
    q (∑ i, ∑ j, ∑ k, ∑ l, σ (y i j) * a k i * b j l * x k l) = 0 := by
  have hk : ∀ i j k l (a b : A), q (σ (y i j) * a * b * x k l) = 0 := by
    intro i j k l a b
    rw [map_mul, map_mul, map_mul]
    rcases h with h | h
    · have h1 : q (x k l) = 0 := congrFun (congrFun h k) l
      rw [h1, mul_zero]
    · have h1 : q (y i j) = 0 := congrFun (congrFun h i) j
      rw [hσ _ h1, zero_mul, zero_mul, zero_mul]
  simp only [map_sum, hk, Finset.sum_const_zero]

theorem map_trace_sesq_eq_zero {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (p : A →ₐ[F] B) (s : E →ₐ[F] E) {m n : ℕ}
    (c : A ⊗[F] E) (a : Fin m → Fin m → A ⊗[F] E) (b : Fin n → Fin n → A ⊗[F] E)
    (x y : Matrix (Fin m) (Fin n) (A ⊗[F] E))
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0) :
    p (Algebra.trace A (A ⊗[F] E) (c * ∑ i, ∑ j, ∑ k, ∑ l, sigR A s (y i j) * a k i * b j l * x k l)) = 0 := by
  have hc : ∀ z : A ⊗[F] E, (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A s z) =
      sigR B s ((Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [RingHom.map_zero]
    | add a b ha hb => simp only [RingHom.map_add, ha, hb]
    | tmul a e => rfl
  have hh := map_sesq_sum_eq_zero (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A s)
    (fun z hz => by rw [hc, hz, map_zero]) a b x y h
  rw [map_trace_tensor, map_mul]
  erw [hh]
  rw [mul_zero, map_zero]

variable {D : D7}

theorem map_sympl_eq_zero {B : Type} [CommRing B] [Algebra D.host.F B] (p : AF D.host.F →ₐ[D.host.F] B)
    (V W : HSp D) (x y : WA V W)
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0) :
    p (sympl V W x y) = 0 := by
  unfold sympl hHom
  split_ifs
  · exact map_trace_sesq_eq_zero p D.sp.cm.sig _ (fun k i => incA D (V.gram k i))
      (fun j l => incA D (W.gram j l)) x y h
  · exact map_trace_sesq_eq_zero p D.sp.cm.sig _ (fun k i => incA D (V.gram i k))
      (fun j l => incA D (W.gram l j)) x y h

theorem sympl_parts (D : D7) (V W : HSp D) (x y : WA V W) :
    ((IsRealW V W x ∨ IsRealW V W y) → sndA D.host.F (sympl V W x y) = 0) ∧
      ((x.map (infPart D) = 0 ∨ y.map (infPart D) = 0) → fstA D.host.F (sympl V W x y) = 0) :=
  ⟨fun h => map_sympl_eq_zero (sndA D.host.F) V W x y h, fun h => map_sympl_eq_zero (fstA D.host.F) V W x y h⟩

end GlobalTheory.FockCompare
