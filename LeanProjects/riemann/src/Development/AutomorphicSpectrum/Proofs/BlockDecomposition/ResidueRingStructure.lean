import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf

noncomputable section

namespace GlobalTheory.CompanionTheory.RvRingPf

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem repr_one_tmul {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr ((1 : Fv F v) ⊗ₜ[F] e) k =
      algebraMap F (Fv F v) (bs.repr e k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem struct_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (i j k : Fin d) :
    algebraMap F (Fv F v) (bs.repr (bs i * bs j) k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
  exact Finset.mem_image.2 ⟨(i, j, k), Finset.mem_univ _, rfl⟩

theorem one_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (k : Fin d) :
    algebraMap F (Fv F v) (bs.repr 1 k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩

theorem sig_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (i k : Fin d) :
    algebraMap F (Fv F v) (bs.repr (σ (bs i)) k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_image.2 ⟨(i, k), Finset.mem_univ _, rfl⟩

theorem repr_mul {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr (x * y) k =
      ∑ i, ∑ j, ((Algebra.TensorProduct.basis (Fv F v) bs).repr x i *
        (Algebra.TensorProduct.basis (Fv F v) bs).repr y j) *
          algebraMap F (Fv F v) (bs.repr (bs i * bs j) k) := by
  set bK := Algebra.TensorProduct.basis (Fv F v) bs with hbK
  have e : x * y = ∑ i, ∑ j, (bK.repr x i * bK.repr y j) • ((1 : Fv F v) ⊗ₜ[F] (bs i * bs j)) := by
    conv_lhs => rw [← bK.sum_repr x, ← bK.sum_repr y]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, hbK, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← bK.coord_apply, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, bK.coord_apply, hbK, repr_one_tmul, smul_eq_mul]

theorem repr_sig (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (x : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr (sigR (Fv F v) σ x) k =
      ∑ i, (Algebra.TensorProduct.basis (Fv F v) bs).repr x i *
        algebraMap F (Fv F v) (bs.repr (σ (bs i)) k) := by
  set bK := Algebra.TensorProduct.basis (Fv F v) bs with hbK
  have e : sigR (Fv F v) σ x = ∑ i, bK.repr x i • ((1 : Fv F v) ⊗ₜ[F] σ (bs i)) := by
    conv_lhs => rw [← bK.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbK, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp [sigR]
  rw [← bK.coord_apply, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, bK.coord_apply, hbK, repr_one_tmul, smul_eq_mul]

def ringOf {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) : Subring (Fv F v ⊗[F] E) where
  carrier := Rv bs v
  mul_mem' := by
    intro x y hx hy k
    rw [repr_mul]
    exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (hx i) (hy j)) (struct_int h i j k)
  one_mem' := by
    intro k
    rw [Algebra.TensorProduct.one_def, repr_one_tmul]
    exact one_int h k
  add_mem' := by
    intro x y hx hy k
    rw [map_add, Finsupp.add_apply]
    exact add_mem (hx k) (hy k)
  zero_mem' := by
    intro k
    rw [map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx k
    rw [map_neg, Finsupp.neg_apply]
    exact neg_mem (hx k)

theorem sigR_mem {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (x : Fv F v ⊗[F] E) (hx : x ∈ ringOf h) :
    sigR (Fv F v) σ x ∈ ringOf h := by
  intro k
  rw [repr_sig]
  exact sum_mem fun i _ => mul_mem (hx i) (sig_int h i k)

theorem rvRing : PositivityTheory.SiegelWeilFormula.Gunr.RvRing := by
  intro F E _ _ _ _ _ σ d bs v h
  exact ⟨ringOf h, (sigR (Fv F v) σ).restrict (ringOf h) (ringOf h) (sigR_mem h), rfl, fun x => rfl⟩

end GlobalTheory.CompanionTheory.RvRingPf

end
