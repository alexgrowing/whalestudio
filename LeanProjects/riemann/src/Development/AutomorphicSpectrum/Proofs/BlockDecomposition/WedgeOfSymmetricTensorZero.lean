import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace GlobalTheory.CompanionTheory.WedgeOf

section SymmWedge

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

theorem wedgeT_tmul_self (a : V) : wedgeT (R := R) V (a ⊗ₜ[R] a) = 0 := by
  rw [wedgeT_tmul]
  exact (exteriorPower.ιMulti R (M := V) 2).map_eq_zero_of_eq ![a, a]
    (i := 0) (j := 1) rfl (by decide)

theorem wedgeT_tmul_add_swap (a b : V) :
    wedgeT (R := R) V (a ⊗ₜ[R] b) + wedgeT (R := R) V (b ⊗ₜ[R] a) = 0 := by
  have h := wedgeT_tmul_self (R := R) (a + b)
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add,
    map_add, wedgeT_tmul_self, wedgeT_tmul_self, zero_add, add_zero] at h
  exact h

theorem sum_sum_eq_zero_of_antisymm {ι M : Type} [DecidableEq ι] [AddCommGroup M]
    (f : ι → ι → M) (hd : ∀ i, f i i = 0) (ha : ∀ i j, f i j + f j i = 0) (s : Finset ι) :
    ∑ i ∈ s, ∑ j ∈ s, f i j = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    simp only [Finset.sum_insert has, Finset.sum_add_distrib, ih, hd, zero_add, add_zero]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ ha a i

theorem wedgeT_eq_zero_of_basis {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V)
    (t : V ⊗[R] V) (ht : TensorProduct.comm R V V t = t) : wedgeT (R := R) V t = 0 := by
  set B := b.tensorProduct b with hB
  have hsym : ∀ i j, B.repr t (i, j) = B.repr t (j, i) := by
    have key : ∀ (i j : ι) (s : V ⊗[R] V),
        B.repr (TensorProduct.comm R V V s) (i, j) = B.repr s (j, i) := by
      intro i j s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp [hB, Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]
      | add x y hx hy => simp [map_add, hx, hy]
    intro i j
    rw [← key i j t, ht]
  have hexp : t = ∑ i, ∑ j, B.repr t (i, j) • (b i ⊗ₜ[R] b j) := by
    conv_lhs => rw [← B.sum_repr t]
    rw [Fintype.sum_prod_type]
    simp [hB, Module.Basis.tensorProduct_apply]
  rw [hexp]
  simp only [map_sum, map_smul]
  refine sum_sum_eq_zero_of_antisymm
    (fun i j ↦ B.repr t (i, j) • wedgeT (R := R) V (b i ⊗ₜ[R] b j)) ?_ ?_ Finset.univ
  · intro i
    simp [wedgeT_tmul_self]
  · intro i j
    show B.repr t (i, j) • _ + B.repr t (j, i) • _ = 0
    rw [hsym j i, ← smul_add, wedgeT_tmul_add_swap, smul_zero]

theorem map_wedgeT {W : Type} [AddCommGroup W] [Module R W] (r : W →ₗ[R] V) (s : W ⊗[R] W) :
    exteriorPower.map 2 r (wedgeT (R := R) W s) = wedgeT (R := R) V (TensorProduct.map r r s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [TensorProduct.map_tmul, wedgeT_tmul, wedgeT_tmul, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    fin_cases i <;> rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem wedgeT_eq_zero_of_symm (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Projective R V] (t : V ⊗[R] V)
    (ht : t - TensorProduct.comm R V V t = 0) : wedgeT (R := R) V t = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' R V
  obtain ⟨i, hi⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hri : ∀ v, r (i v) = v := fun v ↦ LinearMap.congr_fun hi v
  have hcomm : TensorProduct.comm R V V t = t := (sub_eq_zero.1 ht).symm
  have hmap : ∀ s : V ⊗[R] V, TensorProduct.comm R (Fin n → R) (Fin n → R) (TensorProduct.map i i s)
      = TensorProduct.map i i (TensorProduct.comm R V V s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hback : ∀ s : V ⊗[R] V, TensorProduct.map r r (TensorProduct.map i i s) = s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hri]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hW : wedgeT (R := R) (Fin n → R) (TensorProduct.map i i t) = 0 :=
    wedgeT_eq_zero_of_basis (Pi.basisFun R (Fin n)) _ (by rw [hmap, hcomm])
  have := map_wedgeT r (TensorProduct.map i i t)
  rw [hW, map_zero, hback] at this
  exact this.symm

end SymmWedge

end GlobalTheory.CompanionTheory.WedgeOf
