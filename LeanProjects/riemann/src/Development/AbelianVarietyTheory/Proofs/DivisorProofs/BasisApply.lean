import Mathlib
open NumberField

noncomputable section
namespace GlobalTheory.UnitaryStd

variable {r g : ℕ}

def matAddEnd (V : Type) [AddCommGroup V] (r : ℕ) : Matrix (Fin r) (Fin r) ℤ →+* AddMonoid.End (Fin r → V) where
  toFun M :=
    { toFun := fun x i => ∑ j, M i j • x j
      map_zero' := by ext i; simp
      map_add' := fun x y => by ext i; simp [smul_add, Finset.sum_add_distrib] }
  map_one' := AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (1 : Matrix (Fin r) (Fin r) ℤ) i j • x j = x i
    simp [Matrix.one_apply, ite_smul]
  map_mul' := fun M N => AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (M * N) i j • x j = ∑ k, M i k • ∑ j, N k j • x j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  map_zero' := AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (0 : Matrix (Fin r) (Fin r) ℤ) i j • x j = 0
    simp
  map_add' := fun M N => AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (M + N) i j • x j = ∑ j, M i j • x j + ∑ j, N i j • x j
    simp [add_smul, Finset.sum_add_distrib]

@[nolint unusedArguments]
def Lat {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) : Type :=
  Fin r → (Fin g → ℤ) × (Fin g → ℤ)

variable {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)

instance : AddCommGroup (Lat ρ g) := inferInstanceAs (AddCommGroup (Fin r → (Fin g → ℤ) × (Fin g → ℤ)))

instance : Module (𝓞 E) (Lat ρ g) :=
  Module.compHom (Fin r → (Fin g → ℤ) × (Fin g → ℤ)) ((matAddEnd ((Fin g → ℤ) × (Fin g → ℤ)) r).comp ρ)

variable {ρ g}

theorem smul_apply (a : 𝓞 E) (x : Lat ρ g) (i : Fin r) : (a • x) i = ∑ j, ρ a i j • x j := rfl

theorem add_apply (x y : Lat ρ g) (i : Fin r) : (x + y) i = x i + y i := rfl

theorem zsmul_apply (n : ℤ) (x : Lat ρ g) (i : Fin r) : (n • x) i = n • x i := rfl

theorem neg_apply (x : Lat ρ g) (i : Fin r) : (-x) i = -x i := rfl

theorem zero_apply (i : Fin r) : (0 : Lat ρ g) i = 0 := rfl

@[ext] theorem ext {x y : Lat ρ g} (h : ∀ i, x i = y i) : x = y := funext h

variable (ρ g)

def coordEquiv : Lat ρ g ≃ₗ[ℤ] (Fin r × (Fin g ⊕ Fin g) → ℤ) where
  toFun x := fun p => Sum.elim (x p.1).1 (x p.1).2 p.2
  invFun c := fun i => (fun k => c (i, Sum.inl k), fun k => c (i, Sum.inr k))
  left_inv x := by ext i <;> rfl
  right_inv c := by ext ⟨i, k | k⟩ <;> rfl
  map_add' x y := by ext ⟨i, k | k⟩ <;> rfl
  map_smul' n x := by ext ⟨i, k | k⟩ <;> rfl

def basis : Module.Basis (Fin r × (Fin g ⊕ Fin g)) ℤ (Lat ρ g) := Module.Basis.ofEquivFun (coordEquiv ρ g)

instance : Module.Free ℤ (Lat ρ g) := Module.Free.of_basis (basis ρ g)
instance : Module.Finite ℤ (Lat ρ g) := Module.Finite.of_basis (basis ρ g)

def form (S : Matrix (Fin r) (Fin r) ℤ) : LinearMap.BilinForm ℤ (Lat ρ g) :=
  LinearMap.mk₂ ℤ (fun x y => ∑ i, ∑ j, S i j * ((x i).1 ⬝ᵥ (y j).2 - (x i).2 ⬝ᵥ (y j).1))
    (fun x y z => by
      simp only [add_apply, Prod.fst_add, Prod.snd_add, add_dotProduct, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun n x y => by
      simp only [zsmul_apply, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun x y z => by
      simp only [add_apply, Prod.fst_add, Prod.snd_add, dotProduct_add, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun n x y => by
      simp only [zsmul_apply, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem form_apply (S : Matrix (Fin r) (Fin r) ℤ) (x y : Lat ρ g) :
    form ρ g S x y = ∑ i, ∑ j, S i j * ((x i).1 ⬝ᵥ (y j).2 - (x i).2 ⬝ᵥ (y j).1) := rfl

def cx : Lat ρ g →ₗ[ℤ] Lat ρ g where
  toFun x := fun i => ((x i).2, -(x i).1)
  map_add' x y := by
    funext i
    refine Prod.ext (funext fun k => rfl) (funext fun k => ?_)
    show -((x i).1 k + (y i).1 k) = -(x i).1 k + -(y i).1 k
    ring
  map_smul' n x := by
    funext i
    refine Prod.ext (funext fun k => rfl) (funext fun k => ?_)
    show -(n * (x i).1 k) = n * -(x i).1 k
    ring

theorem cx_apply (x : Lat ρ g) (i : Fin r) : cx ρ g x i = ((x i).2, -(x i).1) := rfl

def act (a : 𝓞 E) : Lat ρ g →ₗ[ℤ] Lat ρ g := (DistribMulAction.toAddMonoidHom (Lat ρ g) a).toIntLinearMap

theorem act_apply (a : 𝓞 E) (x : Lat ρ g) : act ρ g a x = a • x := rfl

theorem basis_repr (x : Lat ρ g) (p : Fin r × (Fin g ⊕ Fin g)) :
    (basis ρ g).repr x p = Sum.elim (x p.1).1 (x p.1).2 p.2 := rfl

theorem basis_apply (p : Fin r × (Fin g ⊕ Fin g)) (i : Fin r) :
    basis ρ g p i = (fun k => Pi.single (M := fun _ => ℤ) p 1 (i, Sum.inl k),
      fun k => Pi.single (M := fun _ => ℤ) p 1 (i, Sum.inr k)) := by
  rw [basis, Module.Basis.coe_ofEquivFun]
  rfl

end GlobalTheory.UnitaryStd
