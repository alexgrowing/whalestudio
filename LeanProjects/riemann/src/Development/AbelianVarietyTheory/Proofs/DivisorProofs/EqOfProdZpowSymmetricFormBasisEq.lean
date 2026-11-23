import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.SymMono

def elem {r : ℕ} (a b : Fin r) : LinearMap.BilinForm ℤ (Fin r → ℤ) :=
  (LinearMap.mul ℤ ℤ).compl₁₂ (LinearMap.proj a) (LinearMap.proj b)

@[simp] theorem elem_apply {r : ℕ} (a b : Fin r) (u v : Fin r → ℤ) : elem a b u v = u a * v b := rfl

def symElem {r : ℕ} (a b : Fin r) : LinearMap.BilinForm ℤ (Fin r → ℤ) :=
  (if a ≤ b then elem a b else 0) + (if a < b then elem b a else 0)

theorem symElem_symm {r : ℕ} (a b : Fin r) (u v : Fin r → ℤ) : symElem a b u v = symElem a b v u := by
  unfold symElem
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, h.le]; ring
  · simp; ring
  · simp [not_le.2 h, not_lt.2 h.le]

theorem ite_bil_apply {r : ℕ} (p : Prop) [Decidable p] (f : LinearMap.BilinForm ℤ (Fin r → ℤ)) (u v : Fin r → ℤ) :
    (if p then f else 0) u v = if p then f u v else 0 := by
  split_ifs <;> rfl

theorem sum_symElem {r : ℕ} (β : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hβ : ∀ u v, β u v = β v u) :
    β = ∑ a, ∑ b, β (Pi.single a 1) (Pi.single b 1) • symElem a b := by
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℤ (Fin r)) fun i j => ?_
  simp only [Pi.basisFun_apply, LinearMap.sum_apply, LinearMap.smul_apply, symElem,
    LinearMap.add_apply, smul_eq_mul]
  simp only [ite_bil_apply, elem_apply, Pi.single_apply, mul_add, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul]
  simp only [← ite_and]
  rw [Fintype.sum_eq_single i (fun x hx => Fintype.sum_eq_zero _ (fun y => if_neg (by tauto))),
    Fintype.sum_eq_single j (fun x hx => Fintype.sum_eq_zero _ (fun y => if_neg (by tauto))),
    Fintype.sum_eq_single j (fun y hy => if_neg (by tauto)),
    Fintype.sum_eq_single i (fun y hy => if_neg (by tauto))]
  rcases le_or_gt i j with h | h
  · simp [h, not_lt.2 h]
  · simp [h, not_le.2 h, hβ (Pi.single i 1)]

end GlobalTheory.SymMono

namespace GlobalTheory.SymMono

theorem zpow_finsum {G J : Type} [CommGroup G] (g : G) (s : Finset J) (f : J → ℤ) :
    g ^ (∑ i ∈ s, f i) = ∏ i ∈ s, g ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem symElem_mem {r : ℕ} (a b : Fin r) : symElem a b ∈ balForms (id : ℤ → ℤ) (Fin r → ℤ) :=
  mem_balForms_int.2 (symElem_symm a b)

theorem repr_self_eq_sum {r : ℕ} {I : Type} (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (i k : I) :
    ε.repr (ε i) k = ∑ a, ∑ b, (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1) (Pi.single b 1) *
      ε.repr ⟨symElem a b, symElem_mem a b⟩ k := by
  have he : ε i = ∑ a, ∑ b, (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1) (Pi.single b 1) •
      (⟨symElem a b, symElem_mem a b⟩ : balForms (id : ℤ → ℤ) (Fin r → ℤ)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact sum_symElem _ (mem_balForms_int.1 (ε i).2)
  conv_lhs => rw [he]
  simp only [map_sum, LinearEquiv.map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem eq_of_prod_zpow_eq (F : Type) [Field F] (r : ℕ) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (x y : I → F) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (h : ∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b =
      ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) : x = y := by
  classical
  set X : I → Fˣ := fun i => Units.mk0 (x i) (hx i) with hXd
  set Y : I → Fˣ := fun i => Units.mk0 (y i) (hy i) with hYd
  have hXY : ∀ a b, ∏ i, (X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) = 1 := by
    intro a b
    rw [Finset.prod_congr rfl (fun i _ => div_zpow _ _ _), Finset.prod_div_distrib, div_eq_one]
    apply Units.ext
    simpa [X, Y, Units.coe_prod] using h a b
  funext k
  have hk : X k / Y k = 1 := by
    calc X k / Y k = ∏ i, (X i / Y i) ^ (ε.repr (ε i) k) := by
          simp [Finsupp.single_apply]
      _ = ∏ i, ∏ a, ∏ b, ((X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1)
            (Pi.single b 1))) ^ (ε.repr ⟨symElem a b, symElem_mem a b⟩ k) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [repr_self_eq_sum, zpow_finsum]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [zpow_finsum]
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [zpow_mul]
      _ = ∏ a, ∏ b, (∏ i, (X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1)
            (Pi.single b 1))) ^ (ε.repr ⟨symElem a b, symElem_mem a b⟩ k) := by
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [Finset.prod_zpow]
      _ = 1 := by simp [hXY]
  simpa [X, Y] using congrArg Units.val (div_eq_one.1 hk)

end GlobalTheory.SymMono

example : ∀ (F : Type) [Field F] (r : ℕ) (I : Type) [Fintype I] (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (x y : I → F), (∀ i, x i ≠ 0) → (∀ i, y i ≠ 0) → (∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b = ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) → x = y := GlobalTheory.SymMono.eq_of_prod_zpow_eq
