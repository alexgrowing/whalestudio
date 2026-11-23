import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory TopRep ContRepresentation

universe u v w

section Cons

variable {G : Type v} [TopologicalSpace G]

def finConsHomeomorph (m : ℕ) : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by simp
  right_inv x := by simp
  continuous_toFun := Continuous.finCons (A := fun _ : Fin (m + 1) => G) continuous_fst continuous_snd
  continuous_invFun := (continuous_apply 0).prodMk (continuous_pi fun _ => continuous_apply _)

@[simp]
theorem finConsHomeomorph_symm_apply (m : ℕ) (x : Fin (m + 1) → G) :
    (finConsHomeomorph m).symm x = (x 0, Fin.tail x) :=
  rfl

end Cons

variable {k G : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

def nestedHomeomorph (X : TopRep.{u} k G) : (m : ℕ) → resolutionX X m ≃ₜ C(Fin m → G, X)
  | 0 => Homeomorph.continuousMapOfUnique
  | m + 1 => ((Homeomorph.refl G).arrowCongr (nestedHomeomorph X m)).trans
      (Homeomorph.curry.symm.trans ((finConsHomeomorph m).arrowCongr (Homeomorph.refl X)))

variable (X : TopRep.{u} k G)

@[simp]
theorem nestedHomeomorph_zero_apply (v : resolutionX X 0) (x : Fin 0 → G) :
    nestedHomeomorph X 0 v x = v :=
  rfl

theorem nestedHomeomorph_succ_apply (m : ℕ) (f : resolutionX X (m + 1))
    (x : Fin (m + 1) → G) :
    nestedHomeomorph X (m + 1) f x =
      nestedHomeomorph X m ((f : C(G, resolutionX X m)) (x 0)) (Fin.tail x) :=
  rfl

theorem nestedHomeomorph_add (m : ℕ) (a b : resolutionX X m) :
    nestedHomeomorph X m (a + b) = nestedHomeomorph X m a + nestedHomeomorph X m b := by
  induction m with
  | zero => ext x; rfl
  | succ m ih =>
    ext x
    change nestedHomeomorph X m (((a + b : resolutionX X (m + 1)) : C(G, resolutionX X m)) (x 0))
        (Fin.tail x) = nestedHomeomorph X m ((a : C(G, resolutionX X m)) (x 0)) (Fin.tail x) +
          nestedHomeomorph X m ((b : C(G, resolutionX X m)) (x 0)) (Fin.tail x)
    rw [ContinuousMap.add_apply, ih]
    rfl

theorem nestedHomeomorph_smul (m : ℕ) (r : k) (a : resolutionX X m) :
    nestedHomeomorph X m (r • a) = r • nestedHomeomorph X m a := by
  induction m with
  | zero => ext x; rfl
  | succ m ih =>
    ext x
    change nestedHomeomorph X m (((r • a : resolutionX X (m + 1)) : C(G, resolutionX X m)) (x 0))
        (Fin.tail x) = r • nestedHomeomorph X m ((a : C(G, resolutionX X m)) (x 0)) (Fin.tail x)
    rw [ContinuousMap.smul_apply, ih]
    rfl

def nestedLinearEquiv (m : ℕ) : resolutionX X m ≃ₗ[k] C(Fin m → G, X) where
  toFun := nestedHomeomorph X m
  invFun := (nestedHomeomorph X m).symm
  map_add' := nestedHomeomorph_add X m
  map_smul' := nestedHomeomorph_smul X m
  left_inv := (nestedHomeomorph X m).symm_apply_apply
  right_inv := (nestedHomeomorph X m).apply_symm_apply

@[simp]
theorem nestedLinearEquiv_apply (m : ℕ) (a : resolutionX X m) :
    nestedLinearEquiv X m a = nestedHomeomorph X m a :=
  rfl

theorem nestedHomeomorph_ρ_apply (m : ℕ) (g : G) (a : resolutionX X m) (x : Fin m → G) :
    nestedHomeomorph X m ((resolutionX X m).ρ g a) x =
      X.ρ g (nestedHomeomorph X m a fun i => g⁻¹ * x i) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [nestedHomeomorph_succ_apply, nestedHomeomorph_succ_apply]
    exact ih _ _

theorem nestedHomeomorph_d_apply (m : ℕ) (a : resolutionX X m) (x : Fin (m + 1) → G) :
    nestedHomeomorph X (m + 1) ((d X m).hom a) x =
      ∑ i : Fin (m + 1), (-1 : k) ^ (i : ℕ) • nestedHomeomorph X m a (fun j => x (i.succAbove j)) := by
  induction m with
  | zero =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp only [Fin.val_zero, pow_zero, one_smul]
    rfl
  | succ m ih =>
    have h1 : ((d X (m + 1)).hom a : C(G, resolutionX X (m + 1))) (x 0) =
        a - (d X m).hom ((a : C(G, resolutionX X m)) (x 0)) := by
      rw [hom_d_succ]
      rfl
    rw [nestedHomeomorph_succ_apply, h1,
      show nestedHomeomorph X (m + 1) (a - (d X m).hom ((a : C(G, resolutionX X m)) (x 0))) =
        nestedHomeomorph X (m + 1) a -
          nestedHomeomorph X (m + 1) ((d X m).hom ((a : C(G, resolutionX X m)) (x 0))) from
        map_sub (nestedLinearEquiv X (m + 1)) _ _,
      ContinuousMap.sub_apply, ih, Fin.sum_univ_succ (n := m + 1)]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [nestedHomeomorph_succ_apply X m a, Fin.succ_succAbove_zero]
    congr 1
    funext j
    simp only [Fin.tail, Fin.succ_succAbove_succ]
