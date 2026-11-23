import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory

theorem exists_multilinear_of_commuting_endAlgHom :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)]
      [∀ v, Module ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V]
      (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v)
      (ℓ : ∀ v, Module.Dual ℂ (Wv v)) (y : V),
      (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) →
      (∀ v, Φ v ((ℓ v).smulRight (w v)) y = y) →
      ∃ F : MultilinearMap ℂ Wv V, F w = y ∧
        ∀ v (A : Module.End ℂ (Wv v)) (x : ∀ u, Wv u),
          Φ v A (F x) = F (Function.update x v (A (x v))) := by
  intro ι _ hd Wv _ _ V _ _ Φ w ℓ y hc hfix
  let f : (∀ v, Wv v) → ι → Module.End ℂ V := fun x v => Φ v ((ℓ v).smulRight (x v))
  have comm : ∀ x, ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Commute (f x)) :=
    fun x a _ b _ hab => hc a b hab _ _
  let G : (∀ v, Wv v) → V := fun x => (Finset.univ.noncommProd (f x) (comm x)) y

  let R : (∀ v, Wv v) → ι → Module.End ℂ V := fun x v =>
    (Finset.univ.erase v).noncommProd (f x)
      (fun _ ha _ hb hab => comm x (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab)
  have hsplit : ∀ x v, G x = f x v (R x v y) := by
    intro x v
    simp only [G, R]
    rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ v) (f x) (comm x)]
    rfl
  have hR : ∀ x v (a : Wv v), R (Function.update x v a) v = R x v := by
    intro x v a
    simp only [R]
    apply Finset.noncommProd_congr rfl
    intro u hu
    simp only [f, Function.update_of_ne (Finset.ne_of_mem_erase hu)]
  have hfu : ∀ x v (a : Wv v), f (Function.update x v a) v = Φ v ((ℓ v).smulRight a) := by
    intro x v a
    simp only [f, Function.update_self]
  refine ⟨{ toFun := G, map_update_add' := ?_, map_update_smul' := ?_ }, ?_, ?_⟩
  · intro dec x v a b
    obtain rfl : dec = hd := Subsingleton.elim _ _
    have e : (ℓ v).smulRight (a + b) = (ℓ v).smulRight a + (ℓ v).smulRight b := by
      ext z; simp [smul_add]
    rw [hsplit _ v, hsplit _ v, hsplit _ v, hR, hR, hR, hfu, hfu, hfu, e, map_add,
      LinearMap.add_apply]
  · intro dec x v c a
    obtain rfl : dec = hd := Subsingleton.elim _ _
    have e : (ℓ v).smulRight (c • a) = c • (ℓ v).smulRight a := by
      ext z; simp [smul_comm c]
    rw [hsplit _ v, hsplit _ v, hR, hR, hfu, hfu, e, map_smul, LinearMap.smul_apply]
  · show (Finset.univ.noncommProd (f w) (comm w)) y = y
    exact Finset.noncommProd_induction _ _ _ (fun T : Module.End ℂ V => T y = y)
      (fun S T hS hT => by rw [Module.End.mul_apply, hT, hS]) rfl
      (fun v _ => hfix v)
  · intro v A x
    show Φ v A (G x) = G (Function.update x v (A (x v)))
    rw [hsplit x v, hsplit _ v, hR, hfu]
    have : (ℓ v).smulRight (A (x v)) = A * (ℓ v).smulRight (x v) := by
      ext z; simp
    rw [this, map_mul, Module.End.mul_apply]

end GlobalTheory
