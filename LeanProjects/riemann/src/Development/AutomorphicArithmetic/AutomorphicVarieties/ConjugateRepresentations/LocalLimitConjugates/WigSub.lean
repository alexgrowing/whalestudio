import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.WigHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.WigAlpha
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

namespace UpperTheory.V.Cj.H.WignerSubquotient

private theorem mapQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private theorem relQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (S : Subalgebra ℂ (A × B)) {n : ℕ}
    (X : Fin n → Fin n → A) (Y : Fin n → Fin n → B) (h : ∀ p q, (X p q, Y p q) ∈ S) (v : ℂ) :
    (Formalism.REAL.qdet X v, Formalism.REAL.qdet Y v) ∈ S := by
  let Z : Fin n → Fin n → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have e1 : ((Formalism.REAL.qdet Z v : S) : A × B).1 = Formalism.REAL.qdet X v := mapQ ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have e2 : ((Formalism.REAL.qdet Z v : S) : A × B).2 = Formalism.REAL.qdet Y v := mapQ ((AlgHom.snd ℂ _ _).comp S.val) Z v
  rw [← e1, ← e2]
  exact (Formalism.REAL.qdet Z v).2

section

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

private theorem intQ {k : ℕ} (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q m, R (X p q m) = Y p q (R m)) (v : ℂ) (m : M) :
    R (Formalism.REAL.qdet X v m) = Formalism.REAL.qdet Y v (R m) := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | ∀ m, R (z.1 m) = z.2 (R m)}
      mul_mem' := fun {x y} hx hy m => (hx _).trans (congrArg x.2 (hy m))
      add_mem' := fun {x y} hx hy m => (map_add R _ _).trans (congrArg₂ (· + ·) (hx m) (hy m))
      algebraMap_mem' := fun c m => map_smul R c m }
  exact relQ S X Y h v m

private theorem intQop {k : ℕ} (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q m, R (X p q m) = Y p q (R m)) (v : ℂ) (m : M) :
    R ((Formalism.REAL.qdet (fun i j => -MulOpposite.op (X i j)) v).unop m) =
      (Formalism.REAL.qdet (fun i j => -MulOpposite.op (Y i j)) v).unop (R m) := by
  let S : Subalgebra ℂ ((Module.End ℂ M)ᵐᵒᵖ × (Module.End ℂ M')ᵐᵒᵖ) :=
    { carrier := {z | ∀ m, R (z.1.unop m) = z.2.unop (R m)}
      mul_mem' := fun {x y} hx hy m => (hy _).trans (congrArg y.2.unop (hx m))
      add_mem' := fun {x y} hx hy m => (map_add R _ _).trans (congrArg₂ (· + ·) (hx m) (hy m))
      algebraMap_mem' := fun c m => map_smul R c m }
  exact relQ S (fun i j => -MulOpposite.op (X i j)) (fun i j => -MulOpposite.op (Y i j))
    (fun p q m => (map_neg R _).trans (congrArg Neg.neg (h p q m))) v m

end

variable {E : Type} [Field E] {a : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

private noncomputable def res (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (N : Submodule ℂ M) (h : ∀ X, ∀ m ∈ N, L X m ∈ N) :
    Lie E a →ₗ[ℝ] Module.End ℂ N where
  toFun X := (L X).restrict (h X)
  map_add' X Y := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_add L X Y) m.1)
  map_smul' c X := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_smul L c X) m.1)

private theorem res_hom {L : Lie E a →ₗ[ℝ] Module.End ℂ M} (hL : IsLieHom L) (N : Submodule ℂ M)
    (h : ∀ X, ∀ m ∈ N, L X m ∈ N) : IsLieHom (res L N h) :=
  fun X Y => LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hL X Y) m.1)

private theorem res_dCo {L : Lie E a →ₗ[ℝ] Module.End ℂ M} {N : Submodule ℂ M} {L' : Lie E a →ₗ[ℝ] Module.End ℂ N}
    (h : ∀ X m, (L' X m : M) = L X m) {q : ℕ} (ω' : Herm E a [⋀^Fin q]→ₗ[ℝ] N) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M)
    (hω : ∀ Y, (ω' Y : M) = ω Y) (Y : Fin (q + 1) → Herm E a) : (dCo L' ω' Y : M) = dCo L ω Y := by
  rw [dCo_apply, dCo_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hω, ← h]
  exact map_zsmul N.subtype _ _

end UpperTheory.V.Cj.H.WignerSubquotient

open UpperTheory.V.Cj.H.WignerSubquotient in
theorem UpperTheory.V.Cj.H.wigSub :
    UpperTheory.V.Cj.H.WigSub := by
  intro E _ _ _ a M _ _ _ _ LA LB hA hB hAB N sA sB τ x z hz
  subst hz
  refine ⟨?_, fun q ω h1 h2 hN => ?_⟩
  · obtain ⟨α, p1, p2⟩ := wigAlpha E a M LA LB hA hB hAB τ x
    exact (wigHom E a M (LA + LB) α _ p1 p2).1
  · obtain ⟨α, p1, p2⟩ := wigAlpha E a N (res LA N sA) (res LB N sB) (res_hom hA N sA) (res_hom hB N sB)
      (fun X Y => LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hAB X Y) m.1)) τ x
    let ω' : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] N :=
      { toFun := fun Y => ⟨ω Y, hN Y⟩
        map_update_add' := fun Y i u v => Subtype.ext (ω.map_update_add Y i u v)
        map_update_smul' := fun Y i c u => Subtype.ext (ω.map_update_smul Y i c u)
        map_eq_zero_of_eq' := fun Y i j e hij => Subtype.ext (ω.map_eq_zero_of_eq Y e hij) }
    have hL : ∀ X (m : N), ((res LA N sA + res LB N sB) X m : M) = (LA + LB) X m := fun _ _ => rfl
    obtain ⟨η, hη⟩ := (wigHom E a N (res LA N sA + res LB N sB) α _ p1 p2).2 q ω'
      (fun Z hZ Y => Subtype.ext ((h1 Z hZ Y).trans
        (Submodule.coe_sum N (fun i => ω' (Function.update Y i (brH Z hZ (Y i)))) Finset.univ).symm))
      (AlternatingMap.ext fun Y => Subtype.ext ((res_dCo hL ω' ω (fun _ => rfl) Y).trans (by rw [h2]; rfl)))
    refine ⟨(N.subtype.restrictScalars ℝ).compAlternatingMap η, fun Y => (η Y).2, fun Y => ?_⟩
    rw [← res_dCo hL η _ (fun _ => rfl) Y, hη, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub]
    exact congrArg₂ (· - ·) (intQ N.subtype _ (eL LA τ) (fun _ _ _ => rfl) x (ω' Y))
      (intQop N.subtype _ (eL LB τ) (fun _ _ _ => rfl) x (ω' Y))
