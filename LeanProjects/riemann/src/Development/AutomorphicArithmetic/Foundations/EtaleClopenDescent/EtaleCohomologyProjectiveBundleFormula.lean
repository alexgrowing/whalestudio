import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankOneOfHomotopyInvarian
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankTwo
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaSuccOfForall

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Pbf

private theorem functor_to_single_object_const {G : Type} [Monoid G] {n : ℕ} (y : Fin 1 ⥤ SingleObj G) (θ : Fin (n + 1) ⥤ Fin 1) :
    θ ⋙ y = (Functor.const _).obj (SingleObj.star G) := by
  have key : ∀ (a b : Fin 1) (g : a ⟶ b), y.map g = 𝟙 _ := by
    intro a b g
    obtain rfl : a = b := Subsingleton.elim _ _
    rw [Subsingleton.elim g (𝟙 a), y.map_id]
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  simp only [Functor.comp_map, Functor.const_obj_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact key _ _ _

private theorem eq_triv (U : Scheme.{0}) {N : ℕ} (V : sch.obj U ⟶ ofCat (glCat N)) : V = triv (sch.obj U) N := by
  ext k T x
  let f : (Opposite.op (SimplexCategory.mk 0)) ⟶ k := (SimplexCategory.isTerminalZero.from k.unop).op
  have h := congrArg (fun φ => (ConcreteCategory.hom (NatTrans.app φ T)).toFun x) (V.naturality f)
  refine h.trans ?_
  exact functor_to_single_object_const _ _

private theorem pbf_all (q : ℕ) [NeZero q] (N : ℕ) : ∀ E : Spc, Inv q E → PBF q E N := by
  induction N with
  | zero => exact fun E _ => UpperTheory.projectiveBundleFormula_rank_zero q E
  | succ N ih =>
    rcases N with _ | _ | N
    · exact UpperTheory.projectiveBundleFormula_rank_one_of_homotopyInvariant q
    · exact UpperTheory.projectiveBundleFormula_rank_two q
    · exact UpperTheory.projectiveBundleFormula_succ_of_forall q (N + 2) (by omega) ih

end UpperTheory.Pbf

theorem UpperTheory.Cb.etaleCohomology_projectiveBundle_formula :
    ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), ∀ {N : ℕ} (V : sch.obj U ⟶ ofCat (glCat N)), Inv q (sch.obj U) → ∀ n i : ℤ, Function.Bijective fun a : ∀ j : Fin N, Ht q (sch.obj U) (n - 2 * (j : ℕ)) (i - (j : ℕ)) => ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j)) (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i) := by
  intro q _ U N V h n i
  obtain rfl := UpperTheory.Pbf.eq_triv U V
  exact UpperTheory.Pbf.pbf_all q N _ h n i
