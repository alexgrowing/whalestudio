import Mathlib

namespace Bl.ThirdBlockLemmaB

noncomputable def goal1 :
  {S : Type} →   [inst : CommRing S] →     {A A' : Type} →       [inst_1 : CommRing A] →         [inst_2 : Algebra S A] →           [inst_3 : CommRing A'] → [inst_4 : Algebra S A'] → AlgHom S A A' → AlgHom S (DualNumber A) (DualNumber A') :=
  fun {S} _ {A A'} _ _ _ _ φ =>
    TrivSqZeroExt.lift ((TrivSqZeroExt.inlAlgHom S A' A').comp φ)
      (((TrivSqZeroExt.inrHom A' A').restrictScalars S).comp φ.toLinearMap)
      (fun x y => by
        simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, TrivSqZeroExt.inrHom_apply, AlgHom.coe_comp, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.inr_mul_inr])
      (fun r x => by
        simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, TrivSqZeroExt.inrHom_apply, AlgHom.coe_comp, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.inl_mul_inr, smul_eq_mul, map_mul])
      (fun r x => by
        simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, TrivSqZeroExt.inrHom_apply, AlgHom.coe_comp, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.inr_mul_inl, op_smul_eq_mul, map_mul])

end Bl.ThirdBlockLemmaB
