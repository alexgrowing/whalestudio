import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN

theorem actHK_holds {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B)
    (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd)) : ActHK B hs hd hL hAct := by
  intro i v k hg z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c m =>
    rw [LinearMap.baseChange_tmul]
    have hs1 := ((hAct i).choose_spec.2 v k hg m)
    have e : ∀ m' : MtSub B (partCompl_of hs hd) i, PsiC B (partCompl_of hs hd) hL i (c ⊗ₜ m') = c • ((m' : partOf B i) : B.V (jOf B i) (wOf B i)) := by
      intro m'
      haveI := hL i
      simp only [PsiC, mtEquiv, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype]
      rw [IsBaseChange.equiv_tmul]
      rfl
    rw [e, e, map_smul]
    congr 1

end GlobalTheory.HeckeLocN
