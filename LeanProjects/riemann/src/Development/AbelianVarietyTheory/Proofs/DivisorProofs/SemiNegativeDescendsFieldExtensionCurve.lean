import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackMapOfFlatStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiNegFieldChange

theorem semiNeg_descends_baseChange : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
    ∀ (k' : Type) [Field k'] [Algebra k k'], ∃ (C' : Scheme.{0}) (_ : Algebra k' Γ(C', ⊤)) (π : C' ⟶ C), IsCurve k' C' ∧
      ∀ F : C.Modules, SemiNeg k' ((Scheme.Modules.pullback π).obj F) → SemiNeg k F := by
  intro k _ C _ hC k' _ _
  obtain ⟨h1, h2, h3⟩ := hC
  let t : Sp k' ⟶ Sp k := spMap (algebraMap k k')
  let f := strHom k C
  letI A' : Algebra k' Γ(pullback f t, ⊤) := algebraΓOfHom (pullback.snd f t)
  have hs : strHom k' (pullback f t) = pullback.snd f t := strHom_eq fun _ => rfl
  refine ⟨pullback f t, A', pullback.fst f t, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hs]; exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback (IsPullback.of_hasPullback f t) h1
  · rw [hs]; exact GlobalTheory.ProjSpace.isProjOver_pullback_snd _ h2
  · rw [hs]; haveI := h3; infer_instance
  · intro F hF W r hW i hi
    have : IsProper f := by
      obtain ⟨N, j, hj, e⟩ := h2
      have := isProper_str k N
      change IsProper (strHom k C)
      rw [← e]
      infer_instance
    have hinst : (‹Algebra k Γ(C, ⊤)›) = algebraΓOfHom f :=
      Algebra.algebra_ext _ _ (algebraMap_eq_strHom k C)
    haveI : Flat (pullback.fst f t) := inferInstance
    have hm := GlobalTheory.T.mono_pullback_map_of_flat' _ _ (pullback.fst f t) W F i
    have h := hF _ r (hW.pullback _) _ hm
    rw [← interNum_congr_lbIso k' _ (isLB_vecOne (LB.isLB_pull hW.isLB_det _)) (isLB_vecOne (hW.pullback _).isLB_det)
      (fun j => by fin_cases j; exact hW.lbIso_det_pullback _)] at h
    have P := FieldChangeInter.interNum_pull (f := f) (f' := pullback.snd f t) (π := pullback.fst f t)
      (IsPullback.of_hasPullback f t) (L := ![det W r]) (isLB_vecOne hW.isLB_det)
    have e₃ : (fun j => ((![det W r] : Fin 1 → LB C) j).pull (pullback.fst f t)) = ![(det W r).pull (pullback.fst f t)] :=
      funext fun j => by fin_cases j; rfl
    rw [e₃] at P
    rw [hinst]
    exact P ▸ h

end GlobalTheory.SemiNegFieldChange
