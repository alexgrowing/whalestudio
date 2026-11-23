import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsFreeSheafBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

namespace FreeSheafBasis

section Coproduct

variable {C : Type*} [Category C] [Preadditive C] (A : C) (n : ℕ)
  [HasCoproduct (fun _ : ULift.{u} (Fin n) => A)]

def projC (j : Fin n) : ∐ (fun _ : ULift.{u} (Fin n) => A) ⟶ A :=
  Sigma.desc (fun i : ULift.{u} (Fin n) => if i.down = j then 𝟙 A else 0)

lemma ι_projC (i j : Fin n) :
    Sigma.ι (fun _ : ULift.{u} (Fin n) => A) (ULift.up i) ≫ projC A n j =
      if i = j then 𝟙 A else 0 :=
  Sigma.ι_desc _ _

lemma sum_projC_ι :
    ∑ j : Fin n, projC A n j ≫ Sigma.ι (fun _ : ULift.{u} (Fin n) => A) (ULift.up j) = 𝟙 _ := by
  refine Sigma.hom_ext _ _ (fun ⟨i⟩ => ?_)
  simp only [Preadditive.comp_sum, ← Category.assoc, ι_projC, Category.comp_id]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

end Coproduct

variable (Y : Scheme.{u}) (n : ℕ)

def incl (i : Fin n) : structureModule Y ⟶ freeModule Y n :=
  SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i)

def proj (j : Fin n) : freeModule Y n ⟶ structureModule Y :=
  projC (C := SheafOfModules.{u} Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) n j

lemma incl_proj (i j : Fin n) :
    incl Y n i ≫ proj Y n j = if i = j then 𝟙 (structureModule Y) else 0 :=
  ι_projC (C := SheafOfModules.{u} Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) n i j

lemma sum_proj_incl : ∑ j, proj Y n j ≫ incl Y n j = 𝟙 (freeModule Y n) :=
  sum_projC_ι (C := SheafOfModules.{u} Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) n

variable {Y} in

def evalHom {M N : Y.Modules} (V : Y.Opens) (x : Γ(M, V)) : (M ⟶ N) →+ Γ(N, V) where
  toFun φ := (φ.app V).hom x
  map_zero' := rfl
  map_add' _ _ := rfl

variable {Y} in
lemma evalHom_apply {M N : Y.Modules} (V : Y.Opens) (x : Γ(M, V)) (φ : M ⟶ N) :
    evalHom V x φ = (φ.app V).hom x := rfl

variable {Y n}

lemma incl_proj_app (V : Y.Opens) (i j : Fin n) (r : Γ(Y, V)) :
    ((proj Y n j).app V).hom (((incl Y n i).app V).hom r) = if i = j then r else 0 := by
  have := congrArg (fun φ => evalHom (M := structureModule Y) (N := structureModule Y) V
    (show Γ(structureModule Y, V) from r) φ) (incl_proj Y n i j)
  split_ifs at this ⊢ with hij <;> exact this

lemma sum_incl_proj_app (V : Y.Opens) (m : Γ(freeModule Y n, V)) :
    ∑ j, ((incl Y n j).app V).hom (((proj Y n j).app V).hom m) = m := by
  have := congrArg (fun φ => evalHom V m φ) (sum_proj_incl Y n)
  simp only [map_sum, evalHom_apply] at this
  exact this

end FreeSheafBasis

open FreeSheafBasis in

theorem FreeSheafBasis.proof : FreeSheafBasis.Statement.{u} := by
  intro Y n V h
  have h1 : ((structureModule Y).presheaf.map (homOfLE h).op).hom (1 : Γ(Y, ⊤)) = (1 : Γ(Y, V)) := by
    change (Y.presheaf.map (homOfLE h).op).hom 1 = 1
    exact map_one _
  have hres : ∀ i (r : Γ(Y, V)), r • ((freeModule Y n).presheaf.map (homOfLE h).op).hom
      (stdSection Y n i) = ((incl Y n i).app V).hom r := by
    intro i r
    have e := app_map_apply (incl Y n i) h (show Γ(structureModule Y, ⊤) from (1 : Γ(Y, ⊤)))
    have h1' : ((structureModule Y).presheaf.map (homOfLE h).op).hom
        (show Γ(structureModule Y, ⊤) from (1 : Γ(Y, ⊤))) =
        (show Γ(structureModule Y, V) from (1 : Γ(Y, V))) := h1
    rw [h1'] at e
    have e2 := Scheme.Modules.Hom.app_smul (incl Y n i) r
      (show Γ(structureModule Y, V) from (1 : Γ(Y, V)))
    have hr : r • (show Γ(structureModule Y, V) from (1 : Γ(Y, V))) =
        (show Γ(structureModule Y, V) from r) := mul_one r
    change r • ((freeModule Y n).presheaf.map (homOfLE h).op).hom
      (((incl Y n i).app ⊤).hom (show Γ(structureModule Y, ⊤) from (1 : Γ(Y, ⊤)))) = _
    rw [← e]
    exact e2.symm.trans (congrArg (fun x => (incl Y n i).app V x) hr)
  simp only [hres]
  refine Function.bijective_iff_has_inverse.mpr ⟨fun m j => ((proj Y n j).app V).hom m, ?_, ?_⟩
  · intro r
    funext j
    simp only [map_sum, incl_proj_app]
    change (∑ x, if x = j then r x else 0 : Γ(Y, V)) = r j
    simp
  · intro m
    exact sum_incl_proj_app V m

end

end GroundTheory.Heights₂.Heights.Model
