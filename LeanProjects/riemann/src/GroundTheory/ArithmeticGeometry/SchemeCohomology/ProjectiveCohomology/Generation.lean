import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ModulesAbExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

def globalSection (F : X.Modules) (m : Γ(F, ⊤)) : F.sections :=
  PresheafOfModules.sectionsMk (fun U => resF F (le_top : U.unop ≤ ⊤) m) (by
    intro U V f
    change (F.presheaf.map f) ((F.presheaf.map (homOfLE le_top).op) m) =
      (F.presheaf.map (homOfLE le_top).op) m
    rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
    rfl)

private lemma resF_comp (F : X.Modules) {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (m : Γ(F, U)) :
    resF F h₂ (resF F h₁ m) = resF F (h₂.trans h₁) m := by
  change (F.presheaf.map (homOfLE h₂).op) ((F.presheaf.map (homOfLE h₁).op) m) =
    (F.presheaf.map (homOfLE (h₂.trans h₁)).op) m
  rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
  rfl

lemma freeHomEquiv_symm_app_ιFree (F : X.Modules) {κ : Type u} (t : κ → F.sections) (k : κ)
    (W : X.Opens) (a : Γ(X, W)) :
    (F.freeHomEquiv.symm t).val.app (op W) ((SheafOfModules.ιFree k).val.app (op W) a) =
      a • (show Γ(F, W) from (t k).val (op W)) := by
  have h : SheafOfModules.ιFree k ≫ F.freeHomEquiv.symm t = F.unitHomEquiv.symm (t k) := by
    simpa using (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (F.freeHomEquiv.symm t) k).symm
  have h2 : (F.freeHomEquiv.symm t).val.app (op W) ((SheafOfModules.ιFree k).val.app (op W) a) =
      (SheafOfModules.ιFree k ≫ F.freeHomEquiv.symm t).val.app (op W) a := rfl
  rw [h2, h]
  rfl

theorem exists_generatingSections (F : X.Modules) [F.IsQuasicoherent] {ι : Type u}
    (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    {κ : Type u} [Finite κ] (s : κ → Γ(F, ⊤))
    (hs : ∀ i, Submodule.span Γ(X, V i) (Set.range fun k => resF F (le_top : V i ≤ ⊤) (s k)) = ⊤) :
    ∃ σ : F.GeneratingSections, σ.IsFiniteType := by
  classical
  have := Fintype.ofFinite κ
  let t : κ → F.sections := fun k => globalSection F (s k)
  let π := F.freeHomEquiv.symm t
  have hsurj : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf X.ringCatSheaf).map π) := by
    constructor
    intro U m
    rw [Opens.mem_grothendieckTopology]
    intro x hxU
    have hx : x ∈ iSup V := by rw [hcov]; trivial
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.1 hx
    obtain ⟨f, hfle, hxf⟩ := (hV i).exists_basicOpen_le (V := U ⊓ V i) ⟨x, ⟨hxU, hxi⟩⟩ hxi
    have hDU : X.basicOpen f ≤ U := hfle.trans inf_le_left
    refine ⟨X.basicOpen f, homOfLE hDU, ?_, hxf⟩
    obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq F (hV i) f (resF F hDU m)
    have hm'span : m' ∈ Submodule.span Γ(X, V i)
        (Set.range fun k => resF F (le_top : V i ≤ ⊤) (s k)) := by
      rw [hs i]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm'span
    obtain ⟨w, hw⟩ : IsUnit (resO (X.basicOpen_le f) f ^ e) :=
      (X.toRingedSpace.isUnit_res_basicOpen f).pow e
    let a : κ → Γ(X, X.basicOpen f) := fun k =>
      ((w⁻¹ : (Γ(X, X.basicOpen f))ˣ) : Γ(X, X.basicOpen f)) * resO (X.basicOpen_le f) (c k)
    have h₁ : resF F (X.basicOpen_le f) m' =
        ∑ k, resO (X.basicOpen_le f) (c k) • resF F (le_top : X.basicOpen f ≤ ⊤) (s k) := by
      rw [← hc, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [resF_smul, resF_comp]
    have h₂ : ((w : Γ(X, X.basicOpen f))) • resF F hDU m =
        ∑ k, resO (X.basicOpen_le f) (c k) • resF F (le_top : X.basicOpen f ≤ ⊤) (s k) := by
      rw [← h₁, hm', hw]
    have key : resF F hDU m = ∑ k, a k • resF F (le_top : X.basicOpen f ≤ ⊤) (s k) := by
      have : resF F hDU m = ((w⁻¹ : (Γ(X, X.basicOpen f))ˣ) : Γ(X, X.basicOpen f)) •
          ((w : Γ(X, X.basicOpen f)) • resF F hDU m) := by
        rw [← mul_smul, Units.inv_mul, one_smul]
      rw [this, h₂, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_smul]
    have hsum : (π.val.app (op (X.basicOpen f)))
        (∑ k, (SheafOfModules.ιFree k).val.app (op (X.basicOpen f)) (a k)) =
          ∑ k, a k • resF F (le_top : X.basicOpen f ≤ ⊤) (s k) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [freeHomEquiv_symm_app_ιFree]
      rfl
    exact ⟨∑ k, (SheafOfModules.ιFree k).val.app (op (X.basicOpen f)) (a k), hsum.trans key.symm⟩
  have hπ : Epi π := ⟨fun g h hgh => (SheafOfModules.toSheaf X.ringCatSheaf).map_injective (by
    rw [← cancel_epi ((SheafOfModules.toSheaf X.ringCatSheaf).map π)]
    have := congrArg (SheafOfModules.toSheaf X.ringCatSheaf).map hgh
    exact ((SheafOfModules.toSheaf X.ringCatSheaf).map_comp π g).symm.trans
      (this.trans ((SheafOfModules.toSheaf X.ringCatSheaf).map_comp π h)))⟩
  exact ⟨{ I := κ, s := t, epi := hπ }, ⟨inferInstance⟩⟩

theorem exists_generatingSections_of_iso {F G : X.Modules} (e : F ≅ G)
    (h : ∃ σ : F.GeneratingSections, σ.IsFiniteType) :
    ∃ σ : G.GeneratingSections, σ.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := h
  have he : Epi e.hom := inferInstance
  exact ⟨@SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ F G σ e.hom he,
    @SheafOfModules.GeneratingSections.instIsFiniteTypeOfEpi _ _ _ _ _ _ F G σ e.hom he hσ⟩

end

end GroundTheory.Arith.SchemeCoh
