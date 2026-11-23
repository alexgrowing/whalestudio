import Development.EtaleCohomology.EtaleTrace.GenOutChartPfRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace LateralTheory.EtaleTrace.Cov

theorem alg_germ_eq (X : Scheme.{0}) [IsIntegral X] {V : X.Opens} (s : Γ(X, V)) {y w : X} (hy : y ∈ V) (hw : w ∈ V) :
    algebraMap (X.presheaf.stalk w) X.functionField (X.presheaf.germ V w hw s) =
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ V y hy s) := by
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField]

theorem sect_exists (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (z : X.functionField)
    (hz : ∀ y ∈ U, z ∈ loc X y) : ∃ s : Γ(X, U), ∀ (y : X) (hy : y ∈ U),
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy s) = z := by
  have key : ∀ y : U, ∃ (V : X.Opens) (hV : y.1 ∈ V) (s : Γ(X, V)),
      algebraMap (X.presheaf.stalk y.1) X.functionField (X.presheaf.germ V y.1 hV s) = z := by
    intro y
    obtain ⟨a, ha⟩ := hz y.1 y.2
    obtain ⟨V, hyV, s, hs⟩ := X.presheaf.exists_germ_eq (x := y.1) a
    exact ⟨V, hyV, s, by rw [hs, ha]⟩
  choose V hV s hs using key
  let W : U → X.Opens := fun y => V y ⊓ U
  let sf : ∀ y : U, Γ(X, W y) := fun y => X.presheaf.map (homOfLE inf_le_left : W y ⟶ V y).op (s y)
  have hsf : ∀ (y : U) (w : X) (hw : w ∈ W y),
      algebraMap (X.presheaf.stalk w) X.functionField (X.presheaf.germ (W y) w hw (sf y)) = z := by
    intro y w hw
    simp only [sf, TopCat.Presheaf.germ_res_apply]
    rw [alg_germ_eq X (s y) (hV y) hw.1, hs]
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf W sf := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf
    intro w hw
    congr 1
    refine @Scheme.germToFunctionField_injective X _ (W i ⊓ W j) ⟨⟨w, hw⟩⟩ _ _ ?_
    rw [← @Scheme.algebraMap_germ_eq_germToFunctionField X _ (W i ⊓ W j) ⟨⟨w, hw⟩⟩ w hw,
      ← @Scheme.algebraMap_germ_eq_germToFunctionField X _ (W i ⊓ W j) ⟨⟨w, hw⟩⟩ w hw]
    simp only [TopCat.Presheaf.germ_res_apply]
    rw [hsf i w hw.1, hsf j w hw.2]
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W U (fun y => homOfLE inf_le_right)
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hV _, hy⟩) sf hcompat
  refine ⟨t, fun y hy => ?_⟩
  have h1 := hsf ⟨y, hy⟩ y (show y ∈ W ⟨y, hy⟩ from ⟨hV _, hy⟩)
  rw [← ht ⟨y, hy⟩] at h1
  change algebraMap _ _ (X.presheaf.germ (W ⟨y, hy⟩) y _
    (X.presheaf.map (homOfLE inf_le_right : W ⟨y, hy⟩ ⟶ U).op t)) = z at h1
  erw [TopCat.Presheaf.germ_res_apply] at h1
  exact h1

theorem sect_ext (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (s t : Γ(X, U))
    (h : ∀ (y : X) (hy : y ∈ U), algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy s) =
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy t)) : s = t := by
  apply TopCat.Presheaf.section_ext X.sheaf
  intro y hy
  have : s = t := by
    refine @Scheme.germToFunctionField_injective X _ U ⟨⟨y, hy⟩⟩ _ _ ?_
    rw [← @Scheme.algebraMap_germ_eq_germToFunctionField X _ U ⟨⟨y, hy⟩⟩ y hy,
      ← @Scheme.algebraMap_germ_eq_germToFunctionField X _ U ⟨⟨y, hy⟩⟩ y hy]
    exact h y hy
  rw [this]

theorem SectOfLoc_pf : SectOfLoc := by
  intro X _ U R hR
  have hex : ∀ z : R, ∃ s : Γ(X, U), ∀ (y : X) (hy : y ∈ U),
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy s) = z :=
    fun z => sect_exists X U z (hR z z.2)
  choose σ hσ using hex
  refine ⟨{ toFun := σ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hσ⟩
  · exact sect_ext X U _ _ fun y hy => by simp [hσ]
  · intro a b; exact sect_ext X U _ _ fun y hy => by simp [hσ]
  · exact sect_ext X U _ _ fun y hy => by simp [hσ]
  · intro a b; exact sect_ext X U _ _ fun y hy => by simp [hσ]

theorem GenOutChart_of_gen (h : ChartGen) : GenOutChart := GenOutChart_of_sect SectOfLoc_pf h

end LateralTheory.EtaleTrace.Cov
