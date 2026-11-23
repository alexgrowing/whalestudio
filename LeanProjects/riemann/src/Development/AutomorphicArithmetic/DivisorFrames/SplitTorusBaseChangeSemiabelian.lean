import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusHomPullbackLocalTrivial
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

theorem UpperTheory.split_torus_base_change_semiabelian :
    ∀ (O : Type) [CommRing O] (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
        (G : Over (Sp K)) [GrpObj G], IsSemiAbelian G → ∀ (i : OAct O G) (G' : Over (Sp Ω)) [GrpObj G'] (i' : OAct O G')
        (φ : G'.left ⟶ G.left), IsActPull i' i (spMap (algebraMap K Ω)) φ →
        ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u' : splitTorus (Sp Ω) X ⟶ G') (A : Over (Sp Ω)) [GrpObj A] (q' : G' ⟶ A) (j : OAct O A),
        IsAbelianScheme A → IsMonHom u' → IsKer u' q' → (∀ a, i'.act a ≫ q' = q' ≫ j.act a) →
        ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
          ∃ (G₀ : Over (Sp F)) (_ : GrpObj G₀) (i₀ : OAct O G₀) (φ₀ : G₀.left ⟶ G.left)
            (Y : Type) (_ : AddCommGroup Y) (_ : Module.Free ℤ Y) (_ : Module.Finite ℤ Y) (u₀ : splitTorus (Sp F) Y ⟶ G₀)
            (B : Over (Sp F)) (_ : GrpObj B) (q₀ : G₀ ⟶ B) (j₀ : OAct O B) (ψ : A.left ⟶ B.left),
            IsActPull i₀ i (spMap (algebraMap K F)) φ₀ ∧ IsAbelianScheme B ∧ IsMonHom u₀ ∧ IsKer u₀ q₀ ∧
            (∀ a, i₀.act a ≫ q₀ = q₀ ≫ j₀.act a) ∧ IsActPull j j₀ (spMap (algebraMap F Ω)) ψ := by
  intro O _ K Ω _ _ _ _ G _ hG i G' _ i' φ hφ X _ _ _ u' A _ q' j hA hu' hK hj
  have := hG.comm
  have := hG.smooth
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hφ.1 (isGrpPullback_pullback G (spMap (algebraMap K Ω)))
  obtain ⟨k₁, k₂, k₃, k₄, k₅⟩ := id hK
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  obtain ⟨F, hF, ⟨T⟩⟩ := exists_finite_torusExtension K Ω G inferInstance hG.quasiCompact hG.separated
    ⟨{ X := X, B := A, isAbelian := hA, q := e.inv ≫ q', q_hom := inferInstance,
       q_flat := by rw [Over.comp_left]; infer_instance,
       q_surjective := by rw [Over.comp_left]; infer_instance,
       q_quasiCompact := by rw [Over.comp_left]; infer_instance,
       i := u' ≫ e.hom, i_hom := inferInstance,
       isKernel := k₅.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp) }⟩
  let _ := T.addCommGroup
  let _ := T.free
  let _ := T.finite
  let _ := T.grpB
  have := T.i_hom
  have := T.q_hom
  have hT : IsKer T.i T.q := isKer_torusExtension T
  have hact := exists_isActPull (spMap (algebraMap K F)) i
  have := (OAct.pullback (spMap (algebraMap K F)) G i).hom
  obtain ⟨j₀, hj₀⟩ := hT.exists_oAct (OAct.pullback (spMap (algebraMap K F)) G i) fun a =>
    (splitTorus_hom_abelian_eq_one _ T.X _ T.isAbelian _ inferInstance).trans Hom.one_def
  have hc : spMap (algebraMap F Ω) ≫ spMap (algebraMap K F) = spMap (algebraMap K Ω) :=
    FieldModel.spMap_comp rfl
  obtain ⟨g₁, eg₁, Hg₁⟩ := FieldModel.exists_baseChange hc hφ.1.1
  have gp : IsGrpPullback G' ((Over.pullback (spMap (algebraMap K F))).obj G) (spMap (algebraMap F Ω)) g₁ :=
    hact.1.cancel (hφ.1.congr hc.symm eg₁.symm) Hg₁.w
  obtain ⟨u₁, hu₁, -⟩ := existsUnique_torusCompat Hg₁ T.i
  have := hu₁.isMonHom gp
  have gB := isGrpPullback_pullback T.B (spMap (algebraMap F Ω))
  obtain ⟨q₁, ⟨l₁, l₂, l₃, l₄, l₅⟩, hq₁⟩ := hT.baseChange gp gB hu₁
  have hB : IsAbelianScheme ((Over.pullback (spMap (algebraMap F Ω))).obj T.B) :=
    { comm := by have := T.isAbelian.comm; infer_instance
      smooth := by have := T.isAbelian.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := T.isAbelian.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := T.isAbelian.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  obtain ⟨β, hβ, hqβ⟩ := flatQuotient_iso_of_same_kernel _ G' _ A _ _ q₁ u₁ q' u' l₁ inferInstance l₂ l₃ l₄ l₅
    k₁ hu' k₂ k₃ k₄ k₅
    ((splitTorus_hom_abelian_eq_one _ X _ hB _ inferInstance).trans Hom.one_def)
    ((splitTorus_hom_abelian_eq_one _ T.X _ hA _ inferInstance).trans Hom.one_def)
  refine ⟨F, hF, _, inferInstance, _, _, T.X, inferInstance, inferInstance, inferInstance, T.i, T.B, inferInstance,
    T.q, j₀, β.hom.left ≫ pullback.fst T.B.hom (spMap (algebraMap F Ω)), hact, T.isAbelian, T.i_hom, hT, hj₀,
    ((isGrpPullback_of_iso β).comp gB).congr (Category.id_comp _) rfl, fun a => ?_⟩
  have : Epi q'.left := Flat.epi_of_flat_of_surjective _
  have h₁ : q'.left ≫ β.hom.left ≫ pullback.fst T.B.hom (spMap (algebraMap F Ω)) = g₁ ≫ T.q.left := by
    rw [← Category.assoc, ← Over.comp_left, hqβ]
    exact hq₁.w.symm
  have h₂ : (i'.act a).left ≫ g₁ = g₁ ≫ ((OAct.pullback (spMap (algebraMap K F)) G i).act a).left := by
    refine hact.1.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hact.2, eg₁, hφ.2, ← Category.assoc, eg₁]
    · rw [Category.assoc, Category.assoc, Over.w, Hg₁.w, ← Category.assoc, Over.w]
  rw [← cancel_epi q'.left, ← Category.assoc, ← Over.comp_left, ← hj, Over.comp_left, Category.assoc, h₁,
    ← Category.assoc q'.left, h₁, ← Category.assoc, h₂, Category.assoc, Category.assoc, ← Over.comp_left, hj₀,
    Over.comp_left]
