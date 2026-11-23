import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianTorusAfterSeparable
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusActionWeightedCharts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalCoverResiduePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackClosedImmersionGenericFibreStatement

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.TorusSpread.torusExtension_of_iso {K : Type} [Field K] {G₁ G₂ : Over (Sp K)} [GrpObj G₁] [GrpObj G₂]
    (e : G₁ ≅ G₂) [IsMonHom e.hom] (T : TorusExtension G₁) :
    ∃ T' : TorusExtension G₂, @Module.finrank ℤ T'.X _ T'.addCommGroup.toAddCommMonoid _ =
      @Module.finrank ℤ T.X _ T.addCommGroup.toAddCommMonoid _ := by
  letI := T.addCommGroup; letI := T.grpB
  haveI := T.free; haveI := T.finite; haveI := T.q_hom; haveI := T.i_hom
  haveI : IsIso e.inv.left := ⟨⟨e.hom.left, by rw [← Over.comp_left, e.inv_hom_id, Over.id_left],
    by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]⟩⟩
  have h1 : Flat (e.inv ≫ T.q).left := by have := T.q_flat; rw [Over.comp_left]; infer_instance
  have h2 : Surjective (e.inv ≫ T.q).left := by have := T.q_surjective; rw [Over.comp_left]; infer_instance
  have h3 : QuasiCompact (e.inv ≫ T.q).left := by have := T.q_quasiCompact; rw [Over.comp_left]; infer_instance
  have h4 : IsPullback (T.i ≫ e.hom) (toUnit _) (e.inv ≫ T.q) (η : 𝟙_ _ ⟶ T.B) :=
    T.isKernel.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  exact ⟨TorusExtension.mk T.X T.B T.isAbelian (e.inv ≫ T.q) inferInstance h1 h2 h3 (T.i ≫ e.hom) inferInstance h4, rfl⟩

theorem GlobalTheory.TorusSpread.isClosedImmersion_torus {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G]
    (T : TorusExtension G) : IsClosedImmersion T.i.left := by
  letI := T.grpB; letI := T.addCommGroup
  haveI := T.isAbelian.proper
  have hη : IsClosedImmersion (η[T.B] : 𝟙_ _ ⟶ T.B).left :=
    GlobalTheory.isClosedImmersion_of_section_of_isSeparated T.B.hom _ (by simpa using Over.w η[T.B])
  have hpb : IsPullback T.i.left (toUnit _ : splitTorus _ T.X ⟶ 𝟙_ _).left T.q.left (η[T.B] : 𝟙_ _ ⟶ T.B).left :=
    T.isKernel.map (Over.forget _)
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip hη

theorem GlobalTheory.BdFib.exists_splitTorus_hom_normal_cover : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (f : Y ⟶ X), IsProper p → ∀ y₀ : Y, ∃ (W : Scheme.{0}) (_ : IsIntegral W) (π : W ⟶ Y) (r : ℕ) (u : splitTorus W (Fin r → ℤ) ⟶ (Over.pullback (π ≫ f)).obj t.G), IsFinite π ∧ IsLocallyNoetherian W ∧ π (genericPoint W) = y₀ ∧ IsMonHom u ∧ (∀ (k : Type) [Field k] (g : Sp k ⟶ W), g (IsLocalRing.closedPoint k) = genericPoint W → IsClosedImmersion ((Over.pullback g).map u).left) ∧ ∃ (k : Type) (_ : Field k) (g : Sp k ⟶ Y) (T : TorusExtension ((Over.pullback (g ≫ f)).obj t.G)), g (IsLocalRing.closedPoint k) = y₀ ∧ @Module.finrank ℤ T.X _ T.addCommGroup.toAddCommMonoid _ = r := by
  intro hP E _ _ _ H X t F _ _ Y p f hp y₀
  haveI : LocallyOfFiniteType p := inferInstance
  haveI : QuasiCompact p := inferInstance
  let κ := Y.residueField y₀
  let x₀ : Sp κ ⟶ Y := Y.fromSpecResidueField y₀
  let G₀ := (Over.pullback (x₀ ≫ f)).obj t.G
  have hG₀ : IsSemiAbelian G₀ := IsSemiAbelian.pullback _ _ t.semi
  obtain ⟨k', _, _, _, -, ⟨T⟩⟩ := GlobalTheory.exists_finite_separable_torusExtension κ G₀ hG₀
  obtain ⟨W, _, π, j, hπ, _, hWn, hj, hjπ⟩ := GlobalTheory.T.exists_finite_normal_cover_residue_point F Y p y₀ k'
  let s : Sp k' ⟶ Sp κ := spMap (algebraMap κ k')
  let G := (Over.pullback (π ≫ f)).obj t.G
  have hG : IsSemiAbelian G := IsSemiAbelian.pullback _ _ t.semi
  let H' := (Over.pullback s).obj G₀
  have h1 : IsGrpPullback H' t.G (j ≫ π ≫ f) (pullback.fst G₀.hom s ≫ pullback.fst t.G.hom (x₀ ≫ f)) :=
    ((isGrpPullback_pullback G₀ s).comp (isGrpPullback_pullback t.G (x₀ ≫ f))).congr
      (by rw [← Category.assoc j π f, hjπ]; rfl) rfl
  have w₀ : (pullback.fst G₀.hom s ≫ pullback.fst t.G.hom (x₀ ≫ f)) ≫ t.G.hom = (H'.hom ≫ j) ≫ π ≫ f := by
    rw [Category.assoc]; exact h1.1.w.trans (Category.assoc _ _ _).symm
  let a : H'.left ⟶ G.left := pullback.lift _ _ w₀
  have ha : IsGrpPullback H' G j a :=
    (isGrpPullback_pullback t.G (π ≫ f)).cancel (h1.congr rfl (pullback.lift_fst _ _ _).symm)
      (pullback.lift_snd _ _ _)
  letI := T.addCommGroup
  haveI := T.free; haveI := T.finite; haveI := T.i_hom
  let r := Module.finrank ℤ T.X
  obtain ⟨e⟩ : Nonempty (T.X ≃+ (Fin r → ℤ)) := ⟨(Module.finBasis ℤ T.X).equivFun.toAddEquiv⟩
  let i' : splitTorus (Sp k') (Fin r → ℤ) ⟶ H' := GlobalTheory.SplitTorus.torusMap (Sp k') e.toAddMonoidHom ≫ T.i
  have hi' : IsMonHom i' := inferInstance
  have hc : IsClosedImmersion i'.left := by
    have hT := GlobalTheory.TorusSpread.isClosedImmersion_torus T
    haveI : IsIso (GlobalTheory.SplitTorus.torusMap (Sp k') e.toAddMonoidHom) :=
      ⟨⟨GlobalTheory.SplitTorus.torusMap (Sp k') e.symm.toAddMonoidHom, by
        rw [← GlobalTheory.SplitTorus.torusMap_comp, show e.toAddMonoidHom.comp e.symm.toAddMonoidHom = AddMonoidHom.id _ from
          AddMonoidHom.ext fun x => e.apply_symm_apply x, GlobalTheory.SplitTorus.torusMap_id], by
        rw [← GlobalTheory.SplitTorus.torusMap_comp, show e.symm.toAddMonoidHom.comp e.toAddMonoidHom = AddMonoidHom.id _ from
          AddMonoidHom.ext fun x => e.symm_apply_apply x, GlobalTheory.SplitTorus.torusMap_id]⟩⟩
    haveI : IsIso (GlobalTheory.SplitTorus.torusMap (Sp k') e.toAddMonoidHom).left := inferInstanceAs (IsIso ((Over.forget _).map (GlobalTheory.SplitTorus.torusMap (Sp k') e.toAddMonoidHom)))
    rw [Over.comp_left]
    infer_instance
  obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hP.generic_of_isGrpPullback hWn hj (G := splitTorus W (Fin r → ℤ)) (H := G)
    inferInstance hG (GlobalTheory.SplitTorus.isGrpPullback_bcMap j _) ha i'
  have hgen : π (genericPoint W) = y₀ := by
    obtain ⟨z, hz⟩ : genericPoint W ∈ Set.range j := by rw [hj.range_eq]; rfl
    rw [← hz, ← Scheme.Hom.comp_apply, hjπ, Scheme.Hom.comp_apply]
    exact Y.fromSpecResidueField_apply y₀ _
  obtain ⟨eT, heT, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback G₀ s).comp (isGrpPullback_pullback t.G (x₀ ≫ f))).congr (Category.assoc _ _ _).symm rfl)
    (isGrpPullback_pullback t.G ((s ≫ x₀) ≫ f))
  obtain ⟨T', hT'⟩ := GlobalTheory.TorusSpread.torusExtension_of_iso eT T
  refine ⟨W, inferInstance, π, r, u, hπ, inferInstance, hgen, hu, fun k _ g hg =>
    GlobalTheory.T.pullback_closed_immersion_generic_fibre hj u i' (GlobalTheory.SplitTorus.isGrpPullback_bcMap j _).1 ha.1 hu' hc k g hg,
    k', inferInstance, s ≫ x₀, T', ?_, hT'⟩
  show x₀ (s _) = y₀
  exact Y.fromSpecResidueField_apply y₀ _
