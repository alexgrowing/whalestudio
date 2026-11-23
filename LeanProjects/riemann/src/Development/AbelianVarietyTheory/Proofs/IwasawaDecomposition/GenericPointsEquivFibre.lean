import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ClosurePts

theorem lift_closed {K : Type} [Field K] {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z)
    (y : Sp K ⟶ X) (h : below y = i z) : ∃ y' : Sp K ⟶ Z, y' ≫ i = y := by
  obtain ⟨ψ, rfl⟩ := ExtConj.factor y _ h
  have hbij : Function.Bijective (i.residueFieldMap z).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have : IsIso (i.residueFieldMap z) := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  refine ⟨Spec.map (inv (i.residueFieldMap z) ≫ ψ) ≫ Z.fromSpecResidueField z, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, IsIso.hom_inv_id_assoc]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X) (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ M.X) [IsClosedImmersion i], IsArithVar (i ≫ M.p) 0 → i (genericPoint Z) = M.j x → ∀ (K : Type) [Field K] (σ : F →+* K), ∃ E : {y : Sp K ⟶ Z // y ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F))} ≃ {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap σ} // below y.1 = x}, ∀ y, (E y).1.1 ≫ M.j = y.1 ≫ i ∧ below y.1 = genericPoint Z := by
  intro F _ _ Y M x Z _ i _ hZ hx K _ σ
  have : CharZero K := charZero_of_injective_ringHom σ.injective
  have hgen (y : Sp K ⟶ Z) : below y = genericPoint Z :=
    SmallSecHeight.eq_genericPoint hZ (Scheme.SpecToEquivOfField K Z y).2.hom.charZero
  have hpre : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F)) (S := F)
  have hj : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip hpre
  have hs : spMap (σ.comp (algebraMap (𝓞 F) F)) = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Spec.map_comp]
    rfl
  have hw (y : {y : Sp K ⟶ Z // y ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F))}) :
      (y.1 ≫ i) ≫ M.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [Category.assoc, y.2, hs]
  let f : {y : Sp K ⟶ Z // y ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F))} →
      {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap σ} // below y.1 = x} := fun y =>
    ⟨⟨M.pb.lift (y.1 ≫ i) (spMap σ) (hw y), M.pb.lift_snd _ _ _⟩, by
      apply M.j.isEmbedding.injective
      rw [← hx, ← hgen y.1]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun t : Sp K ⟶ M.X => below t) (M.pb.lift_fst _ _ (hw y))).trans
          (Scheme.Hom.comp_apply _ _ _))⟩
  have hf (y) : (f y).1.1 ≫ M.j = y.1 ≫ i := M.pb.lift_fst _ _ _
  refine ⟨Equiv.ofBijective f ⟨fun a b h => ?_, ?_⟩, fun y => ⟨hf y, hgen y.1⟩⟩
  · apply Subtype.ext
    rw [← cancel_mono i, ← hf, ← hf, h]
  · rintro ⟨⟨y, hy⟩, hyx⟩
    obtain ⟨y', hy'⟩ := lift_closed i (genericPoint Z) (y ≫ M.j)
      ((Scheme.Hom.comp_apply _ _ _).trans ((congrArg M.j hyx).trans hx.symm))
    have h1 : y' ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
      rw [← Category.assoc, hy', Category.assoc, M.pb.w, ← Category.assoc, hy, hs]
    refine ⟨⟨y', h1⟩, Subtype.ext (Subtype.ext (M.pb.hom_ext ((hf _).trans hy') ?_))⟩
    exact (f ⟨y', h1⟩).1.2.trans hy.symm

end GlobalTheory.TrueGeo.ClosurePts
