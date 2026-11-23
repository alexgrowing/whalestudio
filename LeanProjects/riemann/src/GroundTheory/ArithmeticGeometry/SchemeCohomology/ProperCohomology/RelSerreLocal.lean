import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjBaseChangeEmbed
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RestrictTensor
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackCoherent
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CohFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace RelSerre

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} [X.Over (Spec (.of A))] {N : ℕ}

variable (A) in

def baseHom {V : X.Opens} (hV : IsAffineOpen V) : CommRingCat.of A ⟶ Γ(X, V) :=
  Spec.preimage (hV.fromSpec ≫ (X ↘ Spec (.of A)))

variable (A) in

abbrev baseAlgebra {V : X.Opens} (hV : IsAffineOpen V) : Algebra A Γ(X, V) :=
  (baseHom A hV).hom.toAlgebra

variable (A) in
lemma specMap_baseAlgebra {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, V))) = hV.fromSpec ≫ (X ↘ Spec (.of A)) := by
  change Spec.map (CommRingCat.ofHom (baseHom A hV).hom) = _
  rw [CommRingCat.ofHom_hom]
  exact Spec.map_preimage _

variable (i : X' ⟶ projectiveSpace A N) (ψ : X' ⟶ X)
  (h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)))

abbrev graph : X' ⟶ pullback (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A)) :=
  pullback.lift i ψ h

instance isClosedImmersion_graph [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))] :
    IsClosedImmersion (graph i ψ h) := by
  have : IsClosedImmersion (graph i ψ h ≫ pullback.fst _ _) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst _ _)

variable (A) in

abbrev overV {V : X.Opens} (hV : IsAffineOpen V) :
    pullback (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) hV.fromSpec ⟶
      pullback (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A)) :=
  pullback.fst _ _

lemma preimage_opensRange_overV {V : X.Opens} (hV : IsAffineOpen V) :
    graph i ψ h ⁻¹ᵁ (overV (N := N) A hV).opensRange = ψ ⁻¹ᵁ V := by
  have e1 : (overV (N := N) A hV).opensRange = (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) ⁻¹ᵁ hV.fromSpec.opensRange :=
    Scheme.Hom.opensRange_pullbackFst _ _
  rw [e1, hV.opensRange_fromSpec, ← Scheme.Hom.comp_preimage, pullback.lift_snd]

def restrictT {V : X.Opens} (hV : IsAffineOpen V) :
    pullback (graph i ψ h) (overV (N := N) A hV) ⟶
      pullback (graph i ψ h) (overV (N := N) A hV).opensRange.ι :=
  pullback.map _ _ _ _ (𝟙 _)
    (IsOpenImmersion.isoOfRangeEq (overV (N := N) A hV) (overV (N := N) A hV).opensRange.ι
      Subtype.range_coe.symm).hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id]; exact (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm)

instance {V : X.Opens} (hV : IsAffineOpen V) : IsIso (restrictT (N := N) i ψ h hV) := by
  unfold restrictT
  infer_instance

lemma inv_restrictT_fst {V : X.Opens} (hV : IsAffineOpen V) :
    inv (restrictT (N := N) i ψ h hV) ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [IsIso.inv_comp_eq, restrictT, pullback.lift_fst, Category.comp_id]

def restrictIso {V : X.Opens} (hV : IsAffineOpen V) :
    (ψ ⁻¹ᵁ V).toScheme ≅ pullback (graph i ψ h) (overV (N := N) A hV) :=
  X'.isoOfEq (preimage_opensRange_overV i ψ h hV).symm ≪≫
    (pullbackRestrictIsoRestrict (graph i ψ h) (overV (N := N) A hV).opensRange).symm ≪≫
    (asIso (restrictT i ψ h hV)).symm

lemma restrictIso_hom_fst {V : X.Opens} (hV : IsAffineOpen V) :
    (restrictIso (N := N) i ψ h hV).hom ≫ pullback.fst _ _ = (ψ ⁻¹ᵁ V).ι := by
  simp only [restrictIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    inv_restrictT_fst, pullbackRestrictIsoRestrict_inv_fst, Scheme.isoOfEq_hom_ι]

variable (A) in

def pasteIso {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    pullback (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) hV.fromSpec ≅
      pullback (ProjSpace.toSpecBase A N) (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, V)))) :=
  letI := baseAlgebra A hV
  pullbackLeftPullbackSndIso _ _ _ ≪≫ pullback.congrHom rfl (specMap_baseAlgebra A hV).symm

variable (A) in
lemma pasteIso_hom_fst {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    (pasteIso (N := N) A hV).hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [pasteIso, Iso.trans_hom, Category.assoc, pullback.congrHom, asIso_hom, pullback.map]
  erw [pullback.lift_fst]
  rw [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

variable (A) in
lemma pasteIso_hom_snd {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    (pasteIso (N := N) A hV).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [pasteIso, Iso.trans_hom, Category.assoc, pullback.congrHom, asIso_hom, pullback.map]
  erw [pullback.lift_snd]
  rw [Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

def embed {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    (ψ ⁻¹ᵁ V).toScheme ⟶
      pullback (ProjSpace.toSpecBase A N) (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, V)))) :=
  (restrictIso i ψ h hV).hom ≫ pullback.snd _ _ ≫ (pasteIso A hV).hom

instance isClosedImmersion_embed [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))]
    {V : X.Opens} (hV : IsAffineOpen V) : IsClosedImmersion (embed i ψ h hV) := by
  unfold embed
  infer_instance

lemma embed_fst {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    embed i ψ h hV ≫ pullback.fst _ _ = (ψ ⁻¹ᵁ V).ι ≫ i := by
  have hc : pullback.snd (graph i ψ h) (overV (N := N) A hV) ≫ overV A hV =
      pullback.fst _ _ ≫ graph i ψ h := pullback.condition.symm
  have hp := pasteIso_hom_fst (N := N) A hV
  simp only [embed, Category.assoc]
  rw [hp, ← Category.assoc (pullback.snd _ _) (pullback.fst _ _), show pullback.fst (pullback.snd
    (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) hV.fromSpec = overV A hV from rfl, hc,
    Category.assoc, pullback.lift_fst, ← Category.assoc, restrictIso_hom_fst]

end RelSerre

end

end GroundTheory.Arith.SchemeCoh
