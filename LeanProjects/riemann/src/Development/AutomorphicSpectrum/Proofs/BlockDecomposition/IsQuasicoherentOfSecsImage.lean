import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsetOfClosedFibre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.PSupp

lemma secs_mk {X : Scheme.{0}} {E F : X.Modules} (i : F ⟶ E) [Mono i] (V : X.Opens) :
    secs (Subobject.mk i) V = Set.range (i.app V) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso i).hom.app V x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso i).inv.app V x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_arrow]

lemma restrict_map_app {X : Scheme.{0}} (O : X.Opens) {Q P : X.Modules} (a : Q ⟶ P)
    (W : (O : Scheme.{0}).Opens) (y : Γ(Q.restrict O.ι, W)) :
    ((Scheme.Modules.restrictFunctor O.ι).map a).app W y =
      (P.restrictAppIso O.ι W).inv (a.app (O.ι ''ᵁ W) ((Q.restrictAppIso O.ι W).hom y)) :=
  rfl

theorem isQuasicoherent_of_secs_image {X : Scheme.{0}} (O : X.Opens) {P : X.Modules}
    {E : (O : Scheme.{0}).Modules} (hP : P.IsQuasicoherent) (hE : E.IsQuasicoherent)
    (f : P.restrict O.ι ⟶ E) (Bb : Subobject P) (hBb : (Bb : X.Modules).IsQuasicoherent)
    (B : Subobject E)
    (hB : ∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W =
      (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) :
    (B : (O : Scheme.{0}).Modules).IsQuasicoherent := by
  let g : (Bb : X.Modules).restrict O.ι ⟶ E := (Scheme.Modules.restrictFunctor O.ι).map Bb.arrow ≫ f
  have hBr : ((Bb : X.Modules).restrict O.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor O.ι _
  have hs : ∀ U : (O : Scheme.{0}).affineOpens,
      secs B (U : (O : Scheme.{0}).Opens) =
        secs (Subobject.mk (kernel.ι (cokernel.π g))) (U : (O : Scheme.{0}).Opens) := by
    intro U
    rw [secs_mk, range_kernel_ι_cokernel_π_app g U.2, hB _ U.2]
    ext m
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨((Bb : X.Modules).restrictAppIso O.ι (U : (O : Scheme.{0}).Opens)).inv y, ?_⟩
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, restrict_map_app, Iso.inv_hom_id_apply]
    · rintro ⟨y, rfl⟩
      refine ⟨_, ⟨((Bb : X.Modules).restrictAppIso O.ι (U : (O : Scheme.{0}).Opens)).hom y, rfl⟩, ?_⟩
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, restrict_map_app]
  have hEq : B = Subobject.mk (kernel.ι (cokernel.π g)) :=
    le_antisymm ((GlobalTheory.T.subobject_le_iff_affine_sections _ _).2 fun U => (hs U).subset)
      ((GlobalTheory.T.subobject_le_iff_affine_sections _ _).2 fun U => (hs U).symm.subset)
  have hK : (kernel (cokernel.π g)).IsQuasicoherent := inferInstance
  rw [hEq]
  exact GlobalTheory.QCoh.isQuasicoherent_of_iso (Subobject.underlyingIso (kernel.ι (cokernel.π g))).symm

end GlobalTheory.CompanionTheory.GE.PSupp
