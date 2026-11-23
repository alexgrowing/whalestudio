import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

lemma secs_mk {X : Scheme.{0}} {E F : X.Modules} (m : F ⟶ E) [Mono m] (W : X.Opens) :
    secs (Subobject.mk m) W = Set.range (m.app W) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso m).hom.app W x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso m).inv.app W x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_arrow]

lemma isQuasicoherent_image {X : Scheme.{0}} {F E : X.Modules} [F.IsQuasicoherent]
    [E.IsQuasicoherent] (g : F ⟶ E) :
    ((Subobject.mk (kernel.ι (cokernel.π g)) : Subobject E) : X.Modules).IsQuasicoherent :=
  haveI := isQuasicoherent_kernel (cokernel.π g)
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (kernel.ι (cokernel.π g))).symm inferInstance

lemma secs_image {X : Scheme.{0}} {F E : X.Modules} [F.IsQuasicoherent]
    [E.IsQuasicoherent] (g : F ⟶ E) (W : X.Opens) (hW : IsAffineOpen W) :
    secs (Subobject.mk (kernel.ι (cokernel.π g))) W = Set.range (g.app W) := by
  rw [secs_mk]
  haveI := isQuasicoherent_kernel (cokernel.π g)
  have hs : Function.Surjective ((Abelian.factorThruImage g).app W) :=
    GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen (Abelian.factorThruImage g) hW
  have h : ∀ y, (kernel.ι (cokernel.π g)).app W ((Abelian.factorThruImage g).app W y) =
      g.app W y := fun y => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app]
    exact congrArg (fun φ : F ⟶ E => φ.app W y) (Abelian.image.fac g)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hs x
    exact ⟨y, (h y).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨(Abelian.factorThruImage g).app W x, h x⟩

end GlobalTheory.CompanionTheory.GE.ImageOpen

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

attribute [local instance] algebraOfOver

lemma toFunctions_open {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (O : X.Opens) :
    letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
    ∀ (U : (O : Scheme.{0}).Opens) (r : A),
      (O.ι.appIso U).hom (toFunctions (A := A) (O.ι ''ᵁ U) r) = toFunctions (A := A) U r := by
  intro U r
  change (O.ι.appIso U).hom (X.presheaf.map (homOfLE le_top).op
      ((X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv r))) =
    (O : Scheme.{0}).presheaf.map (homOfLE le_top).op
      ((O.ι ≫ (X ↘ Spec (.of A))).appTop ((Scheme.ΓSpecIso (.of A)).inv r))
  rw [Scheme.Hom.comp_appTop]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  rfl

end GlobalTheory.CompanionTheory.GE.ImageOpen

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

lemma map_mem_secs_powSub {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] (O : X.Opens) :
    letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
    ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, P.IsQuasicoherent → E.IsQuasicoherent →
      ∀ (f : P.restrict O.ι ⟶ E) (n : ℕ) (U : (O : Scheme.{0}).Opens), IsAffineOpen U →
      ∀ x : Γ(P, O.ι ''ᵁ U), x ∈ secs (powSub I P n) (O.ι ''ᵁ U) →
        f.app U ((P.restrictAppIso O.ι U).inv x) ∈ secs (powSub I E n) U := by
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f n U hU x hx
  have hU' : IsAffineOpen (O.ι ''ᵁ U) := hU.image_of_isOpenImmersion O.ι
  rw [secs_powSub I P hP n _ hU'] at hx
  rw [secs_powSub I E hE n U hU]
  have hmul : ∀ (a : Γ(X, O.ι ''ᵁ U)) (m : Γ(P, O.ι ''ᵁ U)),
      f.app U ((P.restrictAppIso O.ι U).inv (a • m)) =
        (O.ι.appIso U).hom a • f.app U ((P.restrictAppIso O.ι U).inv m) := by
    intro a m
    rw [Scheme.Modules.smul_restrictAppIso_inv_apply, Scheme.Modules.Hom.app_smul]
  have hJ : ∀ a ∈ Ideal.map (toFunctions (A := A) (O.ι ''ᵁ U)) (I ^ n),
      (O.ι.appIso U).hom a ∈ Ideal.map (toFunctions (A := A) U) (I ^ n) := by
    intro a ha
    have := Ideal.mem_map_of_mem (O.ι.appIso U).hom.hom ha
    rw [Ideal.map_map] at this
    convert this using 2
    ext r
    exact (toFunctions_open O U r).symm
  change x ∈ (Ideal.map (toFunctions (A := A) (O.ι ''ᵁ U)) (I ^ n) • ⊤ :
    Submodule Γ(X, O.ι ''ᵁ U) Γ(P, O.ι ''ᵁ U)) at hx
  refine Submodule.smul_induction_on
    (p := fun x => f.app U ((P.restrictAppIso O.ι U).inv x) ∈
      (Ideal.map (toFunctions (A := A) U) (I ^ n) • ⊤ : Submodule Γ((O : Scheme.{0}), U) Γ(E, U)))
    hx ?_ ?_
  · intro a ha m _
    show _ ∈ _
    rw [hmul]
    exact Submodule.smul_mem_smul (hJ a ha) Submodule.mem_top
  · intro y z hy hz
    show _ ∈ _
    rw [map_add, map_add]
    exact Submodule.add_mem _ hy hz

end GlobalTheory.CompanionTheory.GE.ImageOpen

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

lemma isQuasicoherent_powSub {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {Y : Scheme.{0}} [Y.Over (Spec (.of A))] (M : Y.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((powSub I M (n + 1) : Subobject M) : Y.Modules).IsQuasicoherent :=
  (closedSys_pow I M).qcoh n

theorem image_on_open : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ S : ℕ → Subobject E, ClosedSys I E S → ∀ Sb : ℕ → Subobject P, (∀ e (W : (O : Scheme.{0}).Opens), IsAffineOpen W → ∀ x : Γ(P, O.ι ''ᵁ W), x ∈ secs (Sb e) (O.ι ''ᵁ W) ↔ f.app W ((P.restrictAppIso O.ι W).inv x) ∈ secs (S e) W) → ∀ Bb : Subobject P, (Bb : X.Modules).IsQuasicoherent → (∀ e, Bb ⊔ powSub I P (e + 1) = Sb e) → ∃ B : Subobject E, (B : (O : Scheme.{0}).Modules).IsQuasicoherent ∧ (∀ e, B ⊔ powSub I E (e + 1) = S e) ∧ ∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W) := by
  intro A _ _ I X _ _ O
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f hf S hS Sb hSb Bb hBb hBS
  haveI := hP.1
  haveI := hE.1
  haveI : (Bb : X.Modules).IsQuasicoherent := hBb
  haveI : Epi f := hf
  haveI : ((Bb : X.Modules).restrict O.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  haveI : (P.restrict O.ι).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  let g : (Bb : X.Modules).restrict O.ι ⟶ E := (Scheme.Modules.restrictFunctor O.ι).map Bb.arrow ≫ f
  let B : Subobject E := Subobject.mk (kernel.ι (cokernel.π g))
  have hBq : (B : (O : Scheme.{0}).Modules).IsQuasicoherent := isQuasicoherent_image g
  have hsecs : ∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W =
      (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W) := by
    intro W hW
    rw [secs_image g W hW]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨Bb.arrow.app _ z, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  refine ⟨B, hBq, fun e => ?_, hsecs⟩
  have hBle : Bb ≤ Sb e := hBS e ▸ le_sup_left
  apply le_antisymm
  · refine sup_le ?_ (hS.pow_le e)
    rw [le_iff_secs_subset]
    rintro ⟨W, hW⟩ y hy
    rw [hsecs W hW] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : x ∈ secs (Sb e) (O.ι ''ᵁ W) :=
      (le_iff_secs_subset _ _).1 hBle ⟨_, hW.image_of_isOpenImmersion O.ι⟩ hx
    exact (hSb e W hW x).1 hx'
  · rw [le_iff_secs_subset]
    rintro ⟨W, hW⟩ y hy
    change y ∈ secs (S e) W at hy
    change y ∈ secs (B ⊔ powSub I E (e + 1)) W
    have hW' : IsAffineOpen (O.ι ''ᵁ W) := hW.image_of_isOpenImmersion O.ι
    rw [(supsecs hE.1 B (powSub I E (e + 1)) hBq (isQuasicoherent_powSub I E e)).2 W hW]
    obtain ⟨z, rfl⟩ := GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen f hW y
    have hx : (P.restrictAppIso O.ι W).hom z ∈ secs (Sb e) (O.ι ''ᵁ W) := (hSb e W hW _).2 hy
    rw [← hBS e, (supsecs hP.1 Bb (powSub I P (e + 1)) hBb (isQuasicoherent_powSub I P e)).2 _ hW']
      at hx
    obtain ⟨s, hs, t, ht, hst⟩ := hx
    refine ⟨f.app W ((P.restrictAppIso O.ι W).inv s), (hsecs W hW).symm ▸ ⟨s, hs, rfl⟩,
      f.app W ((P.restrictAppIso O.ι W).inv t),
      map_mem_secs_powSub I O hP.1 hE.1 f (e + 1) W hW t ht, ?_⟩
    rw [← map_add, ← map_add, ← hst]
    rfl

end GlobalTheory.CompanionTheory.GE.ImageOpen
