import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.HodgeCoh
open GlobalTheory.CechDR

variable {k : Type} [CommRing k] {X : Scheme.{0}}

def formRes (s : X ⟶ Sp k) {U V : X.Opens} (h : V ≤ U) (j : ℕ) :
    OmU s U j →ₛₗ[RingHom.id k] OmU s V j :=
  (SemiHom.of_algHom (Sec.res s h)).mOm j

theorem formRes_smul (s : X ⟶ Sp k) {U V : X.Opens} (h : V ≤ U) {j : ℕ} (b : Sec s U)
    (x : OmU s U j) : formRes s h j (b • x) = Sec.res s h b • formRes s h j x :=
  SemiHom.mOm_smul _ b x

theorem formRes_refl (s : X ⟶ Sp k) (U : X.Opens) {j : ℕ} (x : OmU s U j) :
    formRes s (le_refl U) j x = x :=
  SemiHom.mOm_id _ (fun b ↦ congrArg (fun q ↦ q.hom b) (X.presheaf.map_id (op U))) x

theorem formRes_formRes (s : X ⟶ Sp k) {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) {j : ℕ}
    (x : OmU s U j) : formRes s h' j (formRes s h j x) = formRes s (h'.trans h) j x :=
  SemiHom.mOm_mOm _ _ _ (fun b ↦ (Sec.res_res s h h' b).symm) x

def formsAb (s : X ⟶ Sp k) (j : ℕ) : X.Opensᵒᵖ ⥤ Ab where
  obj U := AddCommGrpCat.of (OmU s U.unop j)
  map i := AddCommGrpCat.ofHom (formRes s (leOfHom i.unop) j).toAddMonoidHom
  map_id U := AddCommGrpCat.ext fun x ↦ formRes_refl s U.unop x
  map_comp i i' := AddCommGrpCat.ext fun x ↦ (formRes_formRes s _ _ x).symm

instance formsAb_module (s : X ⟶ Sp k) (j : ℕ) (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((formsAb s j).obj U) :=
  inferInstanceAs (Module (Sec s U.unop) (OmU s U.unop j))

def formsPre (s : X ⟶ Sp k) (j : ℕ) : PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (formsAb s j) fun _ _ i b x ↦ formRes_smul s (leOfHom i.unop) b x

def Omega (s : X ⟶ Sp k) (j : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (formsPre s j)

abbrev algΓ (s : X ⟶ Sp k) : Algebra k Γ(X, ⊤) := algebraΓOfHom s

def hodgeH (s : X ⟶ Sp k) (j q : ℕ) : Type := coh (Omega s j) q

instance (s : X ⟶ Sp k) (j q : ℕ) : AddCommGroup (hodgeH s j q) :=
  inferInstanceAs (AddCommGroup (coh (Omega s j) q))

instance (s : X ⟶ Sp k) (j q : ℕ) : Module k (hodgeH s j q) :=
  letI := algΓ s
  inferInstanceAs (Module k (coh (Omega s j) q))

section Pull

variable {X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k} {f : X' ⟶ X}

variable (s s' f) in

def appSec (U : X.Opens) : Sec s U →+* Sec s' (f ⁻¹ᵁ U) := (f.app U).hom

omit [CommRing k] in
theorem appLE_comp_app {Y : Scheme.{0}} (g : X ⟶ Y) (f : X' ⟶ X) (U : X.Opens) (V : Y.Opens)
    (e : U ≤ g ⁻¹ᵁ V) (e' : f ⁻¹ᵁ U ≤ (f ≫ g) ⁻¹ᵁ V) :
    g.appLE V U e ≫ f.app U = (f ≫ g).appLE V (f ⁻¹ᵁ U) e' := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

theorem semiHom_appSec (hf : f ≫ s = s') (U : X.Opens) :
    SemiHom (RingHom.id k) (appSec s s' f U) := fun r b ↦ by
  subst hf
  rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  change (f.app U).hom ((secMap s U).hom r) = (secMap (f ≫ s) (f ⁻¹ᵁ U)).hom r
  rw [← CommRingCat.comp_apply]
  congr 2
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ U le_top) ≫ f.app U =
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (f ≫ s).appLE ⊤ (f ⁻¹ᵁ U) le_top
  rw [Category.assoc]
  congr 1
  exact appLE_comp_app s f U ⊤ _ _

end Pull

section Pull2

variable {X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k} {f : X' ⟶ X}

def formPull (hf : f ≫ s = s') (U : X.Opens) (j : ℕ) :
    OmU s U j →ₛₗ[RingHom.id k] OmU s' (f ⁻¹ᵁ U) j :=
  (semiHom_appSec hf U).mOm j

theorem formPull_smul (hf : f ≫ s = s') (U : X.Opens) {j : ℕ} (b : Sec s U) (x : OmU s U j) :
    formPull hf U j (b • x) = appSec s s' f U b • formPull hf U j x :=
  SemiHom.mOm_smul _ b x

theorem formRes_formPull (hf : f ≫ s = s') {U V : X.Opens} (h : V ≤ U) {j : ℕ} (x : OmU s U j) :
    formRes s' (f.preimage_mono h) j (formPull hf U j x) = formPull hf V j (formRes s h j x) := by
  have e : ∀ b : Sec s U, Sec.res s' (f.preimage_mono h) (appSec s s' f U b) =
      appSec s s' f V (Sec.res s h b) := fun b ↦ by
    change (f.app U ≫ X'.presheaf.map (homOfLE (f.preimage_mono h)).op).hom b =
      (X.presheaf.map (homOfLE h).op ≫ f.app V).hom b
    rw [f.naturality]; rfl
  have hγ : SemiHom (RingHom.id k) ((appSec s s' f V).comp (Sec.res s h : Sec s U →+* Sec s V)) :=
    (SemiHom.of_algHom (Sec.res s h)).comp (semiHom_appSec hf V)
  exact (SemiHom.mOm_mOm (semiHom_appSec hf U) (SemiHom.of_algHom (Sec.res s' (f.preimage_mono h)))
    hγ e x).trans (SemiHom.mOm_mOm (SemiHom.of_algHom (Sec.res s h)) (semiHom_appSec hf V) hγ
      (fun _ ↦ rfl) x).symm

end Pull2

section Pull3

variable {X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k} {f : X' ⟶ X}

variable (s) in

def toOmega (j : ℕ) : formsPre s j ⟶
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
      (Omega s j) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (formsPre s j)

def pullPre (hf : f ≫ s = s') (j : ℕ) : formsPre s j ⟶
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
      ((Scheme.Modules.pushforward f).obj (Omega s' j)) where
  app U := ModuleCat.ofHom
    { toFun x := ((toOmega s' j).app (op (f ⁻¹ᵁ U.unop))).hom (formPull hf U.unop j x)
      map_add' x y := (congrArg _ (map_add _ x y)).trans (map_add _ _ _)
      map_smul' b x := (congrArg ((toOmega s' j).app (op (f ⁻¹ᵁ U.unop))).hom
        (formPull_smul hf U.unop b x)).trans
          (((toOmega s' j).app (op (f ⁻¹ᵁ U.unop))).hom.map_smul (appSec s s' f U.unop b) _) }
  naturality {U V} i := by
    ext x
    exact (congrArg ((toOmega s' j).app (op (f ⁻¹ᵁ V.unop))).hom
      (formRes_formPull hf (leOfHom i.unop) x)).symm.trans
        (PresheafOfModules.naturality_apply (toOmega s' j)
          ((TopologicalSpace.Opens.map f.base).map i.unop).op (formPull hf U.unop j x))

end Pull3

section Pull4

variable {X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k} {f : X' ⟶ X}

def omegaPull (hf : f ≫ s = s') (j : ℕ) :
    Omega s j ⟶ (Scheme.Modules.pushforward f).obj (Omega s' j) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm
    (pullPre hf j)

theorem appTop_algebraMap (hf : f ≫ s = s') (r : k) :
    letI := algΓ s; letI := algΓ s'
    f.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(X', ⊤) (RingHom.id k r) := by
  subst hf
  change (f.appTop).hom ((s.appTop).hom _) = ((f ≫ s).appTop).hom _
  rw [Scheme.Hom.comp_appTop]; rfl

def hodgePull (hf : f ≫ s = s') (j q : ℕ) : hodgeH s j q →ₗ[k] hodgeH s' j q :=
  letI := algΓ s; letI := algΓ s'
  cohOn.pull (appTop_algebraMap hf) (omegaPull hf j) (le_refl (f ⁻¹ᵁ ⊤)) q

end Pull4

section Api

variable {X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k} {f : X' ⟶ X}

theorem omegaPull_toOmega (hf : f ≫ s = s') (j : ℕ) (U : X.Opens) (x : OmU s U j) :
    (omegaPull hf j).val.app (op U) ((toOmega s j).app (op U) x) =
      (toOmega s' j).app (op (f ⁻¹ᵁ U)) (formPull hf U j x) := by
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
    (formsPre s j) ((Scheme.Modules.pushforward f).obj (Omega s' j)) (omegaPull hf j)
  rw [omegaPull, Equiv.apply_symm_apply] at h
  have h2 := congrArg (fun φ ↦ (φ.app (op U)).hom x) h
  exact h2.symm

end Api

section Zero

variable {B : Type} [CommRing B] [Algebra k B]

theorem coe_eq_algebraMap_zeroEquiv (x : Om k B 0) :
    (x : DR k B) = algebraMap B (DR k B) (exteriorPower.zeroEquiv B Ω[B⁄k] x) := by
  conv_lhs => rw [← (exteriorPower.zeroEquiv B Ω[B⁄k]).symm_apply_apply x]
  generalize exteriorPower.zeroEquiv B Ω[B⁄k] x = b
  rw [exteriorPower.zeroEquiv_symm_apply, Submodule.coe_smul, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]

theorem zeroEquiv_mOm {k' B' : Type} [CommRing k'] [CommRing B'] [Algebra k' B'] {σ : k →+* k'}
    {α : B →+* B'} (h : SemiHom σ α) (x : Om k B 0) :
    exteriorPower.zeroEquiv B' Ω[B'⁄k'] (h.mOm 0 x) = α (exteriorPower.zeroEquiv B Ω[B⁄k] x) := by
  rw [← LinearEquiv.eq_symm_apply]
  apply Subtype.ext
  rw [SemiHom.coe_mOm, coe_eq_algebraMap_zeroEquiv x, SemiHom.mDR_algebraMap,
    coe_eq_algebraMap_zeroEquiv (k := k') ((exteriorPower.zeroEquiv B' Ω[B'⁄k']).symm _),
    LinearEquiv.apply_symm_apply]

end Zero

section Zero2

variable (s : X ⟶ Sp k)

def formsZeroEquiv (U : X.Opensᵒᵖ) : (formsPre s 0).obj U ≃ₗ[X.ringCatSheaf.obj.obj U]
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
      (structureModule X)).obj U :=
  exteriorPower.zeroEquiv (Sec s U.unop) Ω[Sec s U.unop⁄k]

def formsPreZeroIso : formsPre s 0 ≅
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
      (structureModule X) :=
  PresheafOfModules.isoMk (fun U ↦ (formsZeroEquiv s U).toModuleIso)
    (fun U V i ↦ by
      ext x
      exact zeroEquiv_mOm (SemiHom.of_algHom (Sec.res s (leOfHom i.unop))) x)

def omegaZeroIso : Omega s 0 ≅ structureModule X :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (formsPreZeroIso s) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app
      (structureModule X)

def hodgeZeroZeroEquiv : letI := algΓ s; hodgeH s 0 0 ≃ₗ[k] Γ(X, ⊤) :=
  letI := algΓ s
  (cohOn.mapIso k ⊤ 0 (omegaZeroIso s)).trans ((coh.zeroUnitEquiv X).restrictScalars k)

end Zero2

example (s : X ⟶ Sp k) : Module k (hodgeH s 2 1) := inferInstance

example : Nontrivial (hodgeH (𝟙 (Sp ℤ)) 0 0) :=
  letI : Nontrivial Γ(Sp ℤ, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  (hodgeZeroZeroEquiv (𝟙 (Sp ℤ))).toEquiv.nontrivial

example {X' : Scheme.{0}} (s : X ⟶ Sp k) (f : X' ⟶ X) (r : k) (x : hodgeH s 1 1) :
    hodgePull (s' := f ≫ s) rfl 1 1 (r • x) = r • hodgePull (s' := f ≫ s) rfl 1 1 x :=
  map_smul _ r x

end GlobalTheory.HodgeCoh
