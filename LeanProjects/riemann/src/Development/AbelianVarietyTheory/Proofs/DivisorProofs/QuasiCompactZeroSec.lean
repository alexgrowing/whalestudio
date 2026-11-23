import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.LieVB GlobalTheory.Conormal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

section Op

variable (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]

abbrev opModule : Module Oᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id O).fromOpposite fun x y => Commute.all x y)

theorem opModule_central : @IsCentralScalar O M _ (opModule O M).toSMul :=
  @IsCentralScalar.mk O M _ (opModule O M).toSMul fun _ _ => rfl

end Op

section Defs

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

abbrev TM : Over (Sp O) := Over.mk (spMap (algebraMap O (TrivSqZeroExt O M)))

def zeroSec : 𝟙_ (Over (Sp O)) ⟶ TM O M :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom O O M).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

theorem isChart : IsChart (TM O M).hom (sec (zeroSec O M)) ⊤ ⊤ :=
  ⟨isAffineOpen_top (Sp O), isAffineOpen_top (Spec (CommRingCat.of (TrivSqZeroExt O M))), le_top, le_top⟩

abbrev topModule : Module Γ(Sp O, ⊤) M :=
  Module.compHom M (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom

abbrev toTsze : Γ((TM O M).left, ⊤) →+* TrivSqZeroExt O M :=
  (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt O M))).hom.hom

abbrev toO : Γ(Sp O, ⊤) →+* O := (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom

theorem toTsze_base (r : Γ(Sp O, ⊤)) :
    toTsze O M ((TM O M).hom.appLE ⊤ ⊤ le_top r) = algebraMap O _ (toO O r) := by
  rw [appLE_top]
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O (TrivSqZeroExt O M)))) r)

theorem toO_sec (b : Γ((TM O M).left, ⊤)) :
    toO O ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top b) = (toTsze O M b).fst := by
  rw [appLE_top]
  exact congr($(Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O M).toRingHom)) b)

end Defs

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

section Kappa

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

def sndFn : letI := (isChart O M).algebra; letI := topModule O M
    Γ((TM O M).left, ⊤) →ₗ[Γ(Sp O, ⊤)] M :=
  letI := (isChart O M).algebra
  letI := topModule O M
  { toFun := fun b => (toTsze O M b).snd
    map_add' := fun a b => by simp
    map_smul' := fun r b => by
      change (toTsze O M ((TM O M).hom.appLE ⊤ ⊤ le_top r * b)).snd = toO O r • (toTsze O M b).snd
      rw [map_mul, toTsze_base, TrivSqZeroExt.snd_mul]
      simp [TrivSqZeroExt.algebraMap_eq_inl] }

theorem sndFn_apply (b : Γ((TM O M).left, ⊤)) :
    letI := (isChart O M).algebra; letI := topModule O M
    sndFn O M b = (toTsze O M b).snd := rfl

theorem sndFn_der (a b : Γ((TM O M).left, ⊤)) :
    letI := (isChart O M).algebra; letI := topModule O M
    sndFn O M (a * b) = (isChart O M).aug (sec_hom _) a • sndFn O M b +
      (isChart O M).aug (sec_hom _) b • sndFn O M a := by
  letI := (isChart O M).algebra
  letI := topModule O M
  rw [sndFn_apply, sndFn_apply, sndFn_apply, map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
  change _ = (toO O ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top a) • (toTsze O M b).snd : M) +
    toO O ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top b) • (toTsze O M a).snd
  rw [toO_sec, toO_sec]

instance quasiCompact_zeroSec : QuasiCompact (sec (zeroSec O M)) := by
  have : QuasiSeparated (TM O M).hom := show QuasiSeparated (Spec.map _) from inferInstance
  infer_instance

def kappa : Γ(conormal (sec (zeroSec O M)), ⊤) →+ M :=
  letI := (isChart O M).algebra
  letI := topModule O M
  ((AugCot.lift ((isChart O M).aug (sec_hom _)) (sndFn O M) (sndFn_der O M)).toAddMonoidHom).comp
    ((isChart O M).augCotEquiv (sec_hom _)).symm.toLinearMap.toAddMonoidHom

theorem kappa_d (b : Γ((TM O M).left, ⊤)) :
    kappa O M (d (sec_hom (zeroSec O M)) le_top b) = (toTsze O M b).snd := by
  letI := (isChart O M).algebra
  letI := topModule O M
  change (AugCot.lift ((isChart O M).aug (sec_hom _)) (sndFn O M) (sndFn_der O M))
    (((isChart O M).augCotEquiv (sec_hom _)).symm (d (sec_hom (zeroSec O M)) le_top b)) = _
  rw [← (isChart O M).augCotEquiv_d (sec_hom _) b, LinearEquiv.symm_apply_apply, AugCot.lift_d]
  rfl

end Kappa

section Phi

variable {O : Type} [CommRing O]

variable (A : Over (Sp O)) [GrpObj A] in

def Wmod : Type := Γ(omega A, ⊤)

instance (A : Over (Sp O)) [GrpObj A] : AddCommGroup (Wmod A) :=
  inferInstanceAs (AddCommGroup Γ(omega A, ⊤))

instance (A : Over (Sp O)) [GrpObj A] : Module O (Wmod A) :=
  Module.compHom Γ(omega A, ⊤) (cst O)

variable {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]
  {A : Over (Sp O)} [GrpObj A]

def Phi (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) : Wmod A →+ M :=
  (kappa O M).comp (QCoh.appLinear (cotMap z h) ⊤).toAddMonoidHom

theorem Phi_apply (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (w : Wmod A) :
    Phi z h w = kappa O M ((cotMap z h).app ⊤ w) := rfl

end Phi

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

section Tower

open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham

scoped instance cotOp {O B : Type} [CommRing O] [CommRing B] [Bialgebra O B] :
    Module Oᵐᵒᵖ (Cot O B) := opModule O _

scoped instance cotCentral {O B : Type} [CommRing O] [CommRing B] [Bialgebra O B] :
    IsCentralScalar O (Cot O B) := opModule_central O _

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {A : Over (Sp O)} [GrpObj A]
  {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]

theorem zeroSec_spOver_y (t : G.TorsionTower A) (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M)
    (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) :
    zeroSec O M ≫ spOver φ ≫ t.y n = η[A] := by
  have h1 := (t.eq_one_iff n (Bialgebra.counitAlgHom O (G.A n))).2 fun a => by simp
  have h2 := congrArg Over.Hom.left h1
  simp only [Over.comp_left] at h2
  ext1
  simp only [Over.comp_left]
  have e : (zeroSec O M).left ≫ (spOver φ).left =
      (spOver (Bialgebra.counitAlgHom O (G.A n))).left := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact congrArg (fun f => f a) (congrArg AlgHom.toRingHom hφ)
  rw [← Category.assoc, e, h2]
  have hu : (toUnit (Over.mk (spMap (algebraMap O O)))).left = 𝟙 (Sp O) := by
    rw [Over.toUnit_left]; exact Spec.map_id _
  change (toUnit (Over.mk (spMap (algebraMap O O)))).left ≫ η[A].left = η[A].left
  erw [hu]
  exact Category.id_comp _

variable (G) in

def univ (n : ℕ) : G.A n →ₐ[O] TrivSqZeroExt O (Cot O (G.A n)) :=
  AugCot.toSqZero (Bialgebra.counitAlgHom O (G.A n)) LinearMap.id

theorem fst_comp_univ (n : ℕ) :
    (TrivSqZeroExt.fstHom O O (Cot O (G.A n))).comp (univ G n) =
      Bialgebra.counitAlgHom O (G.A n) := by
  ext a; simp [univ]

def cn (t : G.TorsionTower A) (n : ℕ) : Wmod A →+ Cot O (G.A n) :=
  Phi (spOver (univ G n) ≫ t.y n) (zeroSec_spOver_y t n _ (fst_comp_univ (G := G) n))

end Tower

end GlobalTheory.SqZeroPt
