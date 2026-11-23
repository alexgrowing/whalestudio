import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulEqZeroOfAppEqZero

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap resG)
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.LB (resG_resG resG_self)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

section
variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

theorem sec_zeroSec_base (x : (TM O M).left) :
    (sec (zeroSec O M)).base ((TM O M).hom.base x) = x := by
  change (Spec.map _).base ((Spec.map _).base x) = x
  rw [Spec.map_base, Spec.map_base]
  revert x
  intro (x : PrimeSpectrum (TrivSqZeroExt O M))
  change PrimeSpectrum.comap (TrivSqZeroExt.fstHom O O M).toRingHom
    (PrimeSpectrum.comap (algebraMap O (TrivSqZeroExt O M)) x) = x
  refine PrimeSpectrum.ext (Ideal.ext fun r => ?_)
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have hsq : (TrivSqZeroExt.inr r.snd : TrivSqZeroExt O M) ∈ x.asIdeal :=
    x.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact x.asIdeal.zero_mem)
  have e : r = algebraMap O (TrivSqZeroExt O M) r.fst + TrivSqZeroExt.inr r.snd := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  change algebraMap O (TrivSqZeroExt O M) r.fst ∈ x.asIdeal ↔ r ∈ x.asIdeal
  constructor
  · intro h
    rw [e]
    exact x.asIdeal.add_mem h hsq
  · intro h
    have : algebraMap O (TrivSqZeroExt O M) r.fst = r - TrivSqZeroExt.inr r.snd := by
      rw [eq_sub_iff_add_eq, ← e]
    rw [this]
    exact x.asIdeal.sub_mem h hsq

theorem le_of_le_zeroSec {V : (Sp O).Opens} {W : (TM O M).left.Opens}
    (h : V ≤ sec (zeroSec O M) ⁻¹ᵁ W) : (TM O M).hom ⁻¹ᵁ V ≤ W := fun x hx => by
  have := h hx
  rwa [Scheme.Hom.mem_preimage, sec_zeroSec_base] at this

theorem mul_eq_zero_of_zeroSec (U : (TM O M).left.Opens) (x y : Γ((TM O M).left, U))
    (hx : (sec (zeroSec O M)).app U x = 0) (hy : (sec (zeroSec O M)).app U y = 0) : x * y = 0 := by
  refine GlobalTheory.SquareZero.mul_eq_zero_of_app_eq_zero (TrivSqZeroExt O M) O
    (TrivSqZeroExt.fstHom O O M).toRingHom (fun a => ⟨TrivSqZeroExt.inl a, by simp⟩) ?_
    (TM O M).left (Sp O) (𝟙 _) (𝟙 _) (sec (zeroSec O M)) (IsPullback.of_vert_isIso ⟨by simp; rfl⟩) U x y hx hy
  rw [eq_bot_iff, pow_two]
  refine Ideal.mul_le.2 fun a ha b hb => ?_
  have ha' : a.fst = 0 := ha
  have hb' : b.fst = 0 := hb
  rw [Ideal.mem_bot]
  ext <;> simp [ha', hb']

end

theorem appLinear_top_bijective {O : Type} [CommRing O] (F G : (Sp O).Modules) [F.IsQuasicoherent] :
    Function.Bijective fun φ : F ⟶ G => GlobalTheory.QCoh.appLinear φ ⊤ := by
  have : IsIso ((tilde.adjunction (R := .of O)).counit.app F) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of O) F
  have h := GlobalTheory.OmegaGlobal.map_bijective_of_isIso_counit (tilde.adjunction (R := .of O)) F G
  constructor
  · intro φ ψ e
    apply h.1
    ext s
    exact congr($e s)
  · intro f
    let g : (moduleSpecΓFunctor (R := .of O)).obj F →ₗ[CommRingCat.of O]
        (moduleSpecΓFunctor (R := .of O)).obj G :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := fun a s => f.map_smul
          ((Sp O).presheaf.map (TopologicalSpace.Opens.leTop ⊤).op ((Scheme.ΓSpecIso (.of O)).inv a)) s }
    obtain ⟨φ, hφ⟩ := h.2 (ConcreteCategory.ofHom (C := ModuleCat (CommRingCat.of O)) g)
    refine ⟨φ, LinearMap.ext fun s => ?_⟩
    exact congr($hφ s)

section Main

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

abbrev pushO : (Sp O).Modules :=
  (Scheme.Modules.pushforward (TM O M).hom).obj (GlobalTheory.structureModule (TM O M).left)

variable {O M}

theorem pushO_smul (V : (Sp O).Opens) (r : Γ(Sp O, V)) (s : Γ(pushO O M, V)) :
    r • s = ((TM O M).hom.app V r * (show Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ V) from s) :
      Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ V)) := rfl

def toFn {V : (Sp O).Opens} (s : Γ(pushO O M, V)) : Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ V) := s

theorem toFn_add {V : (Sp O).Opens} (s t : Γ(pushO O M, V)) : toFn (s + t) = toFn s + toFn t := rfl
theorem toFn_zero {V : (Sp O).Opens} : toFn (0 : Γ(pushO O M, V)) = 0 := rfl
theorem toFn_smul {V : (Sp O).Opens} (r : Γ(Sp O, V)) (s : Γ(pushO O M, V)) :
    toFn (r • s) = (TM O M).hom.app V r * toFn s := rfl

def ofFn {V : (Sp O).Opens} (x : Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ V)) : Γ(pushO O M, V) := x
theorem ofFn_add {V : (Sp O).Opens} (x y : Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ V)) :
    ofFn (x + y) = ofFn x + ofFn y := rfl

theorem toFn_resM {V V' : (Sp O).Opens} (k : V' ≤ V) (s : Γ(pushO O M, V)) :
    toFn (GlobalTheory.Twist.resM (pushO O M) k s) = resG (TM O M).left ((TM O M).hom.preimage_mono k) (toFn s) :=
  rfl

theorem le_zeroSec_pre (V : (Sp O).Opens) : V ≤ sec (zeroSec O M) ⁻¹ᵁ (TM O M).hom ⁻¹ᵁ V :=
  (le_preimage_iff (sec_hom (zeroSec O M))).2 le_rfl

theorem app_zeroSec_eq (V : (Sp O).Opens) (x : Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ V)) :
    (sec (zeroSec O M)).app _ x = resG (Sp O) ((le_preimage_iff (sec_hom (zeroSec O M))).1 le_rfl)
      ((sec (zeroSec O M)).appLE _ V (le_zeroSec_pre V) x) := by
  rw [GlobalTheory.DualPull.resG_appLE, Scheme.Hom.app_eq_appLE]

def toBase : pushO O M ⟶ GlobalTheory.structureModule (Sp O) :=
  GlobalTheory.LB.homOfLinear (fun V =>
    { toFun := fun s => (sec (zeroSec O M)).appLE _ V (le_zeroSec_pre V) s
      map_add' := fun s t => map_add _ _ _
      map_smul' := fun r s => by
        rw [pushO_smul]
        change (sec (zeroSec O M)).appLE _ V _ ((TM O M).hom.app V r *
          (show Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ V) from s)) = r * _
        rw [map_mul, Scheme.Hom.app_eq_appLE, appLE_base (sec_hom (zeroSec O M)) _ _ le_rfl,
          resG_self] })
    fun {V W} h s => by
      revert s
      intro (s : Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ V))
      change (sec (zeroSec O M)).appLE _ W _ (resG (TM O M).left ((TM O M).hom.preimage_mono h) s) =
        resG (Sp O) h ((sec (zeroSec O M)).appLE _ V _ s)
      rw [GlobalTheory.DualPull.appLE_resG, GlobalTheory.DualPull.resG_appLE]

theorem toBase_app (V : (Sp O).Opens) (s : Γ(pushO O M, V)) :
    (toBase (O := O) (M := M)).app V s = (sec (zeroSec O M)).appLE _ V (le_zeroSec_pre V) s := rfl

end Main

section Deform

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M] {A : Over (Sp O)} [GrpObj A]
  (D : Der A.hom (unitSec A) (pushO O M))

variable (O M A) in

def VanD (D : Der A.hom (unitSec A) (pushO O M)) : Prop :=
  ∀ (W : A.left.Opens) (V : (Sp O).Opens) (h : V ≤ unitSec A ⁻¹ᵁ W) (f : Γ(A.left, W)),
    (toBase (O := O) (M := M)).app V (D.app h f) = 0

variable (hD : VanD O M A D)
include hD

theorem der_mul_der {W : A.left.Opens} {V : (Sp O).Opens} (h : V ≤ unitSec A ⁻¹ᵁ W)
    (f g : Γ(A.left, W)) :
    toFn (D.app h f) * toFn (D.app h g) = 0 :=
  mul_eq_zero_of_zeroSec O M _ _ _ (by rw [app_zeroSec_eq]; exact (congrArg _ (hD _ _ h f)).trans (map_zero _))
    (by rw [app_zeroSec_eq]; exact (congrArg _ (hD _ _ h g)).trans (map_zero _))

def psiM (W : A.left.Opens) : Γ(A.left, W) →+* Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ unitSec A ⁻¹ᵁ W) where
  toFun f := (TM O M).hom.appLE _ _ le_rfl ((unitSec A).appLE W _ le_rfl f) +
    toFn (D.app le_rfl f)
  map_one' := by
    have : D.app (le_refl (unitSec A ⁻¹ᵁ W)) 1 = 0 := by
      simpa using D.app_base (U := ⊤) le_rfl le_top 1
    simp only [map_one, this, toFn_zero, add_zero]
  map_mul' f g := by
    have e := D.app_mul le_rfl f g
    have hm := der_mul_der D hD le_rfl f g
    replace e := congrArg toFn e
    rw [toFn_add, toFn_smul, toFn_smul] at e
    simp only [map_mul]
    rw [e, Scheme.Hom.app_eq_appLE]
    linear_combination -hm
  map_zero' := by simp only [map_zero, toFn_zero, add_zero]
  map_add' f g := by
    simp only [map_add, toFn_add]
    abel

theorem psiM_apply (W : A.left.Opens) (f : Γ(A.left, W)) : psiM D hD W f =
    (TM O M).hom.appLE _ _ le_rfl ((unitSec A).appLE W _ le_rfl f) +
      toFn (D.app le_rfl f) := rfl

theorem psiM_nat (W W' : A.left.Opens) (h : W' ≤ W) (f : Γ(A.left, W)) :
    psiM D hD W' (resG A.left h f) =
      resG (TM O M).left ((TM O M).hom.preimage_mono ((unitSec A).preimage_mono h)) (psiM D hD W f) := by
  rw [psiM_apply, psiM_apply, map_add, D.app_res, ← D.res_app le_rfl ((unitSec A).preimage_mono h),
    toFn_resM, GlobalTheory.DualPull.resG_appLE, GlobalTheory.DualPull.appLE_resG (unitSec A),
    ← GlobalTheory.DualPull.resG_appLE (unitSec A) ((unitSec A).preimage_mono h) le_rfl,
    GlobalTheory.DualPull.appLE_resG (TM O M).hom]

def deformM : (TM O M).left ⟶ A.left :=
  GlobalTheory.KS.DerMorK.deformHom ((TM O M).hom ≫ unitSec A) (psiM D hD) (psiM_nat D hD) fun W f => by
    have h : (((TM O M).hom ≫ unitSec A).app W).hom f =
        (TM O M).hom.appLE _ _ le_rfl ((unitSec A).appLE W _ le_rfl f) := by
      rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app]; rfl
    rw [h]
    have e2 : ∀ a b : Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ unitSec A ⁻¹ᵁ W), (a + b - a) ^ 2 = b * b :=
      fun a b => by ring
    exact ⟨2, (e2 ((TM O M).hom.appLE _ _ le_rfl ((unitSec A).appLE W _ le_rfl f))
      (toFn (D.app le_rfl f))).trans (der_mul_der D hD le_rfl f f)⟩

theorem deformM_base : (deformM D hD).base = ((TM O M).hom ≫ unitSec A).base :=
  GlobalTheory.KS.DerMorK.deformHom_base _ _ _ _

theorem deformM_preimage (W : A.left.Opens) :
    deformM D hD ⁻¹ᵁ W = (TM O M).hom ⁻¹ᵁ unitSec A ⁻¹ᵁ W := rfl

theorem deformM_appLE' (W : A.left.Opens) {U : (TM O M).left.Opens}
    (k : U ≤ deformM D hD ⁻¹ᵁ W) (f : Γ(A.left, W)) :
    (deformM D hD).appLE W U k f = resG (TM O M).left (k.trans (deformM_preimage D hD W).le) (psiM D hD W f) := rfl

attribute [local irreducible] deformM

theorem deformM_comp : deformM D hD ≫ A.hom = (TM O M).hom := by
  have he : unitSec A ≫ A.hom = 𝟙 _ := sec_hom η[A]
  have h₀ : (TM O M).hom ≫ unitSec A ≫ A.hom = (TM O M).hom := by rw [he, Category.comp_id]
  have hb : (deformM D hD ≫ A.hom).base = (TM O M).hom.base := by
    rw [Scheme.Hom.comp_base, deformM_base, ← Scheme.Hom.comp_base, Category.assoc, h₀]
  refine GlobalTheory.KS.DerMorK.hom_ext_appLE hb fun U k => ?_
  ext a
  have k' : (TM O M).hom ⁻¹ᵁ U ≤ (TM O M).hom ⁻¹ᵁ unitSec A ⁻¹ᵁ A.hom ⁻¹ᵁ U :=
    (le_preimage_of_comp h₀).2 le_rfl
  have e1 := (deformM_preimage D hD (A.hom ⁻¹ᵁ U)).ge
  refine (appLE_appLE (f := deformM D hD) rfl le_rfl (k'.trans e1) k a).symm.trans ?_
  rw [deformM_appLE', psiM_apply, D.app_base, toFn_zero, add_zero,
    appLE_base he _ _ ((le_preimage_iff he).1 le_rfl), GlobalTheory.DualPull.appLE_resG,
    GlobalTheory.DualPull.resG_appLE, Scheme.Hom.appLE_eq_app]
theorem zeroSec_psiM {W : A.left.Opens} (k : unitSec A ⁻¹ᵁ W ≤
      sec (zeroSec O M) ⁻¹ᵁ (TM O M).hom ⁻¹ᵁ unitSec A ⁻¹ᵁ W) (f : Γ(A.left, W)) :
    (sec (zeroSec O M)).appLE _ _ k (psiM D hD W f) = (unitSec A).appLE W _ le_rfl f := by
  rw [psiM_apply, map_add, appLE_base (sec_hom (zeroSec O M)) _ _ le_rfl, resG_self]
  have h0 : (sec (zeroSec O M)).appLE _ _ k (toFn (D.app (le_refl (unitSec A ⁻¹ᵁ W)) f)) = 0 :=
    hD _ _ le_rfl f
  rw [h0, add_zero]

theorem zeroSec_deformM : sec (zeroSec O M) ≫ deformM D hD = unitSec A := by
  have hz : sec (zeroSec O M) ≫ (TM O M).hom = 𝟙 _ := sec_hom (zeroSec O M)
  have h₀ : sec (zeroSec O M) ≫ (TM O M).hom ≫ unitSec A = unitSec A := by rw [reassoc_of% hz]
  have hb : (sec (zeroSec O M) ≫ deformM D hD).base = (unitSec A).base := by
    rw [Scheme.Hom.comp_base, deformM_base, ← Scheme.Hom.comp_base, h₀]
  refine GlobalTheory.KS.DerMorK.hom_ext_appLE hb fun W k => ?_
  ext f
  have k' : unitSec A ⁻¹ᵁ W ≤ sec (zeroSec O M) ⁻¹ᵁ (TM O M).hom ⁻¹ᵁ unitSec A ⁻¹ᵁ W :=
    (le_preimage_of_comp h₀).2 le_rfl
  refine (appLE_appLE (f := sec (zeroSec O M)) (g := deformM D hD)
    (V := (TM O M).hom ⁻¹ᵁ unitSec A ⁻¹ᵁ W) rfl (deformM_preimage D hD W).ge k' k f).symm.trans ?_
  rw [deformM_appLE', resG_self, zeroSec_psiM, Scheme.Hom.appLE_eq_app]

def ptM : TM O M ⟶ A := Over.homMk (deformM D hD) (deformM_comp D hD)

theorem zeroSec_ptM : zeroSec O M ≫ ptM D hD = η[A] := by
  ext1
  simp only [Over.comp_left]
  exact zeroSec_deformM D hD

end Deform

section Center

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

def centerFn {W : (TM O M).left.Opens} {V : (Sp O).Opens} (h : V ≤ sec (zeroSec O M) ⁻¹ᵁ W)
    (b : Γ((TM O M).left, W)) : Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ V) :=
  resG (TM O M).left (le_of_le_zeroSec O M h) b -
    (TM O M).hom.appLE _ _ ((TM O M).hom.preimage_mono h) ((sec (zeroSec O M)).appLE W _ le_rfl b)

theorem centerFn_van {W : (TM O M).left.Opens} {V : (Sp O).Opens}
    (h : V ≤ sec (zeroSec O M) ⁻¹ᵁ W) (b : Γ((TM O M).left, W)) :
    (sec (zeroSec O M)).appLE _ V (le_zeroSec_pre V) (centerFn h b) = 0 := by
  rw [centerFn, map_sub, GlobalTheory.DualPull.appLE_resG, appLE_base (sec_hom (zeroSec O M)) _ _ h,
    GlobalTheory.DualPull.resG_appLE, sub_self]

theorem centerFn_app_zero {W : (TM O M).left.Opens} {V : (Sp O).Opens}
    (h : V ≤ sec (zeroSec O M) ⁻¹ᵁ W) (b : Γ((TM O M).left, W)) :
    (sec (zeroSec O M)).app _ (centerFn h b) = 0 := by
  rw [app_zeroSec_eq, centerFn_van, map_zero]

variable (O M) in

def centerDer : Der (TM O M).hom (sec (zeroSec O M)) (pushO O M) where
  app {W V} h := AddMonoidHom.mk' (fun b => ofFn (centerFn h b)) fun a b => by
    rw [← ofFn_add]
    congr 1
    simp only [centerFn, map_add]
    abel
  res_app {W V V'} h h' b := by
    change ofFn (resG (TM O M).left _ (centerFn h b)) = ofFn (centerFn (h'.trans h) b)
    congr 1
  app_res {W W' V} h k b := by
    change ofFn (centerFn h (resG (TM O M).left k b)) =
      ofFn (centerFn (h.trans ((sec (zeroSec O M)).preimage_mono k)) b)
    congr 1
  app_mul {W V} h b c := by
    have hm := mul_eq_zero_of_zeroSec O M _ _ _ (centerFn_app_zero h b) (centerFn_app_zero h c)
    have hp (x : Γ((TM O M).left, W)) : (TM O M).hom.app V ((sec (zeroSec O M)).appLE W V h x) =
        (TM O M).hom.appLE _ _ ((TM O M).hom.preimage_mono h)
          ((sec (zeroSec O M)).appLE W _ le_rfl x) := by
      rw [← GlobalTheory.DualPull.resG_appLE (sec (zeroSec O M)) h le_rfl, Scheme.Hom.app_eq_appLE,
        GlobalTheory.DualPull.appLE_resG]
    change ofFn (centerFn h (b * c)) = ofFn ((TM O M).hom.app V ((sec (zeroSec O M)).appLE W V h b) *
      centerFn h c + (TM O M).hom.app V ((sec (zeroSec O M)).appLE W V h c) * centerFn h b)
    congr 1
    rw [hp, hp]
    simp only [centerFn, map_mul] at hm ⊢
    linear_combination hm
  app_base {W V U} h k a := by
    change ofFn (centerFn h _) = ofFn 0
    congr 1
    rw [centerFn, GlobalTheory.DualPull.resG_appLE,
      appLE_base (sec_hom (zeroSec O M)) le_rfl k
        ((le_preimage_iff (sec_hom (zeroSec O M))).1 ((sec (zeroSec O M)).preimage_mono k)),
      GlobalTheory.DualPull.appLE_resG, sub_self]

theorem toFn_centerDer {W : (TM O M).left.Opens} {V : (Sp O).Opens}
    (h : V ≤ sec (zeroSec O M) ⁻¹ᵁ W) (b : Γ((TM O M).left, W)) :
    toFn ((centerDer O M).app h b) = centerFn h b := rfl

variable (O M) in

def rhoM : conormal (sec (zeroSec O M)) ⟶ pushO O M := (centerDer O M).lift

theorem rhoM_d {W : (TM O M).left.Opens} {V : (Sp O).Opens}
    (h : V ≤ sec (zeroSec O M) ⁻¹ᵁ W) (b : Γ((TM O M).left, W)) :
    (rhoM O M).app V (d (sec_hom (zeroSec O M)) h b) = (centerDer O M).app h b :=
  Der.lift_d (sec_hom (zeroSec O M)) _ h b

theorem rhoM_top (c : Γ(conormal (sec (zeroSec O M)), ⊤)) :
    toTsze O M (toFn ((rhoM O M).app ⊤ c)) = TrivSqZeroExt.inr (kappa O M c) := by
  obtain ⟨b, rfl⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) c
  rw [rhoM_d, toFn_centerDer, kappa_d, centerFn]
  refine (map_sub (toTsze O M) _ _).trans ?_
  have e1 : toTsze O M (resG (TM O M).left (le_of_le_zeroSec O M (isChart O M).le) b) = toTsze O M b := by
    rw [show resG (TM O M).left (le_of_le_zeroSec O M (isChart O M).le) b =
      resG (TM O M).left (le_refl ⊤) b from rfl, resG_self]
  have e2 := toTsze_base O M ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top b)
  have e3 := toO_sec O M b
  erw [e1, e2, e3]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

end Center

section Main2

attribute [local irreducible] deformM

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M] {A : Over (Sp O)} [GrpObj A]

theorem cotMap_ptM_rhoM (D : Der A.hom (unitSec A) (pushO O M)) (hD : VanD O M A D) :
    cotMap (ptM D hD) (zeroSec_ptM D hD) ≫ rhoM O M = (omegaHomEquiv A (pushO O M)).symm D := by
  refine omega_hom_ext fun W f => ?_
  have hW' : unitSec A ⁻¹ᵁ W ≤ sec (zeroSec O M) ⁻¹ᵁ deformM D hD ⁻¹ᵁ W :=
    (le_preimage_of_comp (zeroSec_deformM D hD)).2 le_rfl
  change (rhoM O M).app _ ((cotMap (ptM D hD) (zeroSec_ptM D hD)).app (unitSec A ⁻¹ᵁ W)
    (d (sec_hom η[A]) le_rfl f)) = _
  rw [cotMap_d (ptM D hD) (zeroSec_ptM D hD) _ hW' le_rfl f]
  rw [rhoM_d]
  have e : (omegaHomEquiv A (pushO O M) ((omegaHomEquiv A (pushO O M)).symm D)).app
      (le_refl (unitSec A ⁻¹ᵁ W)) f = D.app le_rfl f := by rw [Equiv.apply_symm_apply]
  rw [omegaHomEquiv_app] at e
  refine Eq.trans ?_ e.symm
  change ofFn (centerFn hW' _) = ofFn (toFn (D.app le_rfl f))
  congr 1
  have e1 : (ptM D hD).left.appLE W (deformM D hD ⁻¹ᵁ W) le_rfl f =
      resG (TM O M).left (deformM_preimage D hD W).le (psiM D hD W f) := deformM_appLE' D hD W le_rfl f
  rw [e1, centerFn, resG_resG, resG_self, GlobalTheory.DualPull.appLE_resG,
    ← GlobalTheory.DualPull.appLE_resG (TM O M).hom hW' le_rfl,
    GlobalTheory.DualPull.resG_appLE, zeroSec_psiM, psiM_apply, Scheme.Hom.appLE_eq_app]
  abel

theorem exists_Phi_eq_of_linearMap : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A],
    (GlobalTheory.LieVB.omega A).IsQuasicoherent → ∀ (M : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (l : Wmod A →ₗ[O] M),
    ∃ (v : TM O M ⟶ A) (h : zeroSec O M ≫ v = η[A]), ∀ w, Phi v h w = l w := by
  intro O _ A _ hqc M _ _ _ _ l
  let ofT : TrivSqZeroExt O M →+* Γ((TM O M).left, (TM O M).hom ⁻¹ᵁ ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt O M))).inv.hom
  have hT (x : TrivSqZeroExt O M) : toTsze O M (ofT x) = x := Iso.inv_hom_id_apply _ _
  let l' : Γ(omega A, ⊤) → M := fun w => l w
  have hl'add (w w' : Γ(omega A, ⊤)) : l' (w + w') = l' w + l' w' := l.map_add w w'
  have hl'smul (a : O) (w : Γ(omega A, ⊤)) : l' (cst O a • w) = a • l' w := l.map_smul a w
  let g : Γ(omega A, ⊤) →ₗ[Γ(Sp O, ⊤)] Γ(pushO O M, ⊤) :=
    { toFun := fun w => ofFn (ofT (TrivSqZeroExt.inr (l' w)))
      map_add' := fun w w' => by
        refine (congrArg (fun m => ofFn (ofT (TrivSqZeroExt.inr m))) (hl'add w w')).trans ?_
        rw [TrivSqZeroExt.inr_add, map_add, ofFn_add]
      map_smul' := fun r w => by
        obtain ⟨a, rfl⟩ : ∃ a, r = cst O a := ⟨toO O r, (Iso.hom_inv_id_apply _ _).symm⟩
        have e : l' (cst O a • w) = a • l' w := hl'smul a w
        rw [RingHom.id_apply]
        change ofFn (ofT (TrivSqZeroExt.inr (l' (cst O a • w)))) =
          ofFn ((TM O M).hom.app ⊤ (cst O a) * ofT (TrivSqZeroExt.inr (l' w)))
        congr 1
        apply (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt O M))).hom).1
        change toTsze O M _ = toTsze O M _
        refine (congrArg (fun m => toTsze O M (ofT (TrivSqZeroExt.inr m))) e).trans ?_
        rw [hT]
        refine Eq.trans ?_ (map_mul (toTsze O M) ((TM O M).hom.app ⊤ (cst O a))
          (ofT (TrivSqZeroExt.inr (l' w)))).symm
        have hb : toTsze O M ((TM O M).hom.app ⊤ (cst O a)) = algebraMap O (TrivSqZeroExt O M) a := by
          rw [Scheme.Hom.app_eq_appLE]
          exact (toTsze_base O M (cst O a)).trans (congrArg _ (Iso.inv_hom_id_apply _ _))
        refine Eq.trans ?_ (congrArg₂ (fun x y : TrivSqZeroExt O M => x * y) hb (hT _)).symm
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl] }
  haveI := hqc
  obtain ⟨φ, hφ⟩ := (appLinear_top_bijective (omega A) (pushO O M)).2 g
  have hφw (w : Γ(omega A, ⊤)) : φ.app ⊤ w = g w := congr($hφ w)
  have hφ0 : φ ≫ toBase = 0 := by
    apply (appLinear_top_bijective (omega A) (GlobalTheory.structureModule (Sp O))).1
    refine LinearMap.ext fun w => ?_
    change toBase.app ⊤ (φ.app ⊤ w) = 0
    rw [hφw, toBase_app]
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).hom).1
    change toO O _ = toO O 0
    rw [map_zero]
    erw [toO_sec O M (ofT (TrivSqZeroExt.inr (l' w)))]
    rw [hT]
    rfl
  let D := omegaHomEquiv A (pushO O M) φ
  have hD : VanD O M A D := fun W V h f => by
    change toBase.app V (D.app h f) = 0
    rw [omegaHomEquiv_app]
    change (φ ≫ toBase).app V _ = 0
    rw [hφ0]
    rfl
  refine ⟨ptM D hD, zeroSec_ptM D hD, fun w => ?_⟩
  have key := cotMap_ptM_rhoM D hD
  rw [Equiv.symm_apply_apply] at key
  have h1 := rhoM_top ((cotMap (ptM D hD) (zeroSec_ptM D hD)).app ⊤ w)
  have h2 : (rhoM O M).app ⊤ ((cotMap (ptM D hD) (zeroSec_ptM D hD)).app ⊤ w) = φ.app ⊤ w := by
    rw [← key]; rfl
  have h3 : toTsze O M (toFn (φ.app ⊤ w)) = TrivSqZeroExt.inr (l w) :=
    (congrArg (fun x => toTsze O M (toFn x)) (hφw w)).trans (hT _)
  rw [Phi_apply]
  exact TrivSqZeroExt.inr_injective (h1.symm.trans ((congrArg (fun x => toTsze O M (toFn x)) h2).trans h3))

end Main2

end GlobalTheory.SqZeroPt
