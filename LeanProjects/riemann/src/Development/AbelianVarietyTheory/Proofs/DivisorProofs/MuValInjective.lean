import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnits
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.MuTw
variable (q : ℕ) [NeZero q]

instance muModule (A : Type) [CommRing A] : Module (ZMod q) (Additive (rootsOfUnity q A)) :=
  AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      exact (mem_rootsOfUnity q _).1 (Additive.toMul x).2))

theorem smul_eq (A : Type) [CommRing A] (c : ZMod q) (x : Additive (rootsOfUnity q A)) : c • x = c.val • x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul]

def muMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    ULift.{1} (Additive (rootsOfUnity q A)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (Additive (rootsOfUnity q B)) where
  toFun x := ⟨Additive.ofMul (restrictRootsOfUnity f q (Additive.toMul x.down))⟩
  map_add' x y := congrArg ULift.up (congrArg Additive.ofMul (map_mul (restrictRootsOfUnity f q) _ _))
  map_smul' c x := by
    apply ULift.ext
    change Additive.ofMul (restrictRootsOfUnity f q (Additive.toMul (c.down • x.down))) =
      c.down • Additive.ofMul (restrictRootsOfUnity f q (Additive.toMul x.down))
    rw [smul_eq, smul_eq, toMul_nsmul, map_pow, ofMul_pow]

theorem muMap_coe {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : ULift.{1} (Additive (rootsOfUnity q A))) :
    (((Additive.toMul (muMap q f x).down : rootsOfUnity q B) : Bˣ) : B) = f (((Additive.toMul x.down : rootsOfUnity q A) : Aˣ) : A) :=
  restrictRootsOfUnity_coe_apply f _

def muF : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj A := ModuleCat.of _ (ULift.{1} (Additive (rootsOfUnity q A)))
  map f := ModuleCat.ofHom (muMap q f.hom)
  map_id A := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact muMap_coe q _ x
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact muMap_coe q _ x

theorem prim_pow {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one] at h
  exact sub_eq_zero.1 h

def root {A : Type} [CommRing A] (ζ : Prim q A) : rootsOfUnity q A := rootsOfUnity.mkOfPowEq ζ.1 (prim_pow q ζ)

theorem root_coe {A : Type} [CommRing A] (ζ : Prim q A) : (((root q ζ : rootsOfUnity q A) : Aˣ) : A) = ζ.1 := rfl

def etaLin (A : Type) [CommRing A] : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (Additive (rootsOfUnity q A)) :=
  Finsupp.lift _ _ _ (fun ζ => ⟨Additive.ofMul (root q ζ)⟩)

theorem etaLin_single (A : Type) [CommRing A] (ζ : Prim q A) (c : ULift.{1} (ZMod q)) :
    etaLin q A (Finsupp.single ζ c) = ⟨c.down • Additive.ofMul (root q ζ)⟩ := by
  rw [etaLin, Finsupp.lift_apply, Finsupp.sum_single_index]
  · rfl
  · exact zero_smul _ _

theorem root_pow_coe {A : Type} [CommRing A] (ζ : Prim q A) (n : ℕ) :
    ((((root q ζ) ^ n : rootsOfUnity q A) : Aˣ) : A) = ζ.1 ^ n := by
  simp [root_coe]

theorem twRel_le_ker (A : Type) [CommRing A] : twRel q 1 A ≤ LinearMap.ker (etaLin q A) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, etaLin_single]
  rw [sub_eq_zero]
  apply ULift.ext
  change (1 : ZMod q) • Additive.ofMul (root q ξ) = ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q) • Additive.ofMul (root q ζ)
  rw [one_smul, zpow_one, smul_eq, ← ofMul_pow]
  congr 1
  apply Subtype.ext; apply Units.ext
  rw [root_pow_coe, root_coe, h]

def eta : twF q 1 ⟶ muF q where
  app A := ModuleCat.ofHom (Submodule.liftQ _ (etaLin q A) (twRel_le_ker q A))
  naturality A B f := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ c => ?_))
    change etaLin q B (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ c)) = muMap q f.hom (etaLin q A (Finsupp.single ζ c))
    rw [Finsupp.mapDomain_single, etaLin_single, etaLin_single]
    apply ULift.ext
    change c.down • Additive.ofMul (root q (Prim.map f.hom ζ)) =
      (muMap q f.hom (c • ⟨Additive.ofMul (root q ζ)⟩)).down
    rw [map_smul]
    change _ = c.down • (muMap q f.hom ⟨Additive.ofMul (root q ζ)⟩).down
    congr 1
    apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact (muMap_coe q f.hom ⟨Additive.ofMul (root q ζ)⟩).symm

theorem eta_mk (A : CommRingCat.{0}) (ζ : Prim q A) (c : ULift.{1} (ZMod q)) :
    ((eta q).app A).hom (Submodule.Quotient.mk (Finsupp.single ζ c)) = ⟨c.down • Additive.ofMul (root q ζ)⟩ :=
  etaLin_single q A ζ c

abbrev rval {V : Scheme.{0}} (t : ((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj (op V)) : Γ(V, ⊤)ˣ :=
  ((Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(V, ⊤))) t) : rootsOfUnity q Γ(V, ⊤)) : Γ(V, ⊤)ˣ)

theorem rval_map {V W : Scheme.{0}} (g : W ⟶ V) (t : ((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj (op V)) :
    ((rval q (((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).map g.op t) : Γ(W, ⊤)ˣ) : Γ(W, ⊤)) =
      (Scheme.Γ ⋙ forget CommRingCat).map g.op ((rval q t : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) := muMap_coe q _ _

theorem isSheaf : Presheaf.IsSheaf Scheme.etaleTopology.{0} (Scheme.Γ ⋙ muF q) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))), isSheaf_iff_isSheaf_of_type]
  intro U S hS x hx
  have hG := GmSec.isSheaf_gamma S hS
  let v : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => ((rval q (x f hf) : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  have hv : v.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    have := congrArg (fun t => ((rval q t : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤))) (hx g₁ g₂ h₁ h₂ e)
    simp only [rval_map] at this
    exact this
  obtain ⟨a, ha, -⟩ := hG v hv
  have hq : a ^ q = 1 := by
    refine hG.isSeparatedFor.ext (fun V f hf => ?_)
    change (Scheme.Γ.map f.op).hom (a ^ q) = (Scheme.Γ.map f.op).hom 1
    rw [map_pow, map_one]
    have h1 := ha f hf
    change (Scheme.Γ.map f.op).hom a = _ at h1
    rw [h1]
    change ((rval q (x f hf) : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) ^ q = 1
    have hr : rval q (x f hf) ^ q = 1 :=
      (mem_rootsOfUnity q _).1 (Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(V, ⊤))) (x f hf))).2
    rw [← Units.val_pow_eq_pow_val, hr, Units.val_one]
  refine ⟨(ULift.up (Additive.ofMul (rootsOfUnity.mkOfPowEq a hq)) :
    ((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj (op U)), ?_, ?_⟩
  · intro V f hf
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact (rval_map q f _).trans (ha f hf)
  · intro y hy
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    refine hG.isSeparatedFor.ext (fun V f hf => ?_)
    have e1 := congrArg (fun t => ((rval q t : Γ(V, ⊤)ˣ) : Γ(V, ⊤))) (hy f hf)
    simp only [rval_map] at e1
    exact e1.trans (ha f hf).symm

def muS : Shv (ZMod q) := ⟨Scheme.Γ ⋙ muF q, isSheaf q⟩

def etaS : tw q 1 ⟶ muS q := ⟨sheafifyLift Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ (eta q)) (isSheaf q)⟩

theorem etaS_sec (U : Scheme.{0}) (m : (twF q 1).obj Γ(U, ⊤)) :
    Sec.map (etaS q) (ofRings.sec (twF q 1) U m) = ((eta q).app Γ(U, ⊤)).hom m := by
  have h := toSheafify_sheafifyLift Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ (eta q)) (isSheaf q)
  exact congrArg (fun φ => (φ.app (op U)).hom m) h

theorem etaS_res {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 1) U) :
    Sec.map (etaS q) (Sec.res g x) = Sec.res g (Sec.map (etaS q) x) :=
  congrArg (fun φ => φ.hom x) ((etaS q).hom.naturality g.op)

abbrev muVal {U : Scheme.{0}} (y : Sec (muS q) U) : Γ(U, ⊤) :=
  (((Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(U, ⊤))) y) : rootsOfUnity q Γ(U, ⊤)) : Γ(U, ⊤)ˣ) : Γ(U, ⊤))

theorem muVal_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec (muS q) U) : muVal q (Sec.res g y) = g.appTop.hom (muVal q y) :=
  muMap_coe q _ _

theorem muVal_injective (U : Scheme.{0}) : Function.Injective (muVal q (U := U)) := fun y y' h => by
  apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; exact Units.ext h

end GlobalTheory.EtC.MuTw
