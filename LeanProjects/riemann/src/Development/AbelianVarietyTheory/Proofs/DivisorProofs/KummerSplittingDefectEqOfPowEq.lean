import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSecOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

noncomputable section

namespace GlobalTheory.EtC.KumPic

section
variable (q : ℕ) [NeZero q]

theorem prim_pow_eq_one {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨r, hr⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hr
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.mp h

def primUnit {A : Type} [CommRing A] (ζ : Prim q A) : Aˣ :=
  Units.ofPowEqOne ζ.1 q (prim_pow_eq_one q ζ) (NeZero.ne q)

theorem primUnit_val {A : Type} [CommRing A] (ζ : Prim q A) : ((primUnit q ζ : Aˣ) : A) = ζ.1 :=
  Units.val_ofPowEqOne _ _ _ _

theorem dv_res (φ : Gm ⟶ (res ℤ (twZ q)).X 0) {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤)))
    (v : (Γ(U, ⊤))ˣ) : Sec.res g (dv q φ U v) = dv q φ V (Units.map g.appTop.hom.toMonoidHom v) := by
  unfold dv
  rw [show ∀ a b : Sec ((res ℤ (twZ q)).X 0) U, Sec.res g (a - b) = Sec.res g a - Sec.res g b from
    fun a b => LinearMap.map_sub _ a b, PicSpec.sec_map_res, PicSpec.unitSec_res, (restrMap _ _).nat, (kumT_spec q).1 V U g v hq]

variable (κ : twZ q ⟶ Gm)
  (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
    Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u)
  (φ : Gm ⟶ (res ℤ (twZ q)).X 0) (hφ : κ ≫ φ = resι ℤ (twZ q))
include hκ hφ

theorem dv_mul_prim {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ) (h : (w : Γ(U, ⊤)) = ζ.1 * v) :
    dv q φ U w = dv q φ U v := by
  have hu := primUnit_val q ζ
  have hw : w = primUnit q ζ * v := Units.ext (by rw [Units.val_mul, hu, h])
  have hk := (kumT_spec q).2 U ζ v w h
  have h1 : Sec.map φ (unitSec (primUnit q ζ)) =
      Sec.map (resι ℤ (twZ q)) (show Sec (twZ q) U from twGen 1 ζ) := by
    rw [← hκ U ζ _ hu, PicSpec.sec_map_comp, hφ]
  have h2 : (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (resGen 1 ζ) =
      Sec.map (resι ℤ (twZ q)) (show Sec (twZ q) U from twGen 1 ζ) :=
    restrMap_spec _ _ U _
  unfold dv
  rw [hk, map_add, h2, hw, PicSpec.unitSec_mul, PicSpec.sec_map_add, h1]
  abel

theorem dv_mul_prim_pow {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : ℕ) :
    ∀ v w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v → dv q φ U w = dv q φ U v := by
  induction a with
  | zero =>
    intro v w h
    rw [pow_zero, one_mul] at h
    rw [Units.ext h]
  | succ a ih =>
    intro v w h
    have h1 : ((primUnit q ζ ^ a * v : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ζ.1 ^ a * v := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, primUnit_val]
    rw [dv_mul_prim q κ hκ φ hφ ζ (primUnit q ζ ^ a * v) w (by rw [h, h1, pow_succ', mul_assoc]), ih v (primUnit q ζ ^ a * v) h1]

end

theorem dv_eq_of_pow_eq : ∀ (q : ℕ) [NeZero q] (κ : twZ q ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u) → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), κ ≫ φ = resι ℤ (twZ q) → ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v' := by
  intro q _ κ hκ φ hφ U hq v v' hvv
  have sep := fun W : Scheme.{0} => (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ ((res ℤ (twZ q)).X 0) W).1
  apply sep U
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map g.appTop.hom
  rw [dv_res q φ g hq, dv_res q φ g hq]
  set x := Units.map g.appTop.hom.toMonoidHom v
  set x' := Units.map g.appTop.hom.toMonoidHom v'
  have hx : x ^ q = x' ^ q := by simp only [x, x', ← map_pow, hvv]
  apply sep V
  have hω : ((x' * x⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hx, inv_pow, mul_inv_cancel, Units.val_one]
  obtain ⟨S₂, hS₂, hP₂⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ _ hω
  refine ⟨S₂, hS₂, fun W h hh => ?_⟩
  obtain ⟨a, ha⟩ := hP₂ W h hh
  rw [dv_res q φ h hqV, dv_res q φ h hqV]
  symm
  apply dv_mul_prim_pow q κ hκ φ hφ (ζ.map h.appTop.hom) a
  change h.appTop.hom (x' : Γ(V, ⊤)) = (h.appTop.hom ζ.1) ^ a * h.appTop.hom (x : Γ(V, ⊤))
  rw [← ha, ← map_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]

end GlobalTheory.EtC.KumPic

end
