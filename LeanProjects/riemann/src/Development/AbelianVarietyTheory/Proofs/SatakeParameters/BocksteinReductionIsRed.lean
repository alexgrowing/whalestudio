import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeftNondeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

noncomputable section

namespace GlobalTheory.EtC.Bock.RedSpec
open GlobalTheory.EtC

variable (Q q : ℕ) [NeZero Q] [NeZero q] (hq : q ∣ Q) (i : ℤ)

abbrev ρ : ULift.{1} (ZMod Q) →+* ULift.{1} (ZMod q) :=
  (ULift.ringEquiv.symm : ZMod q ≃+* ULift.{1} (ZMod q)).toRingHom.comp
    ((ZMod.castHom hq (ZMod q)).comp (ULift.ringEquiv : ULift.{1} (ZMod Q) ≃+* ZMod Q).toRingHom)

def primRed {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), by
    obtain ⟨ξ, h⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q A).2.2.2.2.2 q hq ζ
    rw [← h]; exact ξ.2⟩

theorem primRed_val {A : Type} [CommRing A] (ζ : Prim Q A) : (primRed Q q hq ζ).1 = ζ.1 ^ (Q / q) := rfl

theorem primRed_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (ζ : Prim Q A) :
    Prim.map f (primRed Q q hq ζ) = primRed Q q hq (Prim.map f ζ) :=
  Subtype.ext (map_pow f ζ.1 (Q / q))

abbrev T (q : ℕ) (A : Type) [CommRing A] : Type 1 := (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A

abbrev cl {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (c : ULift.{1} (ZMod q)) : T i q A :=
  Submodule.Quotient.mk (Finsupp.single ζ c)

abbrev Rq (A : CommRingCat.{0}) : ModuleCat.{1} (ULift.{1} (ZMod Q)) :=
  (ModuleCat.restrictScalars.{1} (ρ Q q hq)).obj ((twF q i).obj A)

def gen (A : CommRingCat.{0}) (ζ : Prim Q A) : Rq Q q hq i A := (cl i (primRed Q q hq ζ) 1 : T i q A)

def redFree (A : CommRingCat.{0}) : (Prim Q A →₀ ULift.{1} (ZMod Q)) →ₗ[ULift.{1} (ZMod Q)] Rq Q q hq i A :=
  Finsupp.linearCombination _ (gen Q q hq i A)

theorem redFree_single (A : CommRingCat.{0}) (ζ : Prim Q A) (c : ULift.{1} (ZMod Q)) :
    redFree Q q hq i A (Finsupp.single ζ c) = (cl i (primRed Q q hq ζ) (ρ Q q hq c) : T i q A) := by
  rw [redFree, Finsupp.linearCombination_single]
  show (Submodule.Quotient.mk (ρ Q q hq c • Finsupp.single (primRed Q q hq ζ) 1) : T i q A) = _
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem pow_eq_of_mod {M : Type} [Monoid M] (z : M) (q : ℕ) (hz : z ^ q = 1) (n : ℕ) : z ^ n = z ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, hz, one_pow, one_mul]

theorem twRel_le_ker (A : CommRingCat.{0}) : twRel Q i A ≤ LinearMap.ker (redFree Q q hq i A) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, redFree_single, redFree_single]
  change (cl i (primRed Q q hq ξ) (ρ Q q hq 1) - cl i (primRed Q q hq ζ) (ρ Q q hq (ULift.up ((a ^ i : (ZMod Q)ˣ) : ZMod Q))) : T i q A) = 0
  rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero, map_one]
  let a' : (ZMod q)ˣ := Units.map (ZMod.castHom hq (ZMod q)).toMonoidHom a
  refine Submodule.subset_span ⟨primRed Q q hq ζ, primRed Q q hq ξ, a', ?_, ?_⟩
  · have hz : (ζ.1 ^ (Q / q)) ^ q = 1 := by
      rw [← pow_mul, Nat.div_mul_cancel hq]; exact (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q A).1 ζ
    have hv : (a' : ZMod q).val = (a : ZMod Q).val % q := by
      have : (a' : ZMod q) = (((a : ZMod Q).val : ℕ) : ZMod q) := by
        change ZMod.castHom hq (ZMod q) (a : ZMod Q) = _
        conv_lhs => rw [← ZMod.natCast_zmod_val (a : ZMod Q)]
        rw [map_natCast]
      rw [this, ZMod.val_natCast]
    rw [primRed_val, primRed_val, h, hv, ← pow_eq_of_mod _ q hz, ← pow_mul, ← pow_mul, mul_comm]
  · congr 2
    change ULift.up (ZMod.castHom hq (ZMod q) ((a ^ i : (ZMod Q)ˣ) : ZMod Q)) = ULift.up (((a' ^ i : (ZMod q)ˣ)) : ZMod q)
    rw [show a' ^ i = Units.map (ZMod.castHom hq (ZMod q)).toMonoidHom (a ^ i) from (map_zpow _ a i).symm]
    rfl

def redA (A : CommRingCat.{0}) : (twF Q i).obj A ⟶ Rq Q q hq i A :=
  ModuleCat.ofHom (Y := Rq Q q hq i A) ((twRel Q i A).liftQ (redFree Q q hq i A) (twRel_le_ker Q q hq i A))

theorem redA_cl (A : CommRingCat.{0}) (ζ : Prim Q A) (c : ULift.{1} (ZMod Q)) :
    (redA Q q hq i A).hom (cl i ζ c : T i Q A) = (cl i (primRed Q q hq ζ) (ρ Q q hq c) : T i q A) :=
  redFree_single Q q hq i A ζ c

def redNat : twF Q i ⟶ twF q i ⋙ ModuleCat.restrictScalars.{1} (ρ Q q hq) where
  app A := redA Q q hq i A
  naturality A B f := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ c => ?_))
    change (redA Q q hq i B).hom (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ c)) : T i Q B) =
      ((twF q i).map f).hom ((redA Q q hq i A).hom (cl i ζ c : T i Q A))
    rw [Finsupp.mapDomain_single, redA_cl, redA_cl]
    change _ = (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single (primRed Q q hq ζ) (ρ Q q hq c))) : T i q B)
    rw [Finsupp.mapDomain_single, primRed_map]

end GlobalTheory.EtC.Bock.RedSpec

namespace GlobalTheory.EtC.Bock.RedSpec
open GlobalTheory.EtC

variable (Q q : ℕ) [NeZero Q] [NeZero q] (hq : q ∣ Q) (i : ℤ)

def redPre : Scheme.Γ ⋙ twF Q i ⟶ ((restr (ZMod.castHom hq (ZMod q))).obj (tw q i)).obj :=
  Functor.whiskerLeft Scheme.Γ (redNat Q q hq i) ≫
    Functor.whiskerRight (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) (ModuleCat.restrictScalars.{1} (ρ Q q hq))

def redSh : tw Q i ⟶ (restr (ZMod.castHom hq (ZMod q))).obj (tw q i) :=
  ⟨sheafifyLift Scheme.etaleTopology (redPre Q q hq i) ((restr (ZMod.castHom hq (ZMod q))).obj (tw q i)).property⟩

end GlobalTheory.EtC.Bock.RedSpec
