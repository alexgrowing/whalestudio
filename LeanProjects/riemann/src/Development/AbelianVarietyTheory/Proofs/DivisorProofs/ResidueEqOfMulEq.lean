import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlong

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmallGlue

variable {B : Type} [CommRing B] (t : B)

def Fib : Subring (B × B) :=
  RingHom.eqLocus ((Ideal.Quotient.mk (Ideal.span {t})).comp (RingHom.fst B B))
    ((Ideal.Quotient.mk (Ideal.span {t})).comp (RingHom.snd B B))

def pr₁ : Fib t →+* B := (RingHom.fst B B).comp (Fib t).subtype

def pr₂ : Fib t →+* B := (RingHom.snd B B).comp (Fib t).subtype

theorem sub_mem (p : Fib t) : pr₂ t p - pr₁ t p ∈ Ideal.span {t} := by
  have h : Ideal.Quotient.mk (Ideal.span {t}) (p : B × B).1 = Ideal.Quotient.mk (Ideal.span {t}) (p : B × B).2 := p.2
  rw [Ideal.Quotient.eq] at h
  have := (Ideal.neg_mem_iff _).2 h
  simpa [pr₁, pr₂, neg_sub] using this

def coef (p : Fib t) : B := (Ideal.mem_span_singleton'.1 (sub_mem t p)).choose

theorem coef_mul (p : Fib t) : coef t p * t = pr₂ t p - pr₁ t p :=
  (Ideal.mem_span_singleton'.1 (sub_mem t p)).choose_spec

variable [IsLocalRing B]

theorem residue_eq_of_mul_eq {t : B} (ht : t ≠ 0) {x x' : B} (h : x * t = x' * t) :
    IsLocalRing.residue B x = IsLocalRing.residue B x' := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  by_contra hu
  have hu' : IsUnit (x - x') := by simpa using (IsLocalRing.mem_maximalIdeal _).not.1 hu |> not_not.1
  apply ht
  have : (x - x') * t = 0 := by rw [sub_mul, h, sub_self]
  exact (hu'.mul_right_eq_zero).1 this

end GlobalTheory.SmallGlue

namespace GlobalTheory.SmallGlue

variable {B : Type} [CommRing B] [IsLocalRing B] {t : B}

theorem residue_pr₂ (htm : t ∈ IsLocalRing.maximalIdeal B) (p : Fib t) :
    IsLocalRing.residue B (pr₂ t p) = IsLocalRing.residue B (pr₁ t p) := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← coef_mul]
  exact Ideal.mul_mem_left _ _ htm

def toDual (htm : t ∈ IsLocalRing.maximalIdeal B) (ht : t ≠ 0) :
    Fib t →+* DualNumber (IsLocalRing.ResidueField B) where
  toFun p := TrivSqZeroExt.inl (IsLocalRing.residue B (pr₁ t p)) +
    TrivSqZeroExt.inr (IsLocalRing.residue B (coef t p))
  map_one' := by
    have h : IsLocalRing.residue B (coef t 1) = IsLocalRing.residue B 0 :=
      residue_eq_of_mul_eq ht (by rw [coef_mul, map_one, map_one, sub_self, zero_mul])
    ext <;> simp [h, pr₁]
  map_mul' p q := by
    have h : IsLocalRing.residue B (coef t (p * q)) =
        IsLocalRing.residue B (pr₂ t p * coef t q + pr₁ t q * coef t p) :=
      residue_eq_of_mul_eq ht (by rw [coef_mul, add_mul, _root_.mul_assoc, _root_.mul_assoc, coef_mul, coef_mul, map_mul, map_mul]; ring)
    ext
    · simp [pr₁]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, h, map_add, map_mul,
        residue_pr₂ htm, zero_add, add_zero, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
  map_zero' := by
    have h : IsLocalRing.residue B (coef t 0) = IsLocalRing.residue B 0 :=
      residue_eq_of_mul_eq ht (by rw [coef_mul, map_zero, map_zero, sub_self, zero_mul])
    ext <;> simp [h, pr₁]
  map_add' p q := by
    have h : IsLocalRing.residue B (coef t (p + q)) = IsLocalRing.residue B (coef t p + coef t q) :=
      residue_eq_of_mul_eq ht (by rw [coef_mul, add_mul, coef_mul, coef_mul, map_add, map_add]; ring)
    ext <;> simp [h, pr₁]

end GlobalTheory.SmallGlue

namespace GlobalTheory.SmallGlue

variable {R B : Type} [CommRing R] [CommRing B]

def alg (s : Sp B ⟶ Sp R) : R →+* B := (Spec.preimage s).hom

theorem spMap_alg (s : Sp B ⟶ Sp R) : spMap (alg s) = s := by
  simp [alg, spMap]

variable (t : B) (s : Sp B ⟶ Sp R)

def diag : R →+* Fib t :=
  (RingHom.prod (alg s) (alg s)).codRestrict (Fib t) (fun _ ↦ rfl)

def base : Sp (Fib t) ⟶ Sp R := spMap (diag t s)

theorem spMap_pr₁_base : spMap (pr₁ t) ≫ base t s = s := by
  rw [base, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact spMap_alg s

theorem spMap_pr₂_base : spMap (pr₂ t) ≫ base t s = s := by
  rw [base, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact spMap_alg s

def inc₁ : Over.mk s ⟶ Over.mk (base t s) := Over.homMk (spMap (pr₁ t)) (spMap_pr₁_base t s)

def inc₂ : Over.mk s ⟶ Over.mk (base t s) := Over.homMk (spMap (pr₂ t)) (spMap_pr₂_base t s)

def red : Over.mk (spMap (Ideal.Quotient.mk (Ideal.span {t})) ≫ s) ⟶ Over.mk s :=
  Over.homMk (spMap (Ideal.Quotient.mk (Ideal.span {t}))) rfl

variable [IsLocalRing B] {t}

def dualPt (htm : t ∈ IsLocalRing.maximalIdeal B) (ht : t ≠ 0) :
    Over.mk (spMap (toDual htm ht) ≫ base t s) ⟶ Over.mk (base t s) :=
  Over.homMk (spMap (toDual htm ht)) rfl

abbrev dnFst (k : Type) [CommRing k] : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

end GlobalTheory.SmallGlue

namespace GlobalTheory.SmallGlue

variable {B : Type} [CommRing B] [IsLocalRing B] {t : B}

end GlobalTheory.SmallGlue

namespace GlobalTheory.SmallGlue

variable {R B : Type} [CommRing R] [CommRing B] [IsLocalRing B] {t : B}

end GlobalTheory.SmallGlue

namespace GlobalTheory.SmallGlue

variable {S : Scheme.{0}} {A : Over S} {T : Over S}

variable [GrpObj A]

end GlobalTheory.SmallGlue
