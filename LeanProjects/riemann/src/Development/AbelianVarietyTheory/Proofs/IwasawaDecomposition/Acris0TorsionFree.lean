import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.PrincipalCompletion

variable {R : Type} [CommRing R] (a : R)

theorem fg : (Ideal.span {a}).FG := Submodule.fg_span_singleton a

theorem eval_eq_zero_iff (n : ℕ) (x : AdicCompletion (Ideal.span {a}) R) :
    AdicCompletion.eval (Ideal.span {a}) R n x = 0 ↔
      (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ n ∣ x := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (fg a),
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, trivial, by rw [Algebra.smul_def, map_pow]⟩

theorem complete :
    IsAdicComplete (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a})
      (AdicCompletion (Ideal.span {a}) R) := by
  have h := AdicCompletion.isAdicComplete (M := R) (fg a)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {a}) R),
    Ideal.map_span, Set.image_singleton] at h
  exact h

theorem dense (x : AdicCompletion (Ideal.span {a}) R) (r : ℕ) :
    ∃ (s : R) (z : AdicCompletion (Ideal.span {a}) R),
      x = algebraMap R _ s + (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ r * z := by
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {a}) R r x)
  have : AdicCompletion.eval (Ideal.span {a}) R r (x - algebraMap R _ s) = 0 := by
    rw [map_sub, ← hs, sub_eq_zero]
    rfl
  obtain ⟨z, hz⟩ := (eval_eq_zero_iff a r _).1 this
  exact ⟨s, z, by rw [← hz]; ring⟩

theorem dvd_iff (s : R) (r : ℕ) :
    (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ r ∣ algebraMap R _ s ↔ a ^ r ∣ s := by
  rw [← eval_eq_zero_iff]
  have : AdicCompletion.eval (Ideal.span {a}) R r (algebraMap R _ s) = Submodule.Quotient.mk s := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem torsionFree (ha : ∀ s : R, a * s = 0 → s = 0) (x : AdicCompletion (Ideal.span {a}) R)
    (hx : algebraMap R (AdicCompletion (Ideal.span {a}) R) a * x = 0) : x = 0 := by
  refine AdicCompletion.ext fun n => ?_
  change AdicCompletion.eval (Ideal.span {a}) R n x = 0
  rw [eval_eq_zero_iff]
  obtain ⟨s, z, rfl⟩ := dense a x n
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [dvd_iff]
  have h1 : (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ (n + 1) ∣
      algebraMap R _ (a * s) := ⟨-z, by rw [map_mul]; linear_combination hx⟩
  obtain ⟨t, ht⟩ := (dvd_iff a _ _).1 h1
  exact ⟨t, sub_eq_zero.1 (ha _ (by linear_combination ht))⟩

theorem basic (p : ℕ) (R : Type) [CommRing R] (hp : ∀ s : R, (p : R) * s = 0 → s = 0) :
    IsAdicComplete (Ideal.span {(p : AdicCompletion (Ideal.span {(p : R)}) R)}) (AdicCompletion (Ideal.span {(p : R)}) R) ∧
    (∀ x : AdicCompletion (Ideal.span {(p : R)}) R, (p : AdicCompletion (Ideal.span {(p : R)}) R) * x = 0 → x = 0) ∧
    (∀ (x : AdicCompletion (Ideal.span {(p : R)}) R) (r : ℕ), ∃ (s : R) (z : AdicCompletion (Ideal.span {(p : R)}) R),
      x = algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) s + (p : AdicCompletion (Ideal.span {(p : R)}) R) ^ r * z) ∧
    ∀ (s : R) (r : ℕ), (p : AdicCompletion (Ideal.span {(p : R)}) R) ^ r ∣ algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) s ↔ (p : R) ^ r ∣ s := by
  rw [← map_natCast (algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R)) p]
  exact ⟨complete _, torsionFree _ hp, dense _, dvd_iff _⟩

theorem basic_of_equiv_pt (p : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    (hp : ∀ s : R, (p : R) * s = 0 → s = 0)
    (e : A ≃+* AdicCompletion (Ideal.span {(p : R)}) R)
    (he : ∀ s, e (algebraMap R A s) = algebraMap R _ s) :
    IsAdicComplete (Ideal.span {(p : A)}) A ∧
    (∀ x : A, (p : A) * x = 0 → x = 0) ∧
    (∀ (x : A) (r : ℕ), ∃ (s : R) (z : A), x = algebraMap R A s + (p : A) ^ r * z) ∧
    ∀ (s : R) (r : ℕ), (p : A) ^ r ∣ algebraMap R A s ↔ (p : R) ^ r ∣ s := by
  have hpe : e (p : A) = algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) (p : R) := by
    rw [map_natCast, map_natCast]
  refine ⟨?_, fun x hx => ?_, fun x r => ?_, fun s r => ?_⟩
  · have h := complete (p : R)
    rw [← IsAdicComplete.congr_ringEquiv _ e, Ideal.map_span, Set.image_singleton, hpe]
    exact h
  · apply e.injective
    rw [map_zero]
    apply torsionFree _ hp
    rw [← hpe, ← map_mul, hx, map_zero]
  · obtain ⟨s, z, hz⟩ := dense (p : R) (e x) r
    refine ⟨s, e.symm z, e.injective ?_⟩
    rw [map_add, map_mul, map_pow, he, hpe, RingEquiv.apply_symm_apply]
    exact hz
  · rw [← dvd_iff (p : R) s r, ← hpe, ← he, ← map_pow, map_dvd_iff]

end GlobalTheory.PrincipalCompletion

namespace GlobalTheory.MemLoc

theorem acris0_torsionFree (l : ℕ) [Fact l.Prime] (s : Per.Acris0 l)
    (hs : (l : Per.Acris0 l) * s = 0) : s = 0 := by
  have hu : IsUnit (l : Per.AinfP l) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) (l : Per.Ainf l)
    rwa [map_natCast] at this
  have h : (l : Per.AinfP l) * (s : Per.AinfP l) = 0 := by
    simpa using congrArg Subtype.val hs
  exact Subtype.ext ((hu.mul_right_eq_zero).1 h)

theorem acris_basic : ∀ (l : ℕ) [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) ∧ (∀ x : Per.Acris l, (l : Per.Acris l) * x = 0 → x = 0) ∧ (∀ (x : Per.Acris l) (r : ℕ), ∃ (s : Per.Acris0 l) (z : Per.Acris l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z) ∧ ∀ (s : Per.Acris0 l) (r : ℕ), (l : Per.Acris l) ^ r ∣ algebraMap (Per.Acris0 l) (Per.Acris l) s ↔ (l : Per.Acris0 l) ^ r ∣ s :=
  fun l _ => by
    obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
    exact GlobalTheory.PrincipalCompletion.basic_of_equiv_pt l (Per.Acris0 l) (Per.Acris l)
      (acris0_torsionFree l) e he

end GlobalTheory.MemLoc
