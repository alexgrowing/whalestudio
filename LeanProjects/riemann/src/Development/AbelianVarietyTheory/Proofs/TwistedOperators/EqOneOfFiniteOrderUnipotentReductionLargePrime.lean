import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlEqOneOfPowPrimePow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipRed

theorem bc_val {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (g : GL (Fin n) A) :
    (Formalism.UG.bc f g : GL (Fin n) B).val = f.mapMatrix g.val := rfl

theorem eq_one_of_reduction_eq_one {E R k : Type} [Field E] [CommRing R] [CommRing k]
    [Nontrivial k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) {n m : ℕ} (hm : IsUnit (m : k))
    (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S) (hu : u ^ m = 1)
    (hxy : Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x) (hy : Formalism.UG.bc φ y = 1) : u = 1 := by
  have hU : u.val ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have h1 : (u.val - 1) * ∑ j ∈ Finset.range m, u.val ^ j = 0 := by
    rw [mul_geom_sum, hU, sub_self]
  have hj : ∀ j : ℕ, S.subtype.mapMatrix (y.val ^ j)
      = (x⁻¹).val * ι.mapMatrix (u.val ^ j) * x.val := by
    intro j
    have h : Formalism.UG.bc S.subtype (y ^ j) = x⁻¹ * Formalism.UG.bc ι (u ^ j) * x := by
      rw [map_pow, map_pow, hxy]
      simpa using conj_pow (a := x⁻¹) (b := Formalism.UG.bc ι u) (i := j)
    have h' := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul, bc_val, bc_val, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val] at h'
    exact h'
  have hsum : S.subtype.mapMatrix (∑ j ∈ Finset.range m, y.val ^ j)
      = (x⁻¹).val * ι.mapMatrix (∑ j ∈ Finset.range m, u.val ^ j) * x.val := by
    rw [map_sum, map_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hj j
  have hY : φ.mapMatrix y.val = 1 := by
    rw [← bc_val, hy, Units.val_one]
  have hk : φ.mapMatrix (∑ j ∈ Finset.range m, y.val ^ j) = (m : k) • 1 := by
    rw [map_sum]
    simp only [map_pow, hY, one_pow, Finset.sum_const, Finset.card_range]
    rw [Nat.cast_smul_eq_nsmul]
  have hd : (∑ j ∈ Finset.range m, u.val ^ j).det ≠ 0 := by
    intro h0
    have h2 : S.subtype (∑ j ∈ Finset.range m, y.val ^ j).det = 0 := by
      rw [RingHom.map_det, hsum, Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, h0, map_zero,
        mul_zero, zero_mul]
    have h3 : (∑ j ∈ Finset.range m, y.val ^ j).det = 0 := Subtype.ext h2
    have h4 := RingHom.map_det φ (∑ j ∈ Finset.range m, y.val ^ j)
    rw [h3, map_zero, hk, Matrix.det_smul, Matrix.det_one, mul_one] at h4
    exact (hm.pow _).ne_zero h4.symm
  have hunit : IsUnit (∑ j ∈ Finset.range m, u.val ^ j) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hd)
  have h5 : u.val - 1 = 0 := (hunit.mul_left_eq_zero).1 h1
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h5)

theorem eq_one_of_unipotent_reduction :
    ∀ (E R k : Type) [Field E] [NumberField E] [CommRing R] [CommRing k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) (p n : ℕ), p.Prime → CharP k p → Module.finrank ℚ E * n + 1 < p → ∀ (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S), IsOfFinOrder u → Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x → IsNilpotent ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) → u = 1 := by
  intro E R k _ _ _ _ S ι φ p n hp hchar hlt u x y hu hxy hnil
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Units.ext (Subsingleton.elim _ _)
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial k := CharP.nontrivial_of_char_ne_one (R := k) hp.ne_one
  obtain ⟨a, ha⟩ := hnil
  have hpa : (Formalism.UG.bc φ y) ^ (p ^ a) = 1 := by
    apply Units.ext
    have h1 : ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) ^ (p ^ a) = 0 :=
      pow_eq_zero_of_le (Nat.lt_pow_self hp.one_lt).le ha
    rw [sub_pow_char_pow_of_commute p a (Commute.one_right _), one_pow, sub_eq_zero] at h1
    rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu.orderOf_pos.ne' p hp.ne_one
  apply GlobalTheory.BadShare.gl_eq_one_of_pow_prime_pow E n p hp hlt u (a + b)
  refine eq_one_of_reduction_eq_one S ι φ (m := m) ((CharP.isUnit_natCast_iff hp).2 hm)
    _ x (y ^ p ^ (a + b)) ?_ ?_ ?_
  · rw [← pow_mul, pow_add, mul_assoc, ← hbm, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [map_pow, map_pow, hxy]
    simpa using conj_pow (a := x⁻¹) (b := Formalism.UG.bc ι u) (i := p ^ (a + b))
  · rw [map_pow, pow_add, pow_mul, hpa, one_pow]

end GlobalTheory.UnipRed
