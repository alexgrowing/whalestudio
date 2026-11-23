import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.BaseRing

open Polynomial in

theorem etale_of_adjoin_root_of_unity {R B : Type} [CommRing R] [CommRing B] [IsDomain R] [IsDomain B]
    [IsIntegrallyClosed R] [Algebra R B] (hinj : Function.Injective (algebraMap R B)) (x : B)
    (hx : Algebra.adjoin R {x} = ⊤) (n : ℕ) (hn : 0 < n) (h1 : x ^ n = 1) (hu : IsUnit (n : B)) :
    Algebra.Etale R B ∧ Module.Finite R B := by
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hinj
  have hroot : aeval x (X ^ n - C 1 : R[X]) = 0 := by simp [h1]
  have hint : IsIntegral R x := ⟨_, monic_X_pow_sub_C 1 hn.ne', hroot⟩
  let e : AdjoinRoot (minpoly R x) ≃ₐ[R] B :=
    (minpoly.equivAdjoin hint).trans ((Subalgebra.equivOfEq _ _ hx).trans Subalgebra.topEquiv)
  have he : ∀ p : R[X], e (AdjoinRoot.mk _ p) = aeval x p := by
    intro p
    have : e (AdjoinRoot.root _) = x := by
      change ((AdjoinRoot.Minpoly.toAdjoin R x (AdjoinRoot.root _) : Algebra.adjoin R {x}) : B) = x
      simp [AdjoinRoot.Minpoly.toAdjoin]
    rw [← AdjoinRoot.aeval_eq, ← aeval_algHom_apply, this]
  obtain ⟨g, hg⟩ := minpoly.isIntegrallyClosed_dvd hint hroot
  have hd : IsUnit (aeval x (derivative (minpoly R x))) := by
    have h2 := congrArg (fun p => aeval x (derivative p)) hg
    simp only [derivative_mul, map_add, map_mul, minpoly.aeval, zero_mul, add_zero, derivative_sub,
      derivative_X_pow, derivative_C, sub_zero, aeval_C, map_pow, aeval_X, map_natCast] at h2
    have hxu : IsUnit x := IsUnit.of_pow_eq_one h1 hn.ne'
    exact isUnit_of_mul_isUnit_left (h2 ▸ hu.mul (hxu.pow _))
  have het : Algebra.Etale R (AdjoinRoot (minpoly R x)) := by
    apply GlobalTheory.etale_adjoinRoot_of_isUnit_derivative (minpoly.monic hint)
    rw [← he] at hd
    simpa using hd.map e.symm
  have hfin : Module.Finite R (AdjoinRoot (minpoly R x)) := (minpoly.monic hint).finite_adjoinRoot
  exact ⟨.of_equiv e, Module.Finite.equiv e.toLinearEquiv⟩

theorem adjoin_eq_top_of_closure {R R' : Subring ℂ} (h : R ≤ R') (x : R') (G : Set ℂ)
    (hG : R' = Subring.closure G) (hx : ∀ g ∈ G, g ∈ R ∨ g = x) :
    letI := (Subring.inclusion h).toAlgebra
    Algebra.adjoin R {x} = ⊤ := by
  letI := (Subring.inclusion h).toAlgebra
  have key : R' ≤ (Algebra.adjoin R {x}).toSubring.map R'.subtype := by
    conv_lhs => rw [hG]
    rw [Subring.closure_le]
    intro g hg
    rcases hx g hg with h1 | h1
    · exact ⟨algebraMap R R' ⟨g, h1⟩, Subalgebra.algebraMap_mem _ _, rfl⟩
    · exact ⟨x, Algebra.subset_adjoin rfl, h1.symm⟩
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, hz, hzy⟩ := key y.2
  have : z = y := Subtype.ext hzy
  exact this ▸ hz

theorem away_of_closure {R R' : Subring ℂ} (h : R ≤ R') (s : R) (hs : (s : ℂ) ≠ 0)
    (hi : (s : ℂ)⁻¹ ∈ R') (G : Set ℂ)
    (hG : R' = Subring.closure G) (hx : ∀ g ∈ G, g ∈ R ∨ g = (s : ℂ)⁻¹) :
    letI := (Subring.inclusion h).toAlgebra
    IsLocalization.Away s R' := by
  letI := (Subring.inclusion h).toAlgebra
  have key : ∀ z ∈ Subring.closure G, ∃ n : ℕ, z * (s : ℂ) ^ n ∈ R := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem g hg =>
      rcases hx g hg with h1 | h1
      · exact ⟨0, by simpa using h1⟩
      · exact ⟨1, by rw [h1, pow_one, inv_mul_cancel₀ hs]; exact R.one_mem⟩
    | zero => exact ⟨0, by simp⟩
    | one => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨n, hn⟩ := ha
      obtain ⟨m, hm⟩ := hb
      refine ⟨n + m, ?_⟩
      have := R.add_mem (R.mul_mem hn (R.pow_mem s.2 m)) (R.mul_mem hm (R.pow_mem s.2 n))
      convert this using 1
      ring
    | neg a _ ha =>
      obtain ⟨n, hn⟩ := ha
      exact ⟨n, by rw [neg_mul]; exact R.neg_mem hn⟩
    | mul a b _ _ ha hb =>
      obtain ⟨n, hn⟩ := ha
      obtain ⟨m, hm⟩ := hb
      refine ⟨n + m, ?_⟩
      convert R.mul_mem hn hm using 1
      ring
  refine IsLocalization.Away.mk s ?_ ?_ ?_
  · exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hs))
  · intro z
    obtain ⟨n, hn⟩ := key z (hG ▸ z.2)
    exact ⟨n, ⟨_, hn⟩, Subtype.ext (by simp [RingHom.algebraMap_toAlgebra])⟩
  · intro a b hab
    have : a = b := Subring.inclusion_injective h hab
    exact ⟨0, by rw [this]⟩

theorem isIntegrallyClosed_of_div (R : Subring ℂ)
    (h : ∀ x y : R, (y : ℂ) ≠ 0 → IsIntegral R ((x : ℂ) / y) → (x : ℂ) / y ∈ R) : IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro z hz
  have hinj : Function.Injective (Algebra.ofId R ℂ) := Subtype.val_injective
  let φ : FractionRing R →ₐ[R] ℂ := IsFractionRing.liftAlgHom hinj
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  have hy0 : (y : ℂ) ≠ 0 := fun h0 => nonZeroDivisors.ne_zero hy (Subtype.ext h0)
  have e : φ (algebraMap R _ x / algebraMap R _ y) = (x : ℂ) / y := by
    rw [map_div₀, φ.commutes, φ.commutes]; rfl
  have := h x y hy0 (e ▸ hz.map φ)
  refine ⟨⟨_, this⟩, φ.toRingHom.injective ?_⟩
  change φ _ = φ _
  rw [e, φ.commutes]; rfl

theorem exists_int_of_isIntegral (q : ℚ) (h : IsIntegral ℤ (q : ℂ)) : ∃ k : ℤ, (k : ℚ) = q := by
  have : IsIntegral ℤ q := by
    have := (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ) (x := q) (algebraMap ℚ ℂ).injective).mp h
    exact this
  exact IsIntegrallyClosed.algebraMap_eq_of_integral this

theorem isIntegrallyClosed_closure (d : ℕ) (hd : d.Prime) (h4 : d % 4 = 3) (r : ℂ) (hr : r ^ 2 = -(d : ℂ)) :
    IsIntegrallyClosed (Subring.closure {(1 + r) / 2}) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
  have hmC : (d : ℂ) + 1 = 4 * m := by exact_mod_cast hm
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hre : r.re = 0 := by
    have h1 := congrArg Complex.re hr
    have h2 := congrArg Complex.im hr
    simp [pow_two] at h1 h2
    by_contra h0
    have : r.im = 0 := by
      have : r.re * r.im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left h0
    rw [this] at h1
    nlinarith [mul_self_nonneg r.re]
  have hc : starRingEnd ℂ r = -r := by apply Complex.ext <;> simp [hre]
  set w : ℂ := (1 + r) / 2 with hw
  have hw2 : w ^ 2 = w - m := by rw [hw]; linear_combination (1 / 4 : ℂ) * hr - (1 / 4 : ℂ) * hmC
  have hwR : w ∈ Subring.closure {w} := Subring.subset_closure rfl
  have hform : ∀ z ∈ Subring.closure {w}, ∃ a b : ℤ, z = a + b * w := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem g hg => exact ⟨0, 1, by simpa using hg⟩
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨1, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨a', b', rfl⟩ := hy
      exact ⟨a + a', b + b', by push_cast; ring⟩
    | neg x _ hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact ⟨-a, -b, by push_cast; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨a', b', rfl⟩ := hy
      exact ⟨a * a' - b * b' * m, a * b' + a' * b + b * b', by push_cast; linear_combination (b * b' : ℂ) * hw2⟩
  have hwint : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, ?_⟩
    simp [hw2]
  have hRint : Algebra.IsIntegral ℤ (Subring.closure {w}) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, b, hab⟩ := hform x x.2
    have : IsIntegral ℤ (x : ℂ) := by
      rw [hab]
      exact (isIntegral_algebraMap (x := a)).add ((isIntegral_algebraMap (x := b)).mul hwint)
    exact (isIntegral_algHom_iff (Subring.closure {w}).subtype.toIntAlgHom Subtype.val_injective).mp
      (show IsIntegral ℤ ((Subring.closure {w}).subtype.toIntAlgHom x) from this)
  apply isIntegrallyClosed_of_div
  intro x y hy hint
  have hz : IsIntegral ℤ ((x : ℂ) / y) := isIntegral_trans _ hint
  obtain ⟨a, b, hab⟩ := hform x x.2
  obtain ⟨a', b', hab'⟩ := hform y y.2
  have hcw : starRingEnd ℂ w = 1 - w := by
    rw [hw, map_div₀, map_add, hc, map_one, map_ofNat]; ring
  have hN : (y : ℂ) * starRingEnd ℂ y = ((a' ^ 2 + a' * b' + b' ^ 2 * m : ℤ) : ℂ) := by
    rw [hab', map_add, map_mul, hcw, map_intCast, map_intCast]
    push_cast
    linear_combination (-(b' : ℂ) ^ 2) * hw2
  have hcy : starRingEnd ℂ y ≠ 0 := by simpa using hy
  set N : ℤ := a' ^ 2 + a' * b' + b' ^ 2 * m with hNdef
  have hN0 : (N : ℂ) ≠ 0 := hN ▸ mul_ne_zero hy hcy
  obtain ⟨u, v, huv⟩ : ∃ u v : ℚ, (x : ℂ) / y = u + v * w := by
    refine ⟨((a * (a' + b') + b * b' * m : ℤ) : ℚ) / N, ((a' * b - a * b' : ℤ) : ℚ) / N, ?_⟩
    have : (x : ℂ) / y = x * starRingEnd ℂ y / N := by
      rw [← hN]; field_simp
    rw [this, hab, hab', map_add, map_mul, hcw, map_intCast, map_intCast]
    push_cast
    field_simp
    linear_combination (-(b * b' : ℂ)) * hw2
  rw [huv] at hz ⊢
  have hz' : IsIntegral ℤ ((u : ℂ) + v * (1 - w)) := by
    have := hz.map (starRingEnd ℂ).toIntAlgHom
    simpa [hcw] using this
  obtain ⟨t, ht⟩ := exists_int_of_isIntegral (2 * u + v) (by
    have e : ((2 * u + v : ℚ) : ℂ) = (u + v * w) + (u + v * (1 - w)) := by push_cast; ring
    rw [e]; exact hz.add hz')
  obtain ⟨n, hn⟩ := exists_int_of_isIntegral (u ^ 2 + u * v + v ^ 2 * m) (by
    have e : ((u ^ 2 + u * v + v ^ 2 * m : ℚ) : ℂ) = (u + v * w) * (u + v * (1 - w)) := by
      push_cast; linear_combination (v : ℂ) ^ 2 * hw2
    rw [e]; exact hz.mul hz')
  have hmQ : (d : ℚ) + 1 = 4 * m := by exact_mod_cast hm
  have h5 : (d : ℚ) * v ^ 2 = 4 * n - t ^ 2 := by
    rw [hn, ht]; linear_combination v ^ 2 * hmQ
  obtain ⟨j, hj⟩ : ∃ j : ℤ, (j : ℚ) = d * v := by
    have : IsIntegral ℤ ((d : ℚ) * v) := by
      apply IsIntegral.of_pow (n := 2) (by norm_num)
      have e : ((d : ℚ) * v) ^ 2 = algebraMap ℤ ℚ (d * (4 * n - t ^ 2)) := by
        simp only [algebraMap_int_eq, eq_intCast]
        push_cast
        linear_combination (d : ℚ) * h5
      rw [e]
      exact isIntegral_algebraMap
    exact IsIntegrallyClosed.algebraMap_eq_of_integral this
  have hj2 : j ^ 2 = d * (4 * n - t ^ 2) := by
    have : (j : ℚ) ^ 2 = d * (4 * n - t ^ 2) := by rw [hj]; linear_combination (d : ℚ) * h5
    exact_mod_cast this
  obtain ⟨s, hs⟩ : (d : ℤ) ∣ j := (Nat.prime_iff_prime_int.mp hd).dvd_of_dvd_pow ⟨_, hj2⟩
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hv : v = s := by
    apply mul_left_cancel₀ hdQ
    rw [← hj, hs]; push_cast; ring
  have h6 : (d : ℤ) * s ^ 2 = 4 * n - t ^ 2 := by
    rw [hv] at h5; exact_mod_cast h5
  have hmZ : (d : ℤ) + 1 = 4 * m := by exact_mod_cast hm
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ t - s := by
    apply Int.prime_two.dvd_of_dvd_pow (n := 2)
    exact ⟨2 * n - 2 * m * s ^ 2 + s ^ 2 - t * s, by linear_combination h6 - s ^ 2 * hmZ⟩
  have hu : u = k := by
    have : (t : ℚ) - s = 2 * k := by exact_mod_cast hk
    rw [hv] at ht
    linarith
  rw [hu, hv]
  push_cast
  exact Subring.add_mem _ (intCast_mem _ _) (Subring.mul_mem _ (intCast_mem _ _) hwR)

theorem zeta_pow (n : ℕ) (hn : 0 < n) : zeta n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one

theorem zeta_eq_pow {A A' : ℕ} (hA' : 0 < A') (h : A ∣ A') : ∃ k : ℕ, zeta A = zeta A' ^ k := by
  obtain ⟨k, rfl⟩ := h
  have hA : (A : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right hA').ne'
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left hA').ne'
  refine ⟨k, ?_⟩
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem w_mem (S A : ℕ) : (1 + H.rt0) / 2 ∈ RZ H S A := Subring.subset_closure (by simp)

theorem inv_mem (S A : ℕ) : (S : ℂ)⁻¹ ∈ RZ H S A := Subring.subset_closure (by simp)

theorem zeta_mem (S A : ℕ) : zeta A ∈ RZ H S A := Subring.subset_closure (by simp)

theorem RZ_le {S S' A A' : ℕ} (hS' : 0 < S') (hA' : 0 < A') (hS : S ∣ S') (hA : A ∣ A') :
    RZ H S A ≤ RZ H S' A' := by
  refine Subring.closure_le.mpr ?_
  rintro g (rfl | rfl | rfl)
  · exact w_mem H _ _
  · obtain ⟨k, hk⟩ := hS
    have h1 : (S : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right (hk ▸ hS')).ne'
    have h2 : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left (hk ▸ hS')).ne'
    have : (S : ℂ)⁻¹ = k * (S' : ℂ)⁻¹ := by rw [hk]; push_cast; field_simp
    rw [this]
    exact Subring.mul_mem _ (natCast_mem _ _) (inv_mem H _ _)
  · obtain ⟨k, hk⟩ := zeta_eq_pow hA' hA
    rw [hk]
    exact Subring.pow_mem _ (zeta_mem H _ _) _

theorem isIntegrallyClosed_RZ_one {S : ℕ} (hS : 0 < S) : IsIntegrallyClosed (RZ H S 1) := by
  have h0 := isIntegrallyClosed_closure H.d H.d_prime (by have := H.d_mod; omega) H.rt0 H.sqrt_neg_disc_sq
  have hle : Subring.closure {(1 + H.rt0) / 2} ≤ RZ H S 1 :=
    Subring.closure_le.mpr (by rintro g rfl; exact w_mem H _ _)
  have hS0 : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  letI := (Subring.inclusion hle).toAlgebra
  have hloc := away_of_closure hle (S : Subring.closure {(1 + H.rt0) / 2}) (by simpa using hS.ne')
    (by simpa using inv_mem H S 1) _ rfl (by
      rintro g (rfl | rfl | rfl)
      · exact Or.inl (Subring.subset_closure rfl)
      · exact Or.inr (by simp)
      · left
        have := zeta_pow 1 one_pos
        rw [pow_one] at this
        rw [this]
        exact Subring.one_mem _)
  refine isIntegrallyClosed_of_isLocalization (RZ H S 1)
    (Submonoid.powers (S : Subring.closure {(1 + H.rt0) / 2})) ?_
  exact powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hS.ne')

theorem etale_RZ {S A A' e : ℕ} (hS : 0 < S) (hA' : 0 < A') (hA : A ∣ A') (he : A' ∣ S ^ e)
    [IsIntegrallyClosed (RZ H S A)] :
    letI := (Subring.inclusion (RZ_le H hS hA' dvd_rfl hA)).toAlgebra
    Algebra.Etale (RZ H S A) (RZ H S A') ∧ Module.Finite (RZ H S A) (RZ H S A') := by
  letI := (Subring.inclusion (RZ_le H hS hA' dvd_rfl hA)).toAlgebra
  have hS0 : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  refine etale_of_adjoin_root_of_unity (Subring.inclusion_injective _) ⟨zeta A', zeta_mem H S A'⟩
    (adjoin_eq_top_of_closure _ _ _ rfl ?_) A' hA' (Subtype.ext (zeta_pow A' hA')) ?_
  · rintro g (rfl | rfl | rfl)
    · exact Or.inl (w_mem H _ _)
    · exact Or.inl (inv_mem H _ _)
    · exact Or.inr rfl
  · have hu : IsUnit (S : RZ H S A') :=
      IsUnit.of_mul_eq_one ⟨_, inv_mem H S A'⟩ (Subtype.ext (by simp [hS0]))
    exact isUnit_of_dvd_unit (by exact_mod_cast Nat.cast_dvd_cast (α := RZ H S A') he) (hu.pow e)

theorem isIntegrallyClosed_RZ {S A e : ℕ} (hS : 0 < S) (hA : 0 < A) (he : A ∣ S ^ e) :
    IsIntegrallyClosed (RZ H S A) := by
  have := isIntegrallyClosed_RZ_one H hS
  letI := (Subring.inclusion (RZ_le H hS hA dvd_rfl (one_dvd A))).toAlgebra
  have := (etale_RZ H hS hA (one_dvd A) he).1
  exact GlobalTheory.isIntegrallyClosed_of_smooth (RZ H S 1) (RZ H S A)

theorem spMap_finite_etale {R B : Type} [CommRing R] [CommRing B] (b : R →+* B)
    (hinj : Function.Injective b)
    (h : letI := b.toAlgebra; Algebra.Etale R B ∧ Module.Finite R B) :
    IsFinite (spMap b) ∧ Etale (spMap b) ∧ Surjective (spMap b) := by
  have hf : b.Finite := h.2
  have he : b.Etale := h.1
  refine ⟨(IsFinite.SpecMap_iff _).mpr hf, (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he, ⟨?_⟩⟩
  exact hf.to_isIntegral.comap_surjective hinj

theorem spMap_away {R B : Type} [CommRing R] [CommRing B] (b : R →+* B) (s : R)
    (h : letI := b.toAlgebra; IsLocalization.Away s B) :
    IsOpenImmersion (spMap b) ∧ ∀ x : Sp R, x ∈ Set.range (spMap b) ↔ s ∉ x.asIdeal := by
  letI := b.toAlgebra
  refine ⟨IsOpenImmersion.of_isLocalization s, fun x => ?_⟩
  have := PrimeSpectrum.localization_away_comap_range B s
  exact Set.ext_iff.mp this x

theorem isInc_inclusion {R R' : Subring ℂ} (h : R ≤ R') : IsInc R.subtype R'.subtype (Subring.inclusion h) :=
  fun _ => rfl

theorem eq_inclusion {R R' : Subring ℂ} (h : R ≤ R') {b : R →+* R'} (hb : IsInc R.subtype R'.subtype b) :
    b = Subring.inclusion h :=
  RingHom.ext fun x => Subtype.ext (hb x)

theorem away_RZ {S S' A : ℕ} (hS' : 0 < S') (hle : RZ H S A ≤ RZ H S' A) :
    letI := (Subring.inclusion hle).toAlgebra
    IsLocalization.Away (S' : RZ H S A) (RZ H S' A) := by
  refine away_of_closure hle (S' : RZ H S A) (by simpa using hS'.ne')
    (by simpa using inv_mem H S' A) _ rfl ?_
  rintro g (rfl | rfl | rfl)
  · exact Or.inl (w_mem H _ _)
  · exact Or.inr (by simp)
  · exact Or.inl (zeta_mem H _ _)

theorem inclusion_RZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' A A' e : ℕ), 0 < S' → 0 < A' → S ∣ S' → A ∣ A' → (∃ b : RZ H S A →+* RZ H S' A', IsInc (RZ H S A).subtype (RZ H S' A').subtype b) ∧ ∀ b : RZ H S A →+* RZ H S' A', IsInc (RZ H S A).subtype (RZ H S' A').subtype b → (S = S' → A' ∣ S ^ e → IsFinite (spMap b) ∧ Etale (spMap b) ∧ Surjective (spMap b)) ∧ (A = A' → IsOpenImmersion (spMap b) ∧ ∀ x : Sp (RZ H S A), x ∈ Set.range (spMap b) ↔ (S' : RZ H S A) ∉ x.asIdeal) := by
  intro E _ _ _ H S S' A A' e hS' hA' hS hA
  have hle := RZ_le H hS' hA' hS hA
  refine ⟨⟨Subring.inclusion hle, isInc_inclusion hle⟩, fun b hb => ?_⟩
  rw [eq_inclusion hle hb]
  refine ⟨?_, ?_⟩
  · rintro rfl he
    have := isIntegrallyClosed_RZ H hS' (Nat.pos_of_dvd_of_pos hA hA') (hA.trans he)
    exact spMap_finite_etale _ (Subring.inclusion_injective _) (etale_RZ H hS' hA' hA he)
  · rintro rfl
    exact spMap_away _ _ (away_RZ H hS' hle)

end GlobalTheory.BaseRing

end
