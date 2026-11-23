import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TameFrob

open GlobalTheory.BKReal Polynomial IntermediateField

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

theorem finite_Wq : Module.Finite ℤ_[l] (Wq l a) := by
  classical
  have := Fintype.ofFinite (Fq l a)
  exact ⟨⟨Finset.univ.image (WittVector.teichmuller l), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, span_teich]⟩⟩

def iotaO : Wq l a →+* Om l :=
  (algebraMap ↥(unrExt l a).1 (Om l)).comp
    ((algebraMap ↥(OL (unrExt l a)) ↥(unrExt l a).1).comp (thetaW a (unrExt l a)).toRingHom)

theorem iotaO_algebraMap (u : ℤ_[l]) :
    iotaO l a (algebraMap ℤ_[l] (Wq l a) u) = algebraMap ℚ_[l] (Om l) u := by
  simp only [iotaO, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  rfl

theorem iotaO_teich {z : Fq l a} {ω : Om l} (hz : IsTiltOf ω (l ^ a - 1) (Fq.val l a z)) :
    iotaO l a (WittVector.teichmuller l z) = ω := by
  apply (algebraMap (Om l) ℂ_[l]).injective
  have h := congrArg (fun y : OC l => (y : ℂ_[l]))
    (intToOC_thetaW a (unrExt l a) (WittVector.teichmuller l z))
  rw [wA_teich, WittVector.fontaineTheta_teichmuller] at h
  exact h.trans (GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz)

theorem iotaO_mem (w : Wq l a) : iotaO l a w ∈ Kunr l a :=
  ((thetaW a (unrExt l a) w : ↥(unrExt l a).1)).2

theorem iotaO_injective : Function.Injective (iotaO l a) := by
  have := finite_Wq l a
  have hc : Function.Injective ((iotaO l a).comp (algebraMap ℤ_[l] (Wq l a))) := fun u v h => by
    simp only [RingHom.comp_apply, iotaO_algebraMap] at h
    exact Subtype.val_injective ((algebraMap ℚ_[l] (Om l)).injective h)
  refine (RingHom.injective_iff_ker_eq_bot _).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[l]) ?_)
  rw [RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot _).1 hc

def iota : Wq l a →+* ↥(Kunr l a) := (iotaO l a).codRestrict (Kunr l a) (iotaO_mem l a)

@[simp] theorem coe_iota (w : Wq l a) : ((iota l a w : ↥(Kunr l a)) : Om l) = iotaO l a w := rfl

theorem iota_injective : Function.Injective (iota l a) := fun x y h =>
  iotaO_injective l a (by rw [← coe_iota, h, coe_iota])

theorem exists_gen' : ∃ (z : Fq l a) (ω : Om l), IsPrimitiveRoot ω (l ^ a - 1) ∧
    iotaO l a (WittVector.teichmuller l z) = ω := by
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  exact ⟨z, ω, hω, iotaO_teich l a hz⟩

theorem Kunr_le_adjoin {ω : Om l} (hω : IsPrimitiveRoot ω (l ^ a - 1)) : Kunr l a ≤ ℚ_[l]⟮ω⟯ := by
  refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
  have hx : x ^ l ^ a = x := hx
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_mem _
  have h1 := one_lt_pow_l l a
  haveI : NeZero (l ^ a - 1) := ⟨by omega⟩
  have h2 : x ^ (l ^ a - 1) = 1 := mul_right_cancel₀ h0 (by rw [← pow_succ, Nat.sub_add_cancel h1.le, hx, one_mul])
  obtain ⟨k, -, rfl⟩ := hω.eq_pow_of_pow_eq_one h2
  exact pow_mem (mem_adjoin_simple_self _ _) k

theorem exists_frac (y : ↥(Kunr l a)) : ∃ w s : Wq l a, s ≠ 0 ∧ (y : Om l) * iotaO l a s = iotaO l a w := by
  obtain ⟨z, ω, hω, hzω⟩ := exists_gen' l a
  have hy : (y : Om l) ∈ (ℚ_[l]⟮ω⟯).toSubalgebra := Kunr_le_adjoin l a hω y.2
  rw [adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic ω)] at hy
  refine (?_ : ∀ x ∈ Algebra.adjoin ℚ_[l] {ω}, ∃ w s : Wq l a, s ≠ 0 ∧ x * iotaO l a s = iotaO l a w) _ hy
  have hci : Function.Injective ((iotaO l a).comp (algebraMap ℤ_[l] (Wq l a))) := fun u v h => by
    simp only [RingHom.comp_apply, iotaO_algebraMap] at h
    exact Subtype.val_injective ((algebraMap ℚ_[l] (Om l)).injective h)
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨WittVector.teichmuller l z, 1, one_ne_zero, by rw [map_one, mul_one, hx, hzω]⟩
  | algebraMap r =>
    obtain ⟨⟨u, v⟩, huv⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[l]) r
    refine ⟨algebraMap ℤ_[l] (Wq l a) u, algebraMap ℤ_[l] (Wq l a) v, fun h => ?_, ?_⟩
    · have h1 : ((iotaO l a).comp (algebraMap ℤ_[l] (Wq l a))) v = ((iotaO l a).comp (algebraMap ℤ_[l] (Wq l a))) 0 := by
        simp only [RingHom.comp_apply, h, map_zero]
      exact nonZeroDivisors.coe_ne_zero v (hci h1)
    · rw [iotaO_algebraMap, iotaO_algebraMap, ← map_mul]
      exact congrArg (algebraMap ℚ_[l] (Om l)) huv
  | add x y _ _ hx hy =>
    obtain ⟨w1, s1, hs1, h1⟩ := hx
    obtain ⟨w2, s2, hs2, h2⟩ := hy
    refine ⟨w1 * s2 + w2 * s1, s1 * s2, mul_ne_zero hs1 hs2, ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, ← h1, ← h2]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨w1, s1, hs1, h1⟩ := hx
    obtain ⟨w2, s2, hs2, h2⟩ := hy
    refine ⟨w1 * w2, s1 * s2, mul_ne_zero hs1 hs2, ?_⟩
    rw [map_mul, map_mul, ← h1, ← h2]
    ring

def algK : Algebra (Wq l a) ↥(Kunr l a) := (iota l a).toAlgebra

attribute [local instance] algK

theorem algebraMap_K (w : Wq l a) : algebraMap (Wq l a) ↥(Kunr l a) w = iota l a w := rfl

theorem isFractionRing : IsFractionRing (Wq l a) ↥(Kunr l a) where
  map_units s := by
    refine IsUnit.mk0 _ fun h => nonZeroDivisors.coe_ne_zero s (iota_injective l a ?_)
    rw [← algebraMap_K, h, map_zero]
  surj y := by
    obtain ⟨w, s, hs, h⟩ := exists_frac l a y
    exact ⟨⟨w, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩⟩, Subtype.ext (by simpa [algebraMap_K] using h)⟩
  exists_of_eq h := ⟨1, by rw [iota_injective l a h]⟩

end GlobalTheory.TameFrob

namespace GlobalTheory.TameFrob

open GlobalTheory.BKReal Polynomial IntermediateField

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

attribute [local instance] algK isFractionRing

def frobRing : ↥(Kunr l a) →+* Om l :=
  IsFractionRing.lift (g := (iotaO l a).comp (sigma l a).toRingEquiv.toRingHom)
    ((iotaO_injective l a).comp (sigma l a).injective)

theorem frobRing_iota (w : Wq l a) : frobRing l a (iota l a w) = iotaO l a (sigma l a w) :=
  IsFractionRing.lift_algebraMap _ w

def frob : ↥(Kunr l a) →ₐ[ℚ_[l]] Om l where
  toRingHom := frobRing l a
  commutes' r := by
    have h : (frobRing l a).comp (algebraMap ℚ_[l] ↥(Kunr l a)) = algebraMap ℚ_[l] (Om l) := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun u => ?_)
      have h1 : algebraMap ℚ_[l] ↥(Kunr l a) (algebraMap ℤ_[l] ℚ_[l] u) =
          iota l a (algebraMap ℤ_[l] (Wq l a) u) :=
        Subtype.ext (by rw [coe_iota, iotaO_algebraMap]; rfl)
      simp only [RingHom.comp_apply]
      rw [h1, frobRing_iota, AlgEquiv.commutes, iotaO_algebraMap]
      rfl
    exact RingHom.congr_fun h r

theorem frob_root (x : ↥(Kunr l a)) (hx : (x : Om l) ^ l ^ a = x) : frob l a x = (x : Om l) ^ l := by
  obtain ⟨z, ω, hω, hzω⟩ := exists_gen' l a
  rcases eq_or_ne (x : Om l) 0 with h0 | h0
  · rw [show x = 0 from Subtype.ext h0, map_zero, ZeroMemClass.coe_zero, zero_pow hl.out.ne_zero]
  have h1 := one_lt_pow_l l a
  haveI : NeZero (l ^ a - 1) := ⟨by omega⟩
  have h2 : (x : Om l) ^ (l ^ a - 1) = 1 :=
    mul_right_cancel₀ h0 (by rw [← pow_succ, Nat.sub_add_cancel h1.le, hx, one_mul])
  obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one h2
  have hx' : x = iota l a (WittVector.teichmuller l z) ^ k := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, coe_iota, hzω, hk])
  have hs : sigma l a (WittVector.teichmuller l z) = WittVector.teichmuller l z ^ l := by
    simpa using sigma_pow_teich l a 1 z
  rw [hx', map_pow]
  change frobRing l a _ ^ k = _
  rw [frobRing_iota, hs, map_pow, SubmonoidClass.coe_pow, coe_iota, hzω, ← pow_mul, ← pow_mul, mul_comm]

theorem exists_frob : ∃ F : GQ l, ∀ x : Om l, x ^ l ^ a = x → F x = x ^ l := by
  let φ : Om l →ₐ[ℚ_[l]] Om l := (frob l a).liftNormal (Om l)
  refine ⟨AlgEquiv.ofBijective φ φ.normal_bijective, fun x hx => ?_⟩
  have hm : x ∈ Kunr l a := IntermediateField.subset_adjoin _ _ hx
  have h := AlgHom.liftNormal_commutes (frob l a) (Om l) ⟨x, hm⟩
  rw [AlgEquiv.ofBijective_apply]
  exact h.trans (frob_root l a ⟨x, hm⟩ hx)

theorem irreducible_X_pow_add_prime_over_witt (e : ℕ) [NeZero e] : Irreducible (Polynomial.X ^ e + Polynomial.C (l : Wq l a)) := by
  have hP : (Ideal.span {(l : Wq l a)}).IsPrime := by
    rw [← WittVector.ker_constantCoeff]; exact RingHom.ker_isPrime _
  have hmon : (Polynomial.X ^ e + Polynomial.C (l : Wq l a)).Monic := monic_X_pow_add_C _ (NeZero.ne e)
  have hdeg : (Polynomial.X ^ e + Polynomial.C (l : Wq l a)).natDegree = e := natDegree_X_pow_add_C
  have hl0 : (l : Wq l a) ≠ 0 := fun h => by
    have := congrArg (iotaO l a) h
    rw [map_natCast, map_zero] at this
    exact hl.out.ne_zero (by exact_mod_cast this)
  refine Polynomial.IsEisensteinAt.irreducible ⟨?_, ?_, ?_⟩ hP hmon.isPrimitive (by rw [hdeg]; exact Nat.pos_of_ne_zero (NeZero.ne e))
  · rw [hmon.leadingCoeff]
    exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  · intro n hn
    rw [hdeg] at hn
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg hn.ne, zero_add, Polynomial.coeff_C]
    split_ifs
    · exact Ideal.mem_span_singleton_self _
    · exact zero_mem _
  · rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (NeZero.ne e).symm, zero_add, Polynomial.coeff_C_zero, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h1 : (l : Wq l a) * (1 - l * c) = 0 := by linear_combination hc
    have h2 : (l : Wq l a) * c = 1 := by
      have := (mul_eq_zero.1 h1).resolve_left hl0
      linear_combination -this
    have h3 := congrArg WittVector.constantCoeff h2
    rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_one] at h3
    exact zero_ne_one h3

theorem irreducible_K (e : ℕ) [NeZero e] : Irreducible (Polynomial.X ^ e + Polynomial.C (l : ↥(Kunr l a))) := by
  have hmon : (Polynomial.X ^ e + Polynomial.C (l : Wq l a)).Monic := monic_X_pow_add_C _ (NeZero.ne e)
  have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ↥(Kunr l a))).1 (irreducible_X_pow_add_prime_over_witt l a e)
  simpa [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] using h

end GlobalTheory.TameFrob

namespace GlobalTheory.TameFrob

open GlobalTheory.BKReal IntermediateField

theorem exists_cover : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a →
    ∀ (m : ZMod a) (ζ : Om l), ζ ^ e = 1 →
      ∃ g : GQ l, (∀ x : Om l, x ^ l ^ a = x → g x = x ^ l ^ m.val) ∧ g (ϖ.seq 0) = ζ * ϖ.seq 0 := by
  intro l hl a e _ _ ϖ _ m ζ hζ
  obtain ⟨F, hF⟩ := exists_frob l a
  have hroot : ∀ (n : ℕ) (x : Om l), x ^ l ^ a = x → (x ^ l ^ n) ^ l ^ a = x ^ l ^ n := fun n x hx => by
    rw [← pow_mul, mul_comm, pow_mul, hx]
  have hG : ∀ (n : ℕ) (x : Om l), x ^ l ^ a = x → (F ^ n) x = x ^ l ^ n := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      rw [pow_succ', AlgEquiv.mul_apply, ih x hx, hF _ (hroot n x hx), ← pow_mul, ← pow_succ]
  set G₁ := F ^ m.val
  set π := ϖ.seq 0
  have hirr := irreducible_K l a e
  have hmon : (Polynomial.X ^ e + Polynomial.C (l : ↥(Kunr l a))).Monic :=
    Polynomial.monic_X_pow_add_C _ (NeZero.ne e)
  have hmin : ∀ y : Om l, y ^ e = -(l : Om l) →
      minpoly (↥(Kunr l a)) y = Polynomial.X ^ e + Polynomial.C (l : ↥(Kunr l a)) := fun y hy =>
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hy]) hmon).symm
  have h1 : (G₁ π) ^ e = -(l : Om l) := by
    rw [← map_pow, ϖ.seq_zero, map_neg, map_natCast]
  have h2 : (ζ * π) ^ e = -(l : Om l) := by
    rw [mul_pow, hζ, one_mul, ϖ.seq_zero]
  have ho : ζ * π ∈ MulAction.orbit Gal(Om l/↥(Kunr l a)) (G₁ π) :=
    (Normal.minpoly_eq_iff_mem_orbit (Om l)).1 ((hmin _ h2).trans (hmin _ h1).symm)
  obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.1 ho
  refine ⟨τ.restrictScalars ℚ_[l] * G₁, fun x hx => ?_, ?_⟩
  · rw [AlgEquiv.mul_apply, hG _ x hx, AlgEquiv.restrictScalars_apply]
    have hm : x ^ l ^ m.val ∈ Kunr l a := IntermediateField.subset_adjoin _ _ (hroot _ x hx)
    exact τ.commutes ⟨_, hm⟩
  · rw [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
    exact hτ

example : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ (m : ZMod a) (ζ : Om l), ζ ^ e = 1 → ∃ g : GQ l, (∀ x : Om l, x ^ l ^ a = x → g x = x ^ l ^ m.val) ∧ g (ϖ.seq 0) = ζ * ϖ.seq 0 := exists_cover

end GlobalTheory.TameFrob
