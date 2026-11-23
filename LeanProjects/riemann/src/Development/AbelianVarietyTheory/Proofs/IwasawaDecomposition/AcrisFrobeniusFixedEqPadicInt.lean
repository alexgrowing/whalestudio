import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBdRPlusSectionOfTheta
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PhiFix

private theorem mem_adjoin_of_mem (l : ℕ) [Fact l.Prime] (s : Per.AinfP l) (hs : s ∈ Per.Acris0 l) :
    s ∈ Algebra.adjoin (Per.Ainf l) {y : Per.AinfP l | ∃ x : Per.Ainf l, Per.θ l x = 0 ∧ ∃ n : ℕ,
      ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n} :=
  GlobalTheory.RingIface.Acris0_le_of_dividedPowers l _
    (fun x n y hx hn => Algebra.subset_adjoin (s := {y : Per.AinfP l | ∃ x : Per.Ainf l, Per.θ l x = 0 ∧ ∃ n : ℕ,
      ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n}) (a := y) ⟨x, hx, n, hn⟩) hs

private theorem padicInt_hom_ext (l : ℕ) [Fact l.Prime] {R : Type} [CommRing R]
    (hH : IsHausdorff (Ideal.span {(l : R)}) R) (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  refine sub_eq_zero.1 (hH.haus _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n z)
  have h1 := congrArg f hy
  have h2 := congrArg g hy
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast] at h1 h2
  exact ⟨f y - g y, by linear_combination h1 - h2⟩

theorem fixed_of_mod (l : ℕ) [Fact l.Prime] {R : Type} [CommRing R] (φ : R →+* R) (f : ℤ_[l] →+* R)
    (hf : ∀ z, φ (f z) = f z) (hH : IsHausdorff (Ideal.span {(l : R)}) R)
    (htf : ∀ x : R, (l : R) * x = 0 → x = 0)
    (hmod : ∀ x : R, φ x = x → ∃ c : ℤ, (l : R) ∣ x - c) (x : R) (hx : φ x = x) :
    ∃ z, x = f z := by
  let S : Subring R := φ.eqLocus (RingHom.id R)
  let g : ℤ_[l] →+* S := f.codRestrict S hf
  have hmap : (Ideal.span {(l : ℤ_[l])}).map g = Ideal.span {(l : S)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  haveI : IsPrecomplete (Ideal.span {(l : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  haveI : IsHausdorff ((Ideal.span {(l : ℤ_[l])}).map g) S := by
    rw [hmap]
    refine ⟨fun y hy => Subtype.ext (hH.haus (y : R) fun n => ?_)⟩
    have h := hy n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h ⊢
    simpa using map_dvd S.subtype h
  have hs : Function.Surjective g := by
    refine surjective_of_mk_map_comp_surjective (I := Ideal.span {(l : ℤ_[l])}) g fun q => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨c, w, hw⟩ := hmod y y.2
    have hy : φ y = y := y.2
    have hw' : φ w = w := by
      have h := congrArg φ hw
      rw [map_sub, map_mul, map_natCast, map_intCast, hy] at h
      exact sub_eq_zero.1 (htf _ (by linear_combination hw - h))
    refine ⟨c, ?_⟩
    rw [RingHom.comp_apply, map_intCast, Ideal.Quotient.eq, hmap, Ideal.mem_span_singleton]
    refine ⟨-⟨w, hw'⟩, Subtype.ext ?_⟩
    push_cast
    linear_combination -hw
  obtain ⟨z, hz⟩ := hs ⟨x, hx⟩
  exact ⟨z, (congrArg Subtype.val hz).symm⟩

variable (l : ℕ) [Fact l.Prime]

theorem exists_pow_pred_div_factorial (n : ℕ) :
    ∃ c : ℤ_[l], (((n + 1).factorial : ℕ) : ℤ_[l]) * c = (l : ℤ_[l]) ^ n := by
  have h0 : (((n + 1).factorial : ℕ) : ℤ_[l]) ≠ 0 := by exact_mod_cast (n + 1).factorial_ne_zero
  have hv : ((((n + 1).factorial : ℕ) : ℤ_[l])).valuation ≤ n := by
    have h := PadicInt.valuation_coe (((n + 1).factorial : ℕ) : ℤ_[l])
    rw [PadicInt.coe_natCast, Padic.valuation_natCast] at h
    have h' : padicValNat l (n + 1).factorial = ((((n + 1).factorial : ℕ) : ℤ_[l])).valuation := by
      exact_mod_cast h
    rw [← h']
    exact Nat.lt_succ_iff.1 (padicValNat_factorial_lt_of_ne_zero l n.succ_ne_zero)
  have hs := PadicInt.unitCoeff_spec h0
  have : (((n + 1).factorial : ℕ) : ℤ_[l]) ∣ (l : ℤ_[l]) ^ n := by
    rw [hs, Units.mul_left_dvd]
    exact pow_dvd_pow _ hv
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc.symm⟩

theorem pow_eq_mul (x : Per.Ainf l) (hx : Per.θ l x = 0) :
    ∃ t ∈ Per.Acris0 l, algebraMap (Per.Ainf l) (Per.AinfP l) x ^ l = (l : Per.AinfP l) * t := by
  obtain ⟨d, hd⟩ := (GlobalTheory.RingBasics.isUnit_nat l l.factorial l.factorial_ne_zero).exists_right_inv
  have hdm : d * algebraMap (Per.Ainf l) (Per.AinfP l) x ^ l ∈ Per.Acris0 l :=
    GlobalTheory.RingIface.dividedPower_mem_Acris0 l x l _ hx (by rw [← mul_assoc, hd, one_mul])
  refine ⟨_, mul_mem (natCast_mem _ (l - 1).factorial) hdm, ?_⟩
  rw [← mul_assoc, ← Nat.cast_mul, Nat.mul_factorial_pred (Fact.out : l.Prime).ne_zero, ← mul_assoc, hd, one_mul]

theorem phi_mod (s : Per.AinfP l) (hs : s ∈ Per.Acris0 l) :
    ∃ a : Per.Ainf l, ∃ t ∈ Per.Acris0 l,
      Per.extP (Per.φA l) s = algebraMap (Per.Ainf l) (Per.AinfP l) a + (l : Per.AinfP l) * t := by
  replace hs := mem_adjoin_of_mem l s hs
  induction hs using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨x, hx, n, hn⟩ := hy
    rcases n with _ | n
    · refine ⟨1, 0, zero_mem _, ?_⟩
      have : y = 1 := by simpa using hn
      simp [this]
    · obtain ⟨z, hz⟩ := GlobalTheory.RingBasics.frob_lift l x
      obtain ⟨t, ht, e⟩ := pow_eq_mul l x hx
      obtain ⟨c, hc⟩ := exists_pow_pred_div_factorial l n
      have hc' := congrArg ((algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)) hc
      rw [map_mul, map_natCast, map_pow, map_natCast] at hc'
      have e1 := congrArg (Per.extP (Per.φA l)) hn
      rw [map_mul, map_natCast, map_pow, GlobalTheory.RingBasics.awayMap_algebraMap₂, hz, map_add, map_pow, e, map_mul, map_natCast,
        ← mul_add, mul_pow, pow_succ (l : Per.AinfP l), ← hc'] at e1
      refine ⟨0, ((algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)) c * (t + algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (n + 1),
        mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (add_mem ht (Subalgebra.algebraMap_mem _ _)) _), ?_⟩
      apply (GlobalTheory.RingBasics.isUnit_nat l (n + 1).factorial (n + 1).factorial_ne_zero).mul_left_cancel
      rw [e1, map_zero]
      ring
  | algebraMap r => exact ⟨Per.φA l r, 0, zero_mem _, by rw [GlobalTheory.RingBasics.awayMap_algebraMap₂]; simp⟩
  | add x y _ _ a b =>
    obtain ⟨a, t, ht, e⟩ := a
    obtain ⟨b, u, hu, e'⟩ := b
    exact ⟨a + b, t + u, add_mem ht hu, by rw [map_add, map_add, e, e']; ring⟩
  | mul x y _ _ a b =>
    obtain ⟨a, t, ht, e⟩ := a
    obtain ⟨b, u, hu, e'⟩ := b
    refine ⟨a * b, algebraMap _ _ a * u + t * algebraMap _ _ b + l * t * u,
      add_mem (add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hu) (mul_mem ht (Subalgebra.algebraMap_mem _ _)))
        (mul_mem (mul_mem (natCast_mem _ _) ht) hu), ?_⟩
    rw [map_mul, map_mul, e, e']
    ring

theorem thetaP_mem (s : Per.AinfP l) (hs : s ∈ Per.Acris0 l) : Per.θP l s ∈ 𝓞_ℂ_[l] := by
  replace hs := mem_adjoin_of_mem l s hs
  induction hs using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨x, hx, n, hn⟩ := hy
    rcases n with _ | n
    · have : y = 1 := by simpa using hn
      rw [this, map_one]
      exact one_mem _
    · have e := congrArg (Per.θP l) hn
      rw [map_mul, map_natCast, map_pow, SecEx.fontaineTheta_algebraMap₂, hx] at e
      have h0 : (((n + 1).factorial : ℕ) : ℂ_[l]) ≠ 0 := by exact_mod_cast (n + 1).factorial_ne_zero
      have : Per.θP l y = 0 := by simpa [h0] using e
      rw [this]
      exact zero_mem _
  | algebraMap r => rw [SecEx.fontaineTheta_algebraMap₂]; exact (Per.θ l r).2
  | add x y _ _ a b => rw [map_add]; exact add_mem a b
  | mul x y _ _ a b => rw [map_mul]; exact mul_mem a b

theorem exists_int_nilpotent (t : Per.OC l) (ht : (l : Per.OC l) ∣ t ^ l - t) :
    ∃ (c : ℤ) (N : ℕ), (l : Per.OC l) ∣ (t + c) ^ N := by
  have hl : (l : IsLocalRing.ResidueField (Per.OC l)) = 0 := by
    rw [← map_natCast (IsLocalRing.residue (Per.OC l)), IsLocalRing.residue_eq_zero_iff]
    exact (Fact.out : ¬ IsUnit (l : Per.OC l))
  haveI : CharP (IsLocalRing.ResidueField (Per.OC l)) l :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 hl
  have h1 : IsLocalRing.residue (Per.OC l) t ^ l = IsLocalRing.residue (Per.OC l) t := by
    have := map_dvd (IsLocalRing.residue (Per.OC l)) ht
    rwa [map_natCast, hl, zero_dvd_iff, map_sub, map_pow, sub_eq_zero] at this
  obtain ⟨n, hn⟩ := (mem_bot_iff_intCast l _).1 ((Subfield.mem_bot_iff_pow_eq_self _ l).2 h1)
  have h2 : ¬ IsUnit (t + ((-n : ℤ) : Per.OC l)) := by
    change _ ∈ IsLocalRing.maximalIdeal (Per.OC l)
    rw [← IsLocalRing.residue_eq_zero_iff, map_add, map_intCast, ← hn]
    simp
  generalize hy : t + ((-n : ℤ) : Per.OC l) = y at h2
  have h3 : ‖(y : ℂ_[l])‖ < 1 := by
    refine lt_of_le_of_ne ((GlobalTheory.RingBasics.mem_OC _).1 y.2) fun h => h2 ?_
    have h0 : (y : ℂ_[l]) ≠ 0 := by
      intro h0
      simp [h0] at h
    exact IsUnit.of_mul_eq_one ⟨(y : ℂ_[l])⁻¹, (GlobalTheory.RingBasics.mem_OC _).2 (by simp [h])⟩
      (Subtype.ext (mul_inv_cancel₀ h0))
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 (GlobalTheory.RingBasics.p_ne_zero (p := l))) h3
  refine ⟨-n, N, ?_⟩
  rw [hy, ← Ideal.mem_span_singleton, ← pow_one (Ideal.span _), GlobalTheory.RingBasics.mem_span_pow_OC]
  push_cast
  rw [norm_pow, pow_one]
  exact hN.le

theorem add_int_eq_zero {R : Type} [CommRing R] (hl : (l : R) = 0) (b : R) (hb : b ^ l = b) (c : ℤ)
    (hn : IsNilpotent (b + c)) : b + c = 0 := by
  have hp : l.Prime := Fact.out
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp b (c : R)
  obtain ⟨k, hk⟩ := Int.prime_dvd_pow_self_sub hp c
  have hc : (c : R) ^ l = c := by
    have := congrArg (Int.cast : ℤ → R) hk
    push_cast at this
    rw [hl, zero_mul] at this
    exact sub_eq_zero.1 this
  rw [hb, hc, hl] at hr
  have h1 : (b + c) ^ (l - 1 + 1) = b + c := by
    rw [Nat.sub_add_cancel hp.one_le, hr]
    ring
  have hu : IsUnit (1 - (b + c) ^ (l - 1)) :=
    (hn.pow_of_pos (by have := hp.two_le; omega)).isUnit_one_sub
  exact hu.mul_right_eq_zero.1 (by linear_combination -h1)

theorem acrisFrobeniusRingHom_algebraMap_envelope (s : Per.Acris0 l) :
    phiA l (algebraMap (Per.Acris0 l) (Per.Acris l) s) = algebraMap (Per.Acris0 l) (Per.Acris l)
      ⟨Per.extP (Per.φA l) s, (GlobalTheory.CrisMaps.phiA_extends l).mem _ s.2⟩ :=
  (GlobalTheory.CrisMaps.phiA_extends l).env s

theorem alg_eq (a : Per.Ainf l) : algebraMap (Per.Ainf l) (Per.Acris l) a =
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

theorem phiA_alg (a : Per.Ainf l) : phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem φA_zA (z : ℤ_[l]) : Per.φA l (Per.zA l z) = Per.zA l z :=
  padicInt_hom_ext l inferInstance ((Per.φA l).comp (Per.zA l)) (Per.zA l) z

theorem fixed_mod (x : Per.Acris l) (hx : phiA l x = x) : ∃ c : ℤ, (l : Per.Acris l) ∣ x - c := by
  obtain ⟨-, -, hd, hdv⟩ := acris_basic l
  obtain ⟨s, z, hs⟩ := hd x 1
  obtain ⟨a, t, ht, e⟩ := phi_mod l s s.2
  have e0 : (⟨Per.extP (Per.φA l) s, (GlobalTheory.CrisMaps.phiA_extends l).mem _ s.2⟩ : Per.Acris0 l) =
      algebraMap (Per.Ainf l) (Per.Acris0 l) a + (l : Per.Acris0 l) * ⟨t, ht⟩ := Subtype.ext (by simpa using e)
  have h1 : x = algebraMap (Per.Ainf l) (Per.Acris l) a + (l : Per.Acris l) *
      (algebraMap (Per.Acris0 l) (Per.Acris l) ⟨t, ht⟩ + phiA l z) := by
    have h := congrArg (phiA l) hs
    rw [hx, map_add, acrisFrobeniusRingHom_algebraMap_envelope, e0, map_add, ← alg_eq, pow_one, map_mul, map_mul, map_natCast,
      map_natCast] at h
    linear_combination h
  generalize algebraMap (Per.Acris0 l) (Per.Acris l) ⟨t, ht⟩ + phiA l z = w at h1
  obtain ⟨v, hv⟩ := GlobalTheory.RingBasics.frob_lift l a
  have h2 : (l : Per.Acris l) ∣ algebraMap (Per.Ainf l) (Per.Acris l) (a ^ l - a) := by
    have h := congrArg (phiA l) h1
    rw [hx, map_add, phiA_alg, hv, map_add, map_mul, map_mul, map_natCast, map_natCast] at h
    refine ⟨w - phiA l w - algebraMap (Per.Ainf l) (Per.Acris l) v, ?_⟩
    rw [map_sub]
    linear_combination h1 - h
  have h3 : (l : Per.OC l) ∣ Per.θ l a ^ l - Per.θ l a := by
    have h := h2
    rw [alg_eq, ← pow_one (l : Per.Acris l), hdv, pow_one] at h
    obtain ⟨q, hq⟩ := h
    have hq' : algebraMap (Per.Ainf l) (Per.AinfP l) (a ^ l - a) = (l : Per.AinfP l) * (q : Per.AinfP l) :=
      congrArg Subtype.val hq
    have h := congrArg (Per.θP l) hq'
    rw [SecEx.fontaineTheta_algebraMap₂, map_mul, map_natCast, map_sub, map_pow] at h
    exact ⟨⟨_, thetaP_mem l q q.2⟩, Subtype.ext h⟩
  obtain ⟨c, N, y, hy⟩ := exists_int_nilpotent l _ h3
  obtain ⟨y, rfl⟩ := SecEx.θ_surjective l y
  obtain ⟨k, hk, ek⟩ := pow_eq_mul l ((a + c) ^ N - l * y) (by
    rw [map_sub, map_pow, map_add, map_intCast, map_mul, map_natCast, hy, sub_self])
  have ek0 : algebraMap (Per.Ainf l) (Per.Acris0 l) ((a + c) ^ N - l * y) ^ l = (l : Per.Acris0 l) * ⟨k, hk⟩ :=
    Subtype.ext ek
  have ek1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) ek0
  rw [map_pow, ← alg_eq, map_mul, map_natCast, map_sub, map_pow, map_add, map_intCast, map_mul,
    map_natCast] at ek1
  let π := Ideal.Quotient.mk (Ideal.span {(l : Per.Acris l)})
  have hπ : ∀ u, π u = 0 ↔ (l : Per.Acris l) ∣ u := fun u => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hl : (l : Per.Acris l ⧸ Ideal.span {(l : Per.Acris l)}) = 0 := by
    rw [← map_natCast π, hπ]
  have h4 := add_int_eq_zero l hl (π (algebraMap (Per.Ainf l) (Per.Acris l) a)) (by
    have := (hπ _).2 h2
    rwa [map_sub, map_pow, map_sub, map_pow, sub_eq_zero] at this) c ⟨N * l, by
    have := congrArg π ek1
    rwa [map_pow, map_sub, map_mul, map_mul, map_natCast, hl, zero_mul, zero_mul, sub_zero, map_pow, map_add,
      map_intCast, ← pow_mul] at this⟩
  refine ⟨-c, (hπ _).1 ?_⟩
  rw [h1, map_sub, map_add, map_mul, map_natCast, hl, map_intCast]
  push_cast
  linear_combination h4

end GlobalTheory.MemLoc.PhiFix

namespace GlobalTheory.MemLoc

theorem phi_fixed_eq_padicInt : ∀ (l : ℕ) [Fact l.Prime], ∀ x : Per.Acris l, phiA l x = x → ∃ z : ℤ_[l], x = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z) :=
  fun l _ x hx => PhiFix.fixed_of_mod l (phiA l) ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l))
    (fun z => (PhiFix.phiA_alg l _).trans (congrArg _ (PhiFix.φA_zA l z)))
    (acris_basic l).1.toIsHausdorff (acris_basic l).2.1 (PhiFix.fixed_mod l) x hx

end GlobalTheory.MemLoc
