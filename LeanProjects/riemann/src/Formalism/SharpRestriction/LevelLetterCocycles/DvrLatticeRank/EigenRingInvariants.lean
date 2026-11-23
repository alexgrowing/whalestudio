import Mathlib
import Formalism.PadicSubsetSums.StableGradedCounts.ConcreteDictionaryHolds
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.EigenUniformiser

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries

noncomputable abbrev Ia {O : Type*} [CommRing O] (a : O) : Ideal (PowerSeries O) := Ideal.span {X - C a}

theorem mk_X {O : Type*} [CommRing O] (a : O) : Ideal.Quotient.mk (Ia a) X = Ideal.Quotient.mk (Ia a) (C a) :=
  Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr dvd_rfl)

section Ev

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem map_residue_X_sub_C {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    (X - C a : PowerSeries O).map (IsLocalRing.residue O) = X := by
  rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero, sub_zero]

theorem order_map_X_sub_C {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    ((X - C a : PowerSeries O).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat = 1 := by
  change ((X - C a : PowerSeries O).map (IsLocalRing.residue O)).order.toNat = 1
  rw [map_residue_X_sub_C ha, PowerSeries.order_X]
  rfl

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem ev_exists {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) (f : PowerSeries O) :
    ∃ c : O, Ideal.Quotient.mk (Ia a) f = Ideal.Quotient.mk (Ia a) (C c) := by
  have hg : (X - C a : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    rw [map_residue_X_sub_C ha]
    exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hW⟩ := f.exists_isWeierstrassDivision hg
  obtain ⟨hdeg, heq⟩ := hW
  rw [order_map_X_sub_C ha] at hdeg
  have hr : r = Polynomial.C (r.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (by exact_mod_cast hdeg))
  refine ⟨r.coeff 0, ?_⟩
  rw [heq, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)),
    zero_add]
  congr 1
  conv_lhs => rw [hr]
  exact Polynomial.coe_C _

theorem ev_inj {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) {c c' : O}
    (h : Ideal.Quotient.mk (Ia a) (C c) = Ideal.Quotient.mk (Ia a) (C c')) : c = c' := by
  rw [Ideal.Quotient.eq, ← map_sub] at h
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp h
  have hrec : ∀ n, PowerSeries.coeff (R := O) n H = a * PowerSeries.coeff (R := O) (n + 1) H := by
    intro n
    have hn := congrArg (PowerSeries.coeff (R := O) (n + 1)) hH
    rw [PowerSeries.coeff_C, if_neg (by omega : n + 1 ≠ 0), sub_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul] at hn
    linear_combination -hn
  have hmem : ∀ n, PowerSeries.coeff (R := O) 0 H ∈ (IsLocalRing.maximalIdeal O) ^ n := by
    intro n
    have hpow : PowerSeries.coeff (R := O) 0 H = a ^ n * PowerSeries.coeff (R := O) n H := by
      induction n with
      | zero => simp
      | succ n ih => rw [ih, hrec n, pow_succ]; ring
    rw [hpow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha n)
  have h0 : PowerSeries.coeff (R := O) 0 H = 0 := by
    apply IsHausdorff.haus' (I := IsLocalRing.maximalIdeal O)
    intro n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact hmem n
  have hc := congrArg (PowerSeries.coeff (R := O) 0) hH
  rw [PowerSeries.coeff_zero_C, sub_mul, map_sub, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul, h0,
    mul_zero, sub_zero] at hc
  exact sub_eq_zero.mp hc

theorem ev_zero {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) {c : O}
    (h : Ideal.Quotient.mk (Ia a) (C c) = 0) : c = 0 := by
  exact ev_inj ha (by rw [h, map_zero, map_zero])

end Ev

theorem ev_subst {O : Type*} [CommRing O] {P : PowerSeries O} (hP : constantCoeff P = 0) {a b c : O}
    {F : PowerSeries O}
    (hPb : Ideal.Quotient.mk (Ideal.span {X - C a}) P = Ideal.Quotient.mk (Ideal.span {X - C a}) (C b))
    (hF : Ideal.Quotient.mk (Ideal.span {X - C b}) F = Ideal.Quotient.mk (Ideal.span {X - C b}) (C c)) :
    Ideal.Quotient.mk (Ideal.span {X - C a}) (PowerSeries.subst P F) =
      Ideal.Quotient.mk (Ideal.span {X - C a}) (C c) := by
  have hs : HasSubst P := HasSubst.of_constantCoeff_zero' hP
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton'] at hF
  obtain ⟨k, hk⟩ := hF
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hPb ⊢
  have e : PowerSeries.subst P F - C c = PowerSeries.subst P k * (P - C b) := by
    have := congrArg (PowerSeries.subst P) hk
    rw [subst_mul hs, subst_sub hs, subst_sub hs, subst_X hs, subst_C, subst_C] at this
    exact this.symm
  rw [e]; exact Ideal.mul_mem_left _ _ hPb

section Dvd

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsDomain O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem mk_prod_X_sub_C (a : O) (T : Finset O) :
    Ideal.Quotient.mk (Ia a) (∏ t ∈ T, (X - C t)) = Ideal.Quotient.mk (Ia a) (C (∏ t ∈ T, (a - t))) := by
  simp only [map_prod, map_sub, mk_X]

theorem prod_dvd (T : Finset O) (hT : ∀ t ∈ T, t ∈ IsLocalRing.maximalIdeal O) (f : PowerSeries O)
    (hf : ∀ t ∈ T, Ideal.Quotient.mk (Ia t) f = 0) : (∏ t ∈ T, (X - C t)) ∣ f := by
  classical
  induction T using Finset.induction_on generalizing f with
  | empty => simp
  | @insert t0 T ht0 ih =>
    rw [Finset.prod_insert ht0]
    have h0 : (X - C t0) ∣ f :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (hf t0 (Finset.mem_insert_self _ _)))
    obtain ⟨g, rfl⟩ := h0
    apply mul_dvd_mul_left
    apply ih (fun t ht => hT t (Finset.mem_insert_of_mem ht))
    intro t ht
    have htm := hT t (Finset.mem_insert_of_mem ht)
    obtain ⟨c, hc⟩ := ev_exists htm g
    have hft := hf t (Finset.mem_insert_of_mem ht)
    have key : Ideal.Quotient.mk (Ia t) (C ((t - t0) * c)) = 0 := by
      rw [← hft]
      simp only [map_mul, map_sub, mk_X, hc]
    have hz := ev_zero htm key
    have hne : t - t0 ≠ 0 := sub_ne_zero.mpr (fun h => ht0 (h ▸ ht))
    have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_left hne
    rw [hc, hc0, map_zero, map_zero]

end Dvd

section Order

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem card_le_of_dvd {f v k : PowerSeries O} {s : ℕ} (T : Finset O)
    (hT : ∀ t ∈ T, t ∈ IsLocalRing.maximalIdeal O) (hv : IsUnit v)
    (hf : f.map (IsLocalRing.residue O) = (X ^ s * v).map (IsLocalRing.residue O))
    (hk : f = (∏ t ∈ T, (X - C t)) * k) :
    T.card ≤ s ∧ (T.card = s → IsUnit k) := by
  set κ := IsLocalRing.ResidueField O
  have hprod : (∏ t ∈ T, (X - C t) : PowerSeries O).map (IsLocalRing.residue O) = X ^ T.card := by
    rw [map_prod]
    rw [Finset.prod_congr rfl fun t ht => (map_residue_X_sub_C (hT t ht))]
    rw [Finset.prod_const]
  have e : (X : PowerSeries κ) ^ s * v.map (IsLocalRing.residue O) =
      X ^ T.card * k.map (IsLocalRing.residue O) := by
    rw [← map_X (IsLocalRing.residue O), ← map_pow, ← map_mul, ← hf, hk, map_mul, hprod, map_X]
  have hv' : constantCoeff (v.map (IsLocalRing.residue O)) ≠ 0 := by
    have := (hv.map (PowerSeries.map (IsLocalRing.residue O)))
    rw [isUnit_iff_constantCoeff] at this
    exact this.ne_zero
  have hX : (X : PowerSeries κ) ≠ 0 := X_ne_zero
  by_cases hle : T.card ≤ s
  · refine ⟨hle, fun hcs => ?_⟩
    rw [hcs] at e
    have e2 := mul_left_cancel₀ (pow_ne_zero _ hX) e
    rw [isUnit_iff_constantCoeff]
    by_contra hnu
    apply hv'
    rw [e2, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)]
  · exfalso
    replace hle := not_le.mp hle
    have e2 : (X : PowerSeries κ) ^ s * v.map (IsLocalRing.residue O) =
        X ^ s * (X ^ (T.card - s) * k.map (IsLocalRing.residue O)) := by
      rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle.le]
    have e3 := mul_left_cancel₀ (pow_ne_zero _ hX) e2
    apply hv'
    rw [e3, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), zero_mul]

end Order

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums

variable {l : ℕ} [hl : Fact l.Prime]

theorem bin_mod (ω : ℤ_[l]) : ∃ k : PowerSeries ℤ_[l],
    binomialSeries ℤ_[l] ω = (1 + X) ^ (PadicInt.toZMod ω).val + brk l (l : ℤ_[l]) * k := by
  set n := (PadicInt.toZMod ω).val
  have h1 : ω - (n : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
  obtain ⟨t, ht⟩ := h1
  have hω : ω = (n : ℤ_[l]) + t * l := by rw [ht]; ring
  obtain ⟨m, hm⟩ : X ∣ binomialSeries ℤ_[l] t - 1 := by
    rw [X_dvd_iff, map_sub, binomialSeries_constantCoeff, map_one, sub_self]
  have hs := ConcreteDictionaryLemmas.brk_hasSubst (l := l) (l : ℤ_[l])
  refine ⟨(1 + X) ^ n * subst (brk l (l : ℤ_[l])) m, ?_⟩
  rw [hω, binomialSeries_add, binomialSeries_nat, ← ConcreteDictionaryLemmas.bin_comp t (l : ℤ_[l])]
  have e1 : binomialSeries ℤ_[l] t = 1 + X * m := by rw [← hm]; ring
  have e2 : subst (brk l (l : ℤ_[l])) (1 + X * m : PowerSeries ℤ_[l]) =
      1 + brk l (l : ℤ_[l]) * subst (brk l (l : ℤ_[l])) m := by
    rw [← coe_substAlgHom hs, map_add, map_one, map_mul, coe_substAlgHom, subst_X hs]
  rw [e1, e2]; ring

theorem brk_l : brk l (l : ℤ_[l]) = (1 + X) ^ l - 1 := by
  unfold brk
  rw [PowerSeries.binomialSeries_nat]

section O

variable {O : Type*} [CommRing O] [Algebra ℤ_[l] O] {a ζ : O}

local notation "toO" => PowerSeries.map (algebraMap ℤ_[l] O)

theorem mk_onX (haζ : 1 + a = ζ) : Ideal.Quotient.mk (Ia a) (1 + X) = Ideal.Quotient.mk (Ia a) (C ζ) := by
  simp only [← haζ, map_add, map_one, mk_X]

theorem mk_powX (haζ : 1 + a = ζ) (n : ℕ) :
    Ideal.Quotient.mk (Ia a) ((1 + X) ^ n) = Ideal.Quotient.mk (Ia a) (C (ζ ^ n)) := by
  simp only [map_pow, mk_onX haζ]

theorem toO_N : toO (brk l (l : ℤ_[l])) = (1 + X) ^ l - 1 := by
  rw [brk_l]
  simp

theorem mk_N (haζ : 1 + a = ζ) (hζ : IsPrimitiveRoot ζ l) :
    Ideal.Quotient.mk (Ia a) (toO (brk l (l : ℤ_[l]))) = 0 := by
  rw [toO_N, map_sub, mk_powX haζ, hζ.pow_eq_one]
  simp

theorem mk_bin (haζ : 1 + a = ζ) (hζ : IsPrimitiveRoot ζ l) (ω : ℤ_[l]) :
    Ideal.Quotient.mk (Ia a) (toO (binomialSeries ℤ_[l] ω)) =
      Ideal.Quotient.mk (Ia a) (C (ζ ^ (PadicInt.toZMod ω).val)) := by
  obtain ⟨k, hk⟩ := bin_mod (l := l) ω
  have h1 : toO ((1 + X : PowerSeries ℤ_[l]) ^ (PadicInt.toZMod ω).val) = (1 + X) ^ (PadicInt.toZMod ω).val := by
    simp
  rw [hk, map_add, map_mul, h1, map_add, map_mul, mk_N haζ hζ, zero_mul, add_zero]
  exact mk_powX haζ _

theorem mk_brk (haζ : 1 + a = ζ) (hζ : IsPrimitiveRoot ζ l) (ω : ℤ_[l]) :
    Ideal.Quotient.mk (Ia a) (toO (brk l ω)) =
      Ideal.Quotient.mk (Ia a) (C (ζ ^ (PadicInt.toZMod ω).val - 1)) := by
  unfold brk
  rw [map_sub, map_sub, mk_bin haζ hζ ω]
  simp

theorem mk_prod_brk (haζ : 1 + a = ζ) (hζ : IsPrimitiveRoot ζ l) (S : Finset ℤ_[l]) :
    Ideal.Quotient.mk (Ia a) (toO (∏ ω ∈ S, brk l ω)) =
      Ideal.Quotient.mk (Ia a) (C (∏ ω ∈ S, (ζ ^ (PadicInt.toZMod ω).val - 1))) := by
  simp only [map_prod]
  exact Finset.prod_congr rfl (fun ω _ => mk_brk haζ hζ ω)

end O

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums Classical

variable {l : ℕ} [hl : Fact l.Prime]

theorem isUnit_of_toZMod_ne_zero {x : ℤ_[l]} (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal x).mpr (mem_nonunits_iff.mpr hx)
  rw [← PadicInt.ker_toZMod] at hm
  exact RingHom.mem_ker.mp hm

theorem natCast_ne_zero_zmod {n : ℕ} (h0 : 0 < n) (hn : n < l) : (n : ZMod l) ≠ 0 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt h0 hn ((CharP.cast_eq_zero_iff (ZMod l) l n).mp h)

theorem isUnit_natCast {n : ℕ} (h0 : 0 < n) (hn : n < l) : IsUnit (n : ℤ_[l]) := by
  apply isUnit_of_toZMod_ne_zero
  rw [map_natCast]
  exact natCast_ne_zero_zmod h0 hn

theorem toZMod_ne_zero_of_pow {s : ℕ} (hs : 0 < s) {ω : ℤ_[l]} (hω : ω ^ s = 1) :
    PadicInt.toZMod ω ≠ 0 := by
  intro h
  have h1 := congrArg PadicInt.toZMod hω
  rw [map_pow, h, zero_pow hs.ne', map_one] at h1
  exact zero_ne_one h1

theorem val_pos_of_pow {s : ℕ} (hs : 0 < s) {ω : ℤ_[l]} (hω : ω ^ s = 1) :
    0 < (PadicInt.toZMod ω).val := by
  exact ZMod.val_pos.mpr (toZMod_ne_zero_of_pow hs hω)

theorem val_lt (ω : ℤ_[l]) : (PadicInt.toZMod ω).val < l := ZMod.val_lt _

theorem toZMod_injOn {s : ℕ} (hs : 0 < s) (hsl : s < l) {δ ε : ℤ_[l]} (hδ : δ ^ s = 1)
    (hε : ε ^ s = 1) (h : PadicInt.toZMod δ = PadicInt.toZMod ε) : δ = ε := by
  have e := geom_sum₂_mul δ ε s
  rw [hδ, hε, sub_self] at e
  have hS : IsUnit (∑ i ∈ Finset.range s, δ ^ i * ε ^ (s - 1 - i)) := by
    apply isUnit_of_toZMod_ne_zero
    rw [map_sum]
    have : ∀ i ∈ Finset.range s, PadicInt.toZMod (δ ^ i * ε ^ (s - 1 - i)) =
        PadicInt.toZMod δ ^ (s - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, ← h, ← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_ne_zero (natCast_ne_zero_zmod hs hsl) (pow_ne_zero _ (toZMod_ne_zero_of_pow hs hδ))
  exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hS.ne_zero)

theorem natCast_l_ne_zero {O : Type*} [CommRing O] [IsDomain O] {ζ : O} (hζ : IsPrimitiveRoot ζ l) :
    ((l : ℕ) : O) ≠ 0 := by
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  exact (hζ.neZero').out

theorem algebraMap_injective {O : Type*} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    (hl0 : ((l : ℕ) : O) ≠ 0) : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  have hu := (PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[l] O)
  rcases mul_eq_zero.mp hx with h | h
  · exact hu.ne_zero h
  · exact absurd h (pow_ne_zero _ hl0)

theorem sub_one_mem {O : Type*} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {ζ : O}
    (hζ : IsPrimitiveRoot ζ l) (hmax : (algebraMap ℤ_[l] O) l ∈ IsLocalRing.maximalIdeal O) :
    ζ - 1 ∈ IsLocalRing.maximalIdeal O := by
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), ← map_natCast (algebraMap ℤ_[l] O)]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  have : CharP (IsLocalRing.ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl.out).mpr hl0
  have h2 : (IsLocalRing.residue O (ζ - 1)) ^ l = 0 := by
    rw [map_sub, map_one, sub_pow_char, ← map_pow, hζ.pow_eq_one, map_one, one_pow, sub_self]
  exact (IsLocalRing.residue_eq_zero_iff _).mp ((pow_eq_zero_iff hl.out.ne_zero).mp h2)

theorem pow_sub_one_mem {O : Type*} [CommRing O] [IsLocalRing O] {ζ : O}
    (h : ζ - 1 ∈ IsLocalRing.maximalIdeal O) (n : ℕ) : ζ ^ n - 1 ∈ IsLocalRing.maximalIdeal O := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow ζ 1 n
  rw [one_pow] at hc
  rw [hc]
  exact Ideal.mul_mem_right _ _ h

noncomputable instance instFintypeRoots (s : ℕ) [NeZero s] : Fintype (rootsOfUnity s ℤ_[l]) := Fintype.ofFinite _

theorem prod_roots {M : Type*} [CommMonoid M] (s : ℕ) [NeZero s] (hs : 0 < s) (f : ℤ_[l] → M) :
    ∏ δ : rootsOfUnity s ℤ_[l], f ((δ : ℤ_[l]ˣ) : ℤ_[l]) =
      ∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]), f ω := by
  rw [← Finset.prod_image (f := f) (s := Finset.univ)
    (g := fun δ : rootsOfUnity s ℤ_[l] => ((δ : ℤ_[l]ˣ) : ℤ_[l]))
    (by intro δ _ ε _ h; exact Subtype.ext (Units.ext h))]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Polynomial.mem_nthRootsFinset hs]
  constructor
  · rintro ⟨δ, rfl⟩
    have h1 := δ.2
    rw [mem_rootsOfUnity] at h1
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  · intro hx
    have hu : IsUnit x := IsUnit.of_pow_eq_one hx hs.ne'
    refine ⟨⟨hu.unit, ?_⟩, rfl⟩
    rw [mem_rootsOfUnity]; apply Units.ext; simp [hx]

section Act

variable {O : Type*} [CommRing O] [Algebra ℤ_[l] O]

local notation "toO" => PowerSeries.map (algebraMap ℤ_[l] O)

theorem toO_const_zero {a : PowerSeries ℤ_[l]} (ha : constantCoeff a = 0) : constantCoeff (toO a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, ha, map_zero]

theorem toO_brk_const (a : ℤ_[l]) : constantCoeff (toO (brk l a)) = 0 :=
  toO_const_zero (by rw [(Classical.choose_spec (ConcreteDictionaryLemmas.brk_factor a)).1, map_mul, constantCoeff_X, zero_mul])

theorem hasSubst_brk (a : ℤ_[l]) : HasSubst (toO (brk l a)) :=
  HasSubst.of_constantCoeff_zero (toO_brk_const a)

theorem toO_subst {a : PowerSeries ℤ_[l]} (ha : constantCoeff a = 0) (f : PowerSeries ℤ_[l]) :
    toO (subst a f) = subst (toO a) (toO f) :=
  map_subst (HasSubst.of_constantCoeff_zero' ha) f

theorem subst_brk_brk (a b : ℤ_[l]) (f : PowerSeries O) :
    subst (toO (brk l b)) (subst (toO (brk l a)) f) = subst (toO (brk l (a * b))) f := by
  rw [subst_comp_subst_apply (hasSubst_brk a) (hasSubst_brk b),
    ← toO_subst (ConcreteDictionaryLemmas.brk_const b), ConcreteDictionaryLemmas.brk_comp]

theorem brk_one : brk l (1 : ℤ_[l]) = X := by
  unfold brk
  rw [← Nat.cast_one, PowerSeries.binomialSeries_nat, pow_one, add_sub_cancel_left]

theorem subst_brk_one (f : PowerSeries O) : subst (toO (brk l 1)) f = f := by
  rw [brk_one, map_X, X_subst]

noncomputable def rhoE (δ : ℤ_[l]ˣ) : PowerSeries O ≃ₐ[O] PowerSeries O :=
  AlgEquiv.ofAlgHom (substAlgHom (hasSubst_brk (O := O) (δ : ℤ_[l])))
    (substAlgHom (hasSubst_brk (O := O) ((δ⁻¹ : ℤ_[l]ˣ) : ℤ_[l])))
    (AlgHom.ext fun f => by
      simp only [AlgHom.comp_apply, coe_substAlgHom, AlgHom.id_apply]
      rw [subst_brk_brk, ← Units.val_mul, inv_mul_cancel, Units.val_one, subst_brk_one])
    (AlgHom.ext fun f => by
      simp only [AlgHom.comp_apply, coe_substAlgHom, AlgHom.id_apply]
      rw [subst_brk_brk, ← Units.val_mul, mul_inv_cancel, Units.val_one, subst_brk_one])

theorem rhoE_apply (δ : ℤ_[l]ˣ) (f : PowerSeries O) : rhoE δ f = subst (toO (brk l δ)) f := by
  exact congrFun (coe_substAlgHom (hasSubst_brk (O := O) (δ : ℤ_[l]))) f

noncomputable def rhoHom (s : ℕ) : rootsOfUnity s ℤ_[l] →* (PowerSeries O ≃ₐ[O] PowerSeries O) where
  toFun δ := rhoE (δ : ℤ_[l]ˣ)
  map_one' := AlgEquiv.ext fun f => by
    rw [rhoE_apply]; simp only [OneMemClass.coe_one, Units.val_one, subst_brk_one, AlgEquiv.one_apply]
  map_mul' δ ε := AlgEquiv.ext fun f => by
    simp only [AlgEquiv.mul_apply, rhoE_apply, subst_brk_brk]
    congr 3
    simp only [MulMemClass.coe_mul, Units.val_mul]
    ring

theorem rhoHom_apply (s : ℕ) (δ : rootsOfUnity s ℤ_[l]) (f : PowerSeries O) :
    rhoHom s δ f = subst (toO (brk l ((δ : ℤ_[l]ˣ) : ℤ_[l]))) f :=
  rhoE_apply _ f

noncomputable def vS (a : ℤ_[l]) : PowerSeries ℤ_[l] := Classical.choose (ConcreteDictionaryLemmas.brk_factor a)

theorem brk_eq_X_mul (a : ℤ_[l]) : brk l a = X * vS a :=
  (Classical.choose_spec (ConcreteDictionaryLemmas.brk_factor a)).1

theorem vS_const (a : ℤ_[l]) : constantCoeff (vS a) = a :=
  (Classical.choose_spec (ConcreteDictionaryLemmas.brk_factor a)).2

variable [IsDomain O]

noncomputable def dataS (s : ℕ) [NeZero s] (hinj : Function.Injective (algebraMap ℤ_[l] O)) :
    EigenUniformiser.Data O (rootsOfUnity s ℤ_[l]) where
  ρ := rhoHom s
  ω := (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (rootsOfUnity s ℤ_[l]).subtype
  hω := by
    intro δ ε h
    apply Subtype.ext; apply Units.ext
    have h2 := congrArg Units.val h
    exact hinj h2
  v δ := toO (vS ((δ : ℤ_[l]ˣ) : ℤ_[l]))
  hv δ := by
    show rhoHom s δ X = _
    rw [rhoHom_apply, subst_X (hasSubst_brk _), brk_eq_X_mul, map_mul, map_X]
  hv0 δ := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, vS_const]
    rfl

theorem piPrime_dataS (s : ℕ) [NeZero s] (hs : 0 < s) (hinj : Function.Injective (algebraMap ℤ_[l] O)) :
    EigenUniformiser.piPrime (dataS s hinj) = toO (piP l s) := by
  unfold EigenUniformiser.piPrime
  have h1 : ∀ δ, (dataS s hinj).ρ δ X = toO (brk l ((δ : ℤ_[l]ˣ) : ℤ_[l])) := fun δ => by
    show rhoHom s δ X = _
    rw [rhoHom_apply, subst_X (hasSubst_brk _)]
  simp_rw [h1]
  rw [piP, map_prod]
  exact prod_roots s hs (fun ω => toO (brk l ω))

theorem card_roots {s e : ℕ} [NeZero s] (hes : e * s = l - 1) : Fintype.card (rootsOfUnity s ℤ_[l]) = s := by
  obtain ⟨ω₀, hω₀⟩ := ConcreteDictionaryLemmas.exists_prim (l := l) e s hes
  rw [← Nat.card_eq_fintype_card]
  exact hω₀.card_rootsOfUnity

theorem isUnit_card {s e : ℕ} [NeZero s] (hes : e * s = l - 1) :
    IsUnit ((Fintype.card (rootsOfUnity s ℤ_[l]) : ℕ) : O) := by
  have hl2 := hl.out.two_le
  have hs0 : s ≠ 0 := NeZero.ne s
  have he0 : e ≠ 0 := by
    rintro rfl
    omega
  have hse : s ≤ e * s := Nat.le_mul_of_pos_left s (Nat.pos_of_ne_zero he0)
  have hsl : s < l := by
    generalize e * s = q at hes hse
    omega
  rw [card_roots hes]
  have hu := (isUnit_natCast (l := l) (Nat.pos_of_ne_zero hs0) hsl).map (algebraMap ℤ_[l] O)
  rwa [map_natCast] at hu

end Act

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums Classical

variable {l : ℕ} [hl : Fact l.Prime]

theorem s_bounds {s e : ℕ} (hes : e * s = l - 1) : 0 < s ∧ s < l := by
  have hl2 := hl.out.two_le
  have hs0 : s ≠ 0 := by
    rintro rfl
    omega
  have he0 : e ≠ 0 := by
    rintro rfl
    omega
  have hse : s ≤ e * s := Nat.le_mul_of_pos_left s (Nat.pos_of_ne_zero he0)
  refine ⟨Nat.pos_of_ne_zero hs0, ?_⟩
  generalize e * s = q at hes hse
  omega

theorem card_roots_finset {s e : ℕ} (hes : e * s = l - 1) :
    (Polynomial.nthRootsFinset s (1 : ℤ_[l])).card = s := by
  obtain ⟨ω₀, hω₀⟩ := ConcreteDictionaryLemmas.exists_prim (l := l) e s hes
  exact hω₀.card_nthRootsFinset

theorem X_mul_geom : (X : PowerSeries ℤ_[l]) * ∑ j ∈ Finset.range l, (1 + X) ^ j = brk l (l : ℤ_[l]) := by
  rw [brk_l, ← geom_sum_mul, add_sub_cancel_left, mul_comm]

section Fiber

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra ℤ_[l] O]

local notation "toO" => PowerSeries.map (algebraMap ℤ_[l] O)

noncomputable def vp (l s : ℕ) [Fact l.Prime] (ζ : O) : O :=
  ∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]), (ζ ^ (PadicInt.toZMod ω).val - 1)

noncomputable def PRt (l : ℕ) (O : Type*) [CommRing O] [IsDomain O] : Finset O :=
  (Polynomial.nthRoots l (1 : O)).toFinset.filter fun z => IsPrimitiveRoot z l

theorem mem_PRt {z : O} : z ∈ PRt l O ↔ IsPrimitiveRoot z l := by
  simp only [PRt, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_nthRoots hl.out.pos]
  exact ⟨fun h => h.2, fun h => ⟨h.pow_eq_one, h⟩⟩

theorem coprime_val {s : ℕ} (hs : 0 < s) {δ : ℤ_[l]} (hδ : δ ^ s = 1) :
    (PadicInt.toZMod δ).val.Coprime l :=
  ((Nat.Prime.coprime_iff_not_dvd hl.out).mpr
    (Nat.not_dvd_of_pos_of_lt (val_pos_of_pow hs hδ) (val_lt δ))).symm

theorem pow_eq_pow_val {ζ : O} (hζ : IsPrimitiveRoot ζ l) (n : ℕ) :
    ζ ^ n = ζ ^ ((n : ZMod l).val) := by
  conv_lhs => rw [← Nat.mod_add_div n l]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one, ZMod.val_natCast]

theorem vp_pow {s : ℕ} (hs : 0 < s) {ζ : O} (hζ : IsPrimitiveRoot ζ l) {δ : ℤ_[l]} (hδ : δ ^ s = 1) :
    vp l s (ζ ^ (PadicInt.toZMod δ).val) = vp l s ζ := by
  have : NeZero l := ⟨hl.out.ne_zero⟩
  unfold vp
  have key : ∀ ω : ℤ_[l], (ζ ^ (PadicInt.toZMod δ).val) ^ (PadicInt.toZMod ω).val =
      ζ ^ (PadicInt.toZMod (δ * ω)).val := by
    intro ω
    rw [← pow_mul, pow_eq_pow_val hζ, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      map_mul]
  simp_rw [key]
  have hμ : ∀ ω, ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]) ↔ ω ^ s = 1 := fun ω =>
    Polynomial.mem_nthRootsFinset hs 1
  have h02 : δ * δ ^ (s - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hs, hδ]
  refine Finset.prod_nbij' (fun ω => δ * ω) (fun ω => δ ^ (s - 1) * ω) ?_ ?_ ?_ ?_ ?_
  · intro ω hω; rw [hμ] at hω ⊢; rw [mul_pow, hω, hδ, one_mul]
  · intro ω hω
    rw [hμ] at hω ⊢
    rw [mul_pow, hω, ← pow_mul, mul_comm (s - 1) s, pow_mul, hδ, one_pow, one_mul]
  · intro ω _; rw [← mul_assoc, mul_comm (δ ^ (s - 1)) δ, h02, one_mul]
  · intro ω _; rw [← mul_assoc, h02, one_mul]
  · intro ω _; rfl

theorem mk_P {s : ℕ} {ζ : O} (hζ : IsPrimitiveRoot ζ l) :
    Ideal.Quotient.mk (Ia (ζ - 1)) (toO (piP l s)) = Ideal.Quotient.mk (Ia (ζ - 1)) (C (vp l s ζ)) := by
  unfold piP vp
  exact mk_prod_brk (by ring) hζ _

theorem vp_mem {s e : ℕ} (hes : e * s = l - 1) {ζ : O} (hζ : IsPrimitiveRoot ζ l)
    (hmax : (algebraMap ℤ_[l] O) l ∈ IsLocalRing.maximalIdeal O) :
    vp l s ζ ∈ IsLocalRing.maximalIdeal O := by
  haveI : Fact (1 < l) := ⟨hl.out.one_lt⟩
  have hs0 := (s_bounds hes).1
  have h1 : (1 : ℤ_[l]) ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]) :=
    (Polynomial.mem_nthRootsFinset hs0 (1 : ℤ_[l])).mpr (one_pow _)
  unfold vp
  rw [← Finset.mul_prod_erase _ _ h1]
  apply Ideal.mul_mem_right
  rw [map_one, ZMod.val_one, pow_one]
  exact sub_one_mem hζ hmax

theorem vp_ne_zero {s e : ℕ} (hes : e * s = l - 1) {ζ : O} (hζ : IsPrimitiveRoot ζ l) :
    vp l s ζ ≠ 0 := by
  have hs0 := (s_bounds hes).1
  unfold vp
  rw [Finset.prod_ne_zero_iff]
  intro ω hω
  have hω' : ω ^ s = 1 := (Polynomial.mem_nthRootsFinset hs0 (1 : ℤ_[l])).mp hω
  exact sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt (val_pos_of_pow hs0 hω').ne' (val_lt ω))

noncomputable def Tp (l s : ℕ) [Fact l.Prime] (ζ : O) : Finset O :=
  (Polynomial.nthRootsFinset s (1 : ℤ_[l])).image fun δ => ζ ^ (PadicInt.toZMod δ).val - 1

theorem card_Tp {s e : ℕ} (hes : e * s = l - 1) {ζ : O} (hζ : IsPrimitiveRoot ζ l) :
    (Tp l s ζ).card = s := by
  have : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨hs, hsl⟩ := s_bounds hes
  unfold Tp
  rw [Finset.card_image_of_injOn, card_roots_finset hes]
  intro δ hδ ε hε h
  simp only [Finset.mem_coe, Polynomial.mem_nthRootsFinset hs] at hδ hε
  have h1 : ζ ^ (PadicInt.toZMod δ).val = ζ ^ (PadicInt.toZMod ε).val := sub_left_injective h
  exact toZMod_injOn hs hsl hδ hε (ZMod.val_injective _ (hζ.pow_inj (val_lt δ) (val_lt ε) h1))

theorem Tp_sub_PRt {s e : ℕ} (hes : e * s = l - 1) {ζ : O} (hζ : IsPrimitiveRoot ζ l) :
    Tp l s ζ ⊆ ((PRt l O).filter fun z => vp l s z = vp l s ζ).image (fun z => z - 1) := by
  have hs := (s_bounds hes).1
  intro t ht
  unfold Tp at ht
  obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp ht
  rw [Polynomial.mem_nthRootsFinset hs] at hδ
  refine Finset.mem_image.mpr ⟨ζ ^ (PadicInt.toZMod δ).val, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · exact mem_PRt.mpr (hζ.pow_of_coprime _ (coprime_val hs hδ))
  · exact vp_pow hs hζ hδ

theorem exists_isUnit_map_residue_eq_X_pow_mul {s e : ℕ} (hes : e * s = l - 1) {b : O} (hb : b ∈ IsLocalRing.maximalIdeal O) :
    ∃ v : PowerSeries O, IsUnit v ∧ (toO (piP l s) - C b).map (IsLocalRing.residue O) =
      (X ^ s * v).map (IsLocalRing.residue O) := by
  obtain ⟨ε, hε⟩ := (concrete_dictionary_holds l e s hes 0 _ X_mul_geom).2.1
  refine ⟨toO ε, ε.isUnit.map _, ?_⟩
  rw [hε, map_sub, map_C, (IsLocalRing.residue_eq_zero_iff b).mpr hb, map_zero, sub_zero, map_mul,
    map_pow, map_X, mul_comm]

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem fiber_factor {s e : ℕ} (hes : e * s = l - 1) {r : O} (hr : r ∈ IsLocalRing.maximalIdeal O)
    (U : Finset O) (hU : ∀ t ∈ U, t ∈ IsLocalRing.maximalIdeal O)
    (hUr : ∀ t ∈ U, Ideal.Quotient.mk (Ia t) (toO (piP l s) - C r) = 0) (hcard : s ≤ U.card) :
    U.card = s ∧ ∃ k, IsUnit k ∧ toO (piP l s) - C r = (∏ t ∈ U, (X - C t)) * k := by
  obtain ⟨k, hk⟩ := prod_dvd U hU _ hUr
  obtain ⟨v, hv, hf⟩ := exists_isUnit_map_residue_eq_X_pow_mul hes hr
  have h := card_le_of_dvd U hU hv hf hk
  have hc : U.card = s := le_antisymm h.1 hcard
  exact ⟨hc, k, h.2 hc, hk⟩

theorem geom_eq_prod {ζ0 : O} (hζ0 : IsPrimitiveRoot ζ0 l) :
    toO (∑ j ∈ Finset.range l, (1 + X : PowerSeries ℤ_[l]) ^ j) = ∏ ζ ∈ PRt l O, (X - C (ζ - 1)) := by
  have h1 := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ0
  rw [Polynomial.cyclotomic_prime] at h1
  have h2 := congrArg (Polynomial.aeval (1 + X : PowerSeries O)) h1
  have hC : ∀ μ : O, algebraMap O (PowerSeries O) μ = C μ := fun μ => rfl
  simp only [map_sum, map_pow, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hC] at h2
  have hPR : PRt l O = primitiveRoots l O := by
    ext z
    rw [mem_primitiveRoots hl.out.pos, mem_PRt]
  rw [hPR]
  simp only [map_sum, map_pow, map_add, map_one, map_X]
  rw [h2]
  refine Finset.prod_congr rfl fun μ _ => ?_
  rw [map_sub C, map_one]
  ring

theorem E_core {s e : ℕ} (hes : e * s = l - 1) {ζ0 : O} (hζ0 : IsPrimitiveRoot ζ0 l)
    (hmax : (algebraMap ℤ_[l] O) l ∈ IsLocalRing.maximalIdeal O) :
    ∃ w, IsUnit w ∧ ∏ r ∈ (PRt l O).image (vp l s), (toO (piP l s) - C r) =
      toO (∑ j ∈ Finset.range l, (1 + X : PowerSeries ℤ_[l]) ^ j) * w := by
  set R := (PRt l O).image (vp l s)
  have H : ∀ r ∈ R, ∃ k, IsUnit k ∧ toO (piP l s) - C r =
      (∏ ζ ∈ (PRt l O).filter (fun z => vp l s z = r), (X - C (ζ - 1))) * k := by
    intro r hr
    obtain ⟨ζ1, hζ1, rfl⟩ := Finset.mem_image.mp hr
    have hp1 := mem_PRt.mp hζ1
    set U := ((PRt l O).filter fun z => vp l s z = vp l s ζ1).image (fun z => z - 1)
    have hU : ∀ t ∈ U, t ∈ IsLocalRing.maximalIdeal O := by
      intro t ht
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
      exact sub_one_mem (mem_PRt.mp (Finset.mem_filter.mp hz).1) hmax
    have hUr : ∀ t ∈ U, Ideal.Quotient.mk (Ia t) (toO (piP l s) - C (vp l s ζ1)) = 0 := by
      intro t ht
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
      rw [map_sub, mk_P (mem_PRt.mp hz1), hz2, sub_self]
    have hcard : s ≤ U.card := by
      rw [← card_Tp hes hp1]; exact Finset.card_le_card (Tp_sub_PRt hes hp1)
    obtain ⟨-, k, hk, hk'⟩ := fiber_factor hes (vp_mem hes hp1 hmax) U hU hUr hcard
    refine ⟨k, hk, ?_⟩
    rw [hk', Finset.prod_image (fun x _ y _ h => sub_left_injective h)]
  choose! k hk hk' using H
  refine ⟨∏ r ∈ R, k r, Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
    (fun r hr => hk r hr), ?_⟩
  rw [Finset.prod_congr rfl hk', Finset.prod_mul_distrib, geom_eq_prod hζ0]
  congr 1
  exact Finset.prod_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz) _

end Fiber

end DualFramesAlt.eigenRingInvariants
