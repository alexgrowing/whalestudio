import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvLevCoreOfParts
import Formalism.SharpRestriction.LevelLetterCocycles.IsUnitOfMk
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LevBasicsD
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne

namespace Formalism.MainNotions.UnusedSlot80.InvCutPfL

open Formalism.MainNotions.N.Ln03 Formalism.MainNotions.UnusedSlot80.InvCut

section Part1

variable (LL : Type) [Field LL] (l : ℕ) [Fact l.Prime] (s : ℕ)

theorem invCutPf_precomp_mul (a b : (ZMod (l ^ (s + 1)))ˣ) (f : Rs LL l s → LL) :
    precomp LL l s a (precomp LL l s b f) = precomp LL l s (a * b) f := by
  funext ζ
  simp only [precomp_apply, powR_powR]

theorem invCutPf_precomp_one (f : Rs LL l s → LL) : precomp LL l s 1 f = f := by
  funext ζ
  simp only [precomp_apply, powR_one]

def invCutPf_stab (f : Rs LL l s → LL) : Subgroup (ZMod (l ^ (s + 1)))ˣ where
  carrier := {a | precomp LL l s a f = f}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [← invCutPf_precomp_mul, hb, ha]
  one_mem' := invCutPf_precomp_one LL l s f
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    calc precomp LL l s a⁻¹ f = precomp LL l s a⁻¹ (precomp LL l s a f) := by rw [ha]
      _ = f := by rw [invCutPf_precomp_mul, inv_mul_cancel, invCutPf_precomp_one]

theorem invCutPf_mem_stab (f : Rs LL l s → LL) (a : (ZMod (l ^ (s + 1)))ˣ) :
    a ∈ invCutPf_stab LL l s f ↔ precomp LL l s a f = f := Iff.rfl

theorem invCutPf_exists_pow (ζ₀ ζ : Rs LL l s) : ∃ a, powR LL l s a ζ₀ = ζ := by
  have hN : 0 < l ^ (s + 1) := pos_pow l s
  haveI : NeZero (l ^ (s + 1)) := ⟨hN.ne'⟩
  have h0 : IsPrimitiveRoot (ζ₀ : LL) (l ^ (s + 1)) := (mem_primitiveRoots hN).1 ζ₀.2
  have h1 : IsPrimitiveRoot (ζ : LL) (l ^ (s + 1)) := (mem_primitiveRoots hN).1 ζ.2
  obtain ⟨i, hi, hζ⟩ := h0.eq_pow_of_pow_eq_one h1.pow_eq_one
  have hcop : i.Coprime (l ^ (s + 1)) := (h0.pow_iff_coprime hN i).1 (by rw [hζ]; exact h1)
  refine ⟨ZMod.unitOfCoprime i hcop, Subtype.ext ?_⟩
  show (ζ₀ : LL) ^ ((ZMod.unitOfCoprime i hcop : ZMod (l ^ (s + 1)))).val = ζ
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hζ]

end Part1

theorem precompConst : PrecompConst := by
  intro LL _ l _ s S hS f hf
  by_cases h : Nonempty (Rs LL l s)
  · obtain ⟨ζ₀⟩ := h
    refine ⟨f ζ₀, fun ζ => ?_⟩
    have hle : Subgroup.closure S ≤ invCutPf_stab LL l s f :=
      (Subgroup.closure_le _).2 fun a ha => (invCutPf_mem_stab LL l s f a).2 (hf a ha)
    obtain ⟨a, rfl⟩ := invCutPf_exists_pow LL l s ζ₀ ζ
    have ha : precomp LL l s a f = f :=
      (invCutPf_mem_stab LL l s f a).1 (hle (by rw [hS]; exact Subgroup.mem_top a))
    exact (precomp_apply LL l s a f ζ₀).symm.trans (congrFun ha ζ₀)
  · exact ⟨0, fun ζ => (h ⟨ζ⟩).elim⟩

section Part2

variable {l : ℕ} [Fact l.Prime]

theorem invCutPf_toZModPow_eq_zero {n : ℕ} {z : ℤ_[l]} :
    PadicInt.toZModPow n z = 0 ↔ z ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]

theorem invCutPf_eq_one_iff {k : ℕ} {z : ℤ_[l]} :
    PadicInt.toZModPow k z = 1 ↔ z - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
  rw [← invCutPf_toZModPow_eq_zero, map_sub, map_one, sub_eq_zero]

theorem invCutPf_lt_one_iff {z : ℤ_[l]} : ‖z‖ < 1 ↔ PadicInt.toZModPow 1 z = 0 := by
  rw [PadicInt.norm_lt_one_iff_dvd, invCutPf_toZModPow_eq_zero, pow_one, Ideal.mem_span_singleton]

theorem invCutPf_norm_eq_one {z : ℤ_[l]} (h : PadicInt.toZModPow 1 z ≠ 0) : ‖z‖ = 1 := by
  rcases (PadicInt.norm_le_one z).lt_or_eq with h1 | h1
  · exact absurd (invCutPf_lt_one_iff.1 h1) h
  · exact h1

theorem invCutPf_congr {z w : ℤ_[l]} (h : ‖z - w‖ < 1) :
    PadicInt.toZModPow 1 z = PadicInt.toZModPow 1 w := by
  rw [← sub_eq_zero, ← map_sub]
  exact invCutPf_lt_one_iff.1 h

theorem invCutPf_lower {k n : ℕ} (h : k ≤ n) {z w : ℤ_[l]}
    (e : PadicInt.toZModPow n z = PadicInt.toZModPow n w) :
    PadicInt.toZModPow k z = PadicInt.toZModPow k w := by
  rw [← PadicInt.zmod_cast_comp_toZModPow k n h, RingHom.comp_apply, RingHom.comp_apply, e]

theorem invCutPf_le (s : ℕ) : 0 + 1 ≤ s + 1 := by omega

def invCutPf_rho (s : ℕ) : (ZMod (l ^ (s + 1)))ˣ →* (ZMod (l ^ (0 + 1)))ˣ :=
  ZMod.unitsMap (pow_dvd_pow l (invCutPf_le s))

theorem invCutPf_rho_red (s : ℕ) (x : ℤ_[l]ˣ) : invCutPf_rho s (redU l s x) = redU l 0 x :=
  Units.ext (RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow (0 + 1) (s + 1) (invCutPf_le s))
    (x : ℤ_[l]))

theorem reduction_zero_of_principal_unit (u : ℤ_[l]ˣ) (h1 : (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])}) :
    redU l 0 u = 1 := by
  apply Units.ext
  show PadicInt.toZModPow (0 + 1) (u : ℤ_[l]) = 1
  rw [invCutPf_eq_one_iff, zero_add, pow_one]
  exact h1

theorem invCutPf_teich (x : (ZMod (l ^ 1))ˣ) : ∃ d : DeltaT l, redU l 0 d.1 = x := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.one_lt⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], a = (((x : ZMod (l ^ 1)).val : ℕ) : ℤ_[l]) := ⟨_, rfl⟩
  have hxa : PadicInt.toZModPow 1 a = x := by
    rw [ha, map_natCast, ZMod.natCast_zmod_val]
  have hanorm : ‖a‖ = 1 := invCutPf_norm_eq_one (by rw [hxa]; exact x.ne_zero)
  have htot : Nat.totient (l ^ 1) = l - 1 := by rw [pow_one, Nat.totient_prime hl]
  have hferm : (x : ZMod (l ^ 1)) ^ (l - 1) = 1 := by
    have h := pow_card_eq_one (x := x)
    rw [ZMod.card_units_eq_totient, htot] at h
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hl1norm : ‖((l - 1 : ℕ) : ℤ_[l])‖ = 1 := by
    apply invCutPf_norm_eq_one
    rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by have := hl.two_le; omega) hd
    rw [pow_one] at this
    have := hl.two_le
    omega
  have hFa : ‖Polynomial.aeval a ((Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))‖ < 1 := by
    rw [invCutPf_lt_one_iff]
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, hxa, hferm, sub_self]
  have hder : ‖Polynomial.aeval a
      (Polynomial.derivative (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))‖ = 1 := by
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one,
      sub_zero, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, Algebra.algebraMap_self,
      RingHom.id_apply, norm_mul, norm_pow, hanorm, one_pow, mul_one]
    exact hl1norm
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))
    (a := a) (by rw [hder, one_pow]; exact hFa)
  rw [hder] at hza
  have hz1 : z ^ (l - 1) = 1 := by
    simpa [sub_eq_zero] using hz
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  have hzu : IsUnit z := IsUnit.of_pow_eq_one hz1 hl1
  refine ⟨⟨hzu.unit, Units.ext (by simpa using hz1)⟩, Units.ext ?_⟩
  show PadicInt.toZModPow 1 z = (x : ZMod (l ^ 1))
  rw [invCutPf_congr hza, hxa]

theorem invCutPf_pow_eq_one_iff (n : ℕ) (u : ℤ_[l]ˣ) (m : ℕ)
    (hmu : ((m : ℕ) : ZMod (l ^ (n + 1))) = PadicInt.toZModPow (n + 1) (u : ℤ_[l])) (hm : 1 ≤ m)
    (e : ℕ) : redU l n u ^ e = 1 ↔ l ^ (n + 1) ∣ m ^ e - 1 := by
  rw [← Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hm), ← ZMod.natCast_eq_natCast_iff, Nat.cast_pow,
    Nat.cast_one, hmu, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  exact eq_comm

theorem invCutPf_orderOf (hl2 : l ≠ 2) (s : ℕ) (u : ℤ_[l]ˣ)
    (h1 : (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])})
    (h2 : (u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) :
    orderOf (redU l s u) = l ^ s := by
  have hl := (Fact.out : l.Prime)
  cases s with
  | zero => rw [pow_zero, orderOf_eq_one_iff]; exact reduction_zero_of_principal_unit u h1
  | succ t =>
    haveI : NeZero (l ^ (t + 1 + 1)) := ⟨(pos_pow l (t + 1)).ne'⟩
    obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = (PadicInt.toZModPow (t + 1 + 1) (u : ℤ_[l])).val := ⟨_, rfl⟩
    have hmu : ((m : ℕ) : ZMod (l ^ (t + 1 + 1))) = PadicInt.toZModPow (t + 1 + 1) (u : ℤ_[l]) := by
      rw [hm_def, ZMod.natCast_zmod_val]
    have hmu' : PadicInt.toZModPow (t + 1 + 1) ((m : ℕ) : ℤ_[l]) =
        PadicInt.toZModPow (t + 1 + 1) (u : ℤ_[l]) := by
      rw [map_natCast, hmu]
    have hk : ∀ k ≤ t + 1 + 1,
        (((m : ℕ) : ZMod (l ^ k)) = 1 ↔ (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ k}) := by
      intro k hk
      rw [← map_natCast (PadicInt.toZModPow (p := l) k) m, invCutPf_lower hk hmu', invCutPf_eq_one_iff]
    have hl2' : 1 < l ^ 2 := Nat.one_lt_pow two_ne_zero hl.one_lt
    have hA : m % l = 1 := by
      have := (hk 1 (by omega)).2 (by rw [pow_one]; exact h1)
      rw [← Nat.cast_one (R := ZMod (l ^ 1)), ZMod.natCast_eq_natCast_iff', pow_one,
        Nat.mod_eq_of_lt hl.one_lt] at this
      exact this
    have hB : m % l ^ 2 ≠ 1 := by
      intro hc
      apply h2
      apply (hk 2 (by omega)).1
      rw [← Nat.cast_one (R := ZMod (l ^ 2)), ZMod.natCast_eq_natCast_iff', hc, Nat.mod_eq_of_lt hl2']
    have hm1 : 1 < m := by
      rcases Nat.lt_or_ge 1 m with h | h
      · exact h
      · interval_cases m
        · simp at hA
        · exact absurd (Nat.mod_eq_of_lt hl2') hB
    have hdvd1 : l ∣ m - 1 := (Nat.modEq_iff_dvd' hm1.le).1 (by
      show 1 % l = m % l
      rw [hA, Nat.mod_eq_of_lt hl.one_lt])
    have hndvd2 : ¬ l ^ 2 ∣ m - 1 := fun hd => hB (by
      have : 1 % l ^ 2 = m % l ^ 2 := (Nat.modEq_iff_dvd' hm1.le).2 hd
      rw [← this, Nat.mod_eq_of_lt hl2'])
    have hndvd : ¬ l ∣ m := by
      rw [Nat.dvd_iff_mod_eq_zero, hA]; exact one_ne_zero
    have hm0 : m - 1 ≠ 0 := by omega
    have hv1 : padicValNat l (m - 1) = 1 := by
      have a1 : 1 ≤ padicValNat l (m - 1) := (padicValNat_dvd_iff_le hm0).1 (by rw [pow_one]; exact hdvd1)
      have a2 : ¬ 2 ≤ padicValNat l (m - 1) := fun h => hndvd2 ((padicValNat_dvd_iff_le hm0).2 h)
      omega
    have hodd : Odd l := hl.odd_of_ne_two hl2
    have hv : ∀ j : ℕ, padicValNat l (m ^ (l ^ j) - 1) = 1 + j := by
      intro j
      have := padicValNat.pow_sub_pow hodd hm1 hdvd1 hndvd (pow_ne_zero j hl.ne_zero)
      rw [one_pow] at this
      rw [this, hv1, padicValNat.prime_pow]
    have hne : ∀ j : ℕ, m ^ (l ^ j) - 1 ≠ 0 := by
      intro j
      have := Nat.one_lt_pow (pow_ne_zero j hl.ne_zero) hm1
      omega
    apply orderOf_eq_prime_pow
    · rw [invCutPf_pow_eq_one_iff (t + 1) u m hmu hm1.le, padicValNat_dvd_iff_le (hne t), hv]
      omega
    · rw [invCutPf_pow_eq_one_iff (t + 1) u m hmu hm1.le, padicValNat_dvd_iff_le (hne (t + 1)), hv]
      omega

theorem invCutPf_card_ker (s : ℕ) : Nat.card (invCutPf_rho (l := l) s).ker = l ^ s := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ (s + 1)) := ⟨(pos_pow l s).ne'⟩
  haveI : NeZero (l ^ (0 + 1)) := ⟨(pos_pow l 0).ne'⟩
  have hsurj : Function.Surjective (invCutPf_rho (l := l) s) :=
    ZMod.unitsMap_surjective (pow_dvd_pow l (invCutPf_le s))
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (invCutPf_rho (l := l) s).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
    Nat.card_eq_fintype_card (α := (ZMod (l ^ (s + 1)))ˣ),
    Nat.card_eq_fintype_card (α := (ZMod (l ^ (0 + 1)))ˣ),
    ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hl,
    Nat.totient_prime_pow_succ hl, pow_zero, one_mul] at e1
  have hpos : 0 < l - 1 := by have := hl.two_le; omega
  exact Nat.eq_of_mul_eq_mul_left hpos (e1.symm.trans (mul_comm _ _))

theorem invCutPf_ker_eq (hl2 : l ≠ 2) (s : ℕ) (u : ℤ_[l]ˣ)
    (h1 : (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])})
    (h2 : (u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) :
    (invCutPf_rho (l := l) s).ker = Subgroup.zpowers (redU l s u) := by
  haveI : NeZero (l ^ (s + 1)) := ⟨(pos_pow l s).ne'⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, invCutPf_rho_red, reduction_zero_of_principal_unit u h1]
  · rw [Nat.card_zpowers, invCutPf_orderOf hl2 s u h1 h2, invCutPf_card_ker]

end Part2

theorem genUnits : GenUnits := by
  intro l _ hl2 s u h1 h2
  rw [eq_top_iff]
  intro g _
  obtain ⟨d, hd⟩ := invCutPf_teich (l := l) (invCutPf_rho s g)
  have hk : g * (redU l s d.1)⁻¹ ∈ (invCutPf_rho (l := l) s).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, invCutPf_rho_red, hd, mul_inv_cancel]
  rw [invCutPf_ker_eq hl2 s u h1 h2] at hk
  have hu : redU l s u ∈ Subgroup.closure
      (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hdm : redU l s d.1 ∈ Subgroup.closure
      (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨d, rfl⟩)
  have hz := (Subgroup.zpowers_le.2 hu) hk
  simpa using Subgroup.mul_mem _ hz hdm

end Formalism.MainNotions.UnusedSlot80.InvCutPfL

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

def levelBasicsOfRingCondition (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hGen : GenUnitsC) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
    (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (s : ℕ) :
    LevBasics ((HW l).W K 1 LL h.2.2) a s := by
  have e : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  haveI hpF : Fact ((D.loc l).PD K).p.Prime := ⟨by rw [e]; exact Fact.out⟩
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := OLC.complete_max LL
  haveI : CharZero ↥(OL LL) := Formalism.MainNotions.UnusedSlot80.levg_charZero LL
  letI : Algebra ℤ_[((D.loc l).PD K).p] ↥(OL LL) :=
    ((algebraMap ℤ_[l] ↥(OL LL)).comp (castZp e)).toAlgebra
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := h9
  have hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL h.2.2) :=
    Formalism.MainNotions.UnusedSlot80.ring_condition_uniformizer_polynomial D HW F hP9 l K LL h
  have hlm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [e]; exact Formalism.MainNotions.N.Pv.LocalLengthBound.l_mem_maxOL (D.loc l) LL
  have hZinj : Function.Injective (algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL)) :=
    (Formalism.MainNotions.LiftingTheory.zl_inj_O LL).comp (castZp_inj e)
  have hχ : ∀ g : ((HW l).W K 1 LL h.2.2).Gam, ∃ z : ℤ_[((D.loc l).PD K).p]ˣ,
      algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL) (z : ℤ_[((D.loc l).PD K).p]) =
        (((HW l).W K 1 LL h.2.2).χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨z, hz⟩ := Formalism.MainNotions.LiftingTheory.chi_zl (P := D.loc l) (H := HW l) h.2.2 g
    refine ⟨Units.map (castZp e.symm).toMonoidHom z, ?_⟩
    show algebraMap ℤ_[l] ↥(OL LL) (castZp e (castZp e.symm (z : ℤ_[l]))) = _
    rw [castZp_symm, hz]
  have hγz : ∃ z0 : ℤ_[((D.loc l).PD K).p]ˣ,
      algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL) (z0 : ℤ_[((D.loc l).PD K).p]) =
        (((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL)) ∧
      ((z0 : ℤ_[((D.loc l).PD K).p]) - 1).valuation = 1 := by
    obtain ⟨z, hz, hv⟩ := Formalism.MainNotions.LiftingTheory.gam_zl (P := D.loc l) (H := HW l) h.2.2
    refine ⟨Units.map (castZp e.symm).toMonoidHom z, ?_, ?_⟩
    · show algebraMap ℤ_[l] ↥(OL LL) (castZp e (castZp e.symm (z : ℤ_[l]))) = _
      rw [castZp_symm, hz]
    · have : ((Units.map (castZp e.symm).toMonoidHom z : ℤ_[((D.loc l).PD K).p]ˣ) :
          ℤ_[((D.loc l).PD K).p]) - 1 = castZp e.symm ((z : ℤ_[l]) - 1) := by
        rw [map_sub, map_one]; rfl
      rw [this, castZp_val, hv]
  have hcard := Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F hP9 l K LL h
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [e]; exact h.2.1
  letI : Algebra ↥(OL LL) (AlgebraicClosure ↥LL.1) :=
    ((algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).comp (algebraMap ↥(OL LL) ↥LL.1)).toAlgebra
  have hinjF : Function.Injective (algebraMap ↥(OL LL) (AlgebraicClosure ↥LL.1)) :=
    (algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).injective.comp Subtype.val_injective
  haveI : CharZero (AlgebraicClosure ↥LL.1) :=
    charZero_of_injective_algebraMap (algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).injective
  exact levBasics_of ((HW l).W K 1 LL h.2.2) hlm (AlgebraicClosure ↥LL.1) hR hinjF hZinj hχ hγz
    (by rw [hcard, e]) hp2 hGen a s

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

def levBasics_conv {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {PD : PeriodData G Qp K₀ K B BdR}
    {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (h : Formalism.MainNotions.N.Pv.LocalLengthBound.LB.LevBasics W a s) :
    LevBasics W a s :=
  ⟨h.F, h.fF, h.algOF, h.inj, h.hp, h.root, h.ev, h.ev_O, h.ev_letE, h.ev_π, h.ev_ps, h.ev_pt, h.σ,
    h.ev_γ, h.gen⟩

theorem invLevCore_L (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hRat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
      (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (s : ℕ) (hB : LevBasics ((HW l).W K 1 LL h.2.2) a s),
      LevRat ((HW l).W K 1 LL h.2.2) a s hB.F hB.ev) :
    AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG) := by
  intro l _ K LL hG hCA h5
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨⟨hdom, -, -⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  haveI := hdom
  haveI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  have hR : ToolsR.RingP ((HW l).W K 1 LL hCA.2.2) := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hT : Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL hCA.2.2) := tool_algebra_of_ring_condition D HW F h9 l K LL hCA h5
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL hCA.2.2) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)
  have hB : ∀ (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (s : ℕ),
      LevBasics ((HW l).W K 1 LL hCA.2.2) a s := fun a s =>
    levBasics_conv (Formalism.MainNotions.N.Pv.LocalLengthBound.LB.levelBasicsOfRingCondition D HW F h9
      Formalism.MainNotions.UnusedSlot80.InvCutPfL.genUnits l K LL hCA a s)
  exact invLevCore_of_parts ((HW l).W K 1 LL hCA.2.2) hR.1 hB
    (fun a s => levDiv_of ((HW l).W K 1 LL hCA.2.2) hR hT hpu a s (hB a s))
    (fun a s => hRat l K LL hCA a s (hB a s)) Formalism.MainNotions.UnusedSlot80.InvCutPfL.precompConst

end Formalism.MainNotions.UnusedSlot80.InvW
