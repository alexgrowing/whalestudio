import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesEqZeroOfValsTendstoZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPowSubPowLtOneOfUltra
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp.PrimChar

variable {l : ℕ} [Fact l.Prime]

theorem norm_sub_lt_one_trans {x y z : Qbar l} (h1 : ‖x - y‖ < 1) (h2 : ‖y - z‖ < 1) : ‖x - z‖ < 1 := by
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)

theorem norm_eq_one_of_pow {x : Qbar l} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : ‖x‖ = 1 := by
  have : ‖x‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

theorem norm_pow_sub_pow_lt_one {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : ‖x - y‖ < 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ < 1 :=
  _root_.GlobalTheory.PowerDifferenceNorm.norm_pow_sub_pow_lt_one hx hy h n

theorem norm_natCast_sub_lt_one {a b : ℕ} (h : (a : ZMod l) = (b : ZMod l)) : ‖(a : Qbar l) - b‖ < 1 := by
  obtain ⟨m, hm⟩ := ((ZMod.natCast_eq_natCast_iff a b l).1 h).symm.dvd
  have h2 : (a : Qbar l) - b = (l : Qbar l) * (m : Qbar l) := by
    have := congrArg (Int.cast : ℤ → Qbar l) hm
    push_cast at this
    exact this
  rw [h2, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ m)).trans_lt
    (GlobalTheory.KZ.norm_prime_lt_one_qbar l)

theorem exists_root_close {x : Qbar l} {n : ℕ} (hn : n ≠ 0) (h : ‖x ^ n - 1‖ < 1) :
    ∃ w : Qbar l, w ^ n = 1 ∧ ‖w - x‖ < 1 := by
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (n : Qbar l) := ⟨Nat.cast_ne_zero.2 hn⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Qbar l) n
  have h1 := congrArg (Polynomial.eval x) (Polynomial.X_pow_sub_one_eq_prod (Nat.pos_of_ne_zero hn) hμ)
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, Polynomial.eval_C] at h1
  rw [h1, norm_prod] at h
  by_contra hc
  push Not at hc
  refine absurd h (not_lt.2 (Finset.one_le_prod fun w hw => ?_))
  rw [norm_sub_rev]
  exact hc w ((Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn) 1).1 hw)

theorem exists_teichmuller : ∃ ω : (ZMod l)ˣ →* (Qbar l)ˣ,
    ∀ x : (ZMod l)ˣ, ‖(ω x : Qbar l) - ((x : ZMod l).val : Qbar l)‖ < 1 := by
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hord : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have h0 : ‖(((g : ZMod l).val : ℕ) : Qbar l) ^ (l - 1) - 1‖ < 1 := by
    have := norm_natCast_sub_lt_one (l := l) (a := (g : ZMod l).val ^ (l - 1)) (b := 1) (by
      push_cast
      rw [ZMod.natCast_zmod_val, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one])
    exact_mod_cast this
  obtain ⟨w, hw, hwg⟩ := exists_root_close hl1 h0
  let w' : (Qbar l)ˣ := Units.ofPowEqOne w (l - 1) hw hl1
  have hw' : (w' : Qbar l) = w := rfl
  have hdvd : orderOf w' ∣ orderOf g := by
    rw [hord]
    apply orderOf_dvd_of_pow_eq_one
    ext
    rw [Units.val_pow_eq_pow_val, hw', hw, Units.val_one]
  refine ⟨monoidHomOfForallMemZpowers hg hdvd, fun x => ?_⟩
  obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hg x))
  rw [map_pow, monoidHomOfForallMemZpowers_apply_gen, Units.val_pow_eq_pow_val, hw']
  refine norm_sub_lt_one_trans (norm_pow_sub_pow_lt_one (norm_eq_one_of_pow hl1 hw).le
    (IsUltrametricDist.norm_natCast_le_one _ _) hwg j) ?_
  have := norm_natCast_sub_lt_one (l := l) (a := (g : ZMod l).val ^ j) (b := ((g ^ j : (ZMod l)ˣ) : ZMod l).val) (by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  exact_mod_cast this

theorem exists_wild (k : ℕ) (ζ : Qbar l) (h2 : l ≠ 2) (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (l ^ k))
    (u : (ZMod (l ^ (k + 1)))ˣ) (hu : (u : ZMod (l ^ (k + 1))) = 1 + l) :
    ∃ χ : (ZMod (l ^ (k + 1)))ˣ →* (Qbar l)ˣ, (χ u : Qbar l) = ζ ∧ ∀ b, b ^ (l - 1) = 1 → χ b = 1 := by
  have hl : l.Prime := Fact.out
  have hl2 := hl.two_le
  have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ k) := ⟨hlk⟩
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨g, hg⟩ := (ZMod.isCyclic_units_of_prime_pow l hl h2 (k + 1)).exists_generator
  have hord : orderOf g = l ^ k * (l - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ hl]
  have hou : orderOf u = l ^ k := by
    rw [← orderOf_units, hu, ZMod.orderOf_one_add_prime hl h2]
  obtain ⟨a, ha⟩ := (mem_powers_iff_mem_zpowers.2 (hg u))
  simp only at ha
  have hcop : Nat.Coprime l (l - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hl]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hla : Nat.Coprime a (l ^ k) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
    rintro ⟨c, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 : u ^ (l ^ j * (l - 1)) = 1 := by
      rw [← ha, ← pow_mul, show l * c * (l ^ j * (l - 1)) = (l ^ (j + 1) * (l - 1)) * c by ring, ← hord, pow_mul,
        pow_orderOf_eq_one, one_pow]
    have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hou, pow_succ] at h3
    exact (Nat.Prime.coprime_iff_not_dvd hl).1 hcop (Nat.dvd_of_mul_dvd_mul_left (pow_pos hl.pos j) h3)
  obtain ⟨i, -, hi⟩ := (hζ.pow_of_coprime a hla).eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hc : (ζ ^ i) ^ (l ^ k) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  let c : (Qbar l)ˣ := Units.ofPowEqOne (ζ ^ i) (l ^ k) hc hlk
  have hc' : (c : Qbar l) = ζ ^ i := rfl
  have hc1 : c ^ (l ^ k) = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, hc', hc, Units.val_one]
  have hdvd : orderOf c ∣ orderOf g := by
    rw [hord]
    exact (orderOf_dvd_of_pow_eq_one hc1).mul_right _
  refine ⟨monoidHomOfForallMemZpowers hg hdvd, ?_, fun b hb => ?_⟩
  · rw [← ha, map_pow, monoidHomOfForallMemZpowers_apply_gen, Units.val_pow_eq_pow_val, hc', ← pow_mul, mul_comm,
      pow_mul, hi]
  · have e1 : (monoidHomOfForallMemZpowers hg hdvd b) ^ (l - 1) = 1 := by rw [← map_pow, hb, map_one]
    have e2 : (monoidHomOfForallMemZpowers hg hdvd b) ^ (l ^ k) = 1 := by
      obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hg b))
      simp only
      rw [map_pow, monoidHomOfForallMemZpowers_apply_gen, ← pow_mul, mul_comm, pow_mul, hc1, one_pow]
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) (orderOf_dvd_of_pow_eq_one e2) (orderOf_dvd_of_pow_eq_one e1)

theorem isPrimitive_of_value (k : ℕ) (ζ : Qbar l) (h2 : l ≠ 2) (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (l ^ k))
    (χ : DirichletCharacter (Qbar l) (l ^ (k + 1))) (hχ : χ (1 + (l : ZMod (l ^ (k + 1)))) = ζ)
    (u : (ZMod (l ^ (k + 1)))ˣ) (hu : (u : ZMod (l ^ (k + 1))) = 1 + l) : χ.IsPrimitive := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [DirichletCharacter.isPrimitive_def]
  by_contra hne
  have hd := χ.conductor_dvd_level
  obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow hl).1 hd
  have hi' : i ≤ j + 1 := by
    rcases Nat.lt_or_eq_of_le hi with h | h
    · omega
    · exact absurd (by rw [hc, h]) hne
  have hd2 : χ.conductor ∣ l ^ (j + 1) := by rw [hc]; exact pow_dvd_pow _ hi'
  have hker := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).1 χ.factorsThrough_conductor
  have h1 : (1 + (l : ZMod (l ^ (j + 1)))) ^ (l ^ j) = 1 := by
    rw [← ZMod.orderOf_one_add_prime hl h2 j]; exact pow_orderOf_eq_one _
  have hmem : u ^ (l ^ j) ∈ (ZMod.unitsMap hd).ker := by
    rw [MonoidHom.mem_ker]
    ext
    have := congrArg (ZMod.castHom hd2 (ZMod χ.conductor)) h1
    rw [map_pow, map_add, map_one, map_natCast] at this
    rw [ZMod.unitsMap_def, Units.coe_map, Units.val_pow_eq_pow_val, hu, Units.val_one]
    show ZMod.castHom hd (ZMod χ.conductor) _ = 1
    rw [map_pow, map_add, map_one, map_natCast]
    exact this
  have h3 := hker hmem
  rw [MonoidHom.mem_ker] at h3
  have h4 := congrArg Units.val h3
  rw [MulChar.coe_toUnitHom, Units.val_pow_eq_pow_val, hu, map_pow, hχ, Units.val_one] at h4
  exact hζ.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hl.ne_zero)
    (Nat.pow_lt_pow_right hl.one_lt (Nat.lt_succ_self j)) h4

theorem exists_primitive_inComp : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e k : ℕ) (ζ : Qbar l),
    l ≠ 2 → 1 ≤ k → IsPrimitiveRoot ζ (l ^ k) → ∃ ψ : DirichletCharacter (Qbar l) (l ^ (k + 1)),
      ψ.IsPrimitive ∧ InComp φ e ψ ∧ ψ⁻¹ (1 + (l : ZMod (l ^ (k + 1)))) = ζ := by
  intro l _ φ e k ζ h2 hk hζ
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hcop : Nat.Coprime (1 + l) (l ^ (k + 1)) := Nat.Coprime.pow_right _ (by simp)
  let u : (ZMod (l ^ (k + 1)))ˣ := ZMod.unitOfCoprime (1 + l) hcop
  have hu : (u : ZMod (l ^ (k + 1))) = 1 + l := by
    rw [ZMod.coe_unitOfCoprime]; push_cast; rfl
  obtain ⟨ω, hω⟩ := exists_teichmuller (l := l)
  obtain ⟨χ₂, hχu, hχT⟩ := exists_wild k ζ h2 hk hζ u hu
  have hd : l ∣ l ^ (k + 1) := dvd_pow_self l (Nat.succ_ne_zero k)
  have hred : ∀ b : (ZMod (l ^ (k + 1)))ˣ, ((ZMod.unitsMap hd b : (ZMod l)ˣ) : ZMod l) =
      ZMod.castHom hd (ZMod l) (b : ZMod (l ^ (k + 1))) := fun b => rfl
  have hu1 : ZMod.unitsMap hd u = 1 := by
    ext
    rw [hred, hu, map_add, map_one, map_natCast, ZMod.natCast_self, add_zero, Units.val_one]
  let f : (ZMod (l ^ (k + 1)))ˣ →* (Qbar l)ˣ := ((ω ^ e * MulChar.toUnitHom φ).comp (ZMod.unitsMap hd)) * χ₂
  have hf : ∀ b, (f b : Qbar l) = (ω (ZMod.unitsMap hd b) : Qbar l) ^ e *
      φ ((ZMod.unitsMap hd b : (ZMod l)ˣ) : ZMod l) * χ₂ b := fun b => by
    simp only [f, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom]
  let χ : DirichletCharacter (Qbar l) (l ^ (k + 1)) := MulChar.ofUnitHom f
  have hχ : ∀ b : (ZMod (l ^ (k + 1)))ˣ, χ b = f b := fun b => MulChar.ofUnitHom_coe f b
  have hval : χ (1 + (l : ZMod (l ^ (k + 1)))) = ζ := by
    rw [← hu, hχ, hf, hu1, hχu]; simp
  refine ⟨χ⁻¹, ?_, ?_, ?_⟩
  · have := isPrimitive_of_value k ζ h2 hk hζ χ hval u hu
    rw [DirichletCharacter.isPrimitive_def] at this ⊢
    rw [DirichletCharacter.conductor_inv, this]
  · intro b hb
    have hb' : (((b : ZMod (l ^ (k + 1))).val : ℕ) : ZMod l) = ((ZMod.unitsMap hd b : (ZMod l)ˣ) : ZMod l) := by
      rw [hred, ZMod.castHom_apply, ZMod.natCast_val]
    rw [inv_inv, hχ, hf, hχT b hb, Units.val_one, mul_one, hb', ← sub_mul, norm_mul]
    set x := ZMod.unitsMap hd b with hx
    have hx1 : x ^ (l - 1) = 1 := ZMod.units_pow_card_sub_one_eq_one l x
    have n1 : ‖φ (x : ZMod l)‖ = 1 := norm_eq_one_of_pow hl1 (by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hx1, Units.val_one, map_one])
    have n2 : ‖(ω x : Qbar l)‖ = 1 := norm_eq_one_of_pow hl1 (by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hx1, map_one, Units.val_one])
    rw [n1, mul_one]
    refine norm_pow_sub_pow_lt_one n2.le (IsUltrametricDist.norm_natCast_le_one _ _) ?_ e
    refine norm_sub_lt_one_trans (hω x) (norm_natCast_sub_lt_one ?_)
    rw [hb', ZMod.natCast_zmod_val]
  · rw [inv_inv, hval]

end GlobalTheory.KZ.Cmp.PrimChar
