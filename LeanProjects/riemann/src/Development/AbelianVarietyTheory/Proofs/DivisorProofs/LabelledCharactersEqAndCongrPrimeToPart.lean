import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel.Congr

theorem part_pow {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G} (hx : IsOfFinOrder x) :
    ∃ a : ℕ, Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  set a := (orderOf x).factorization l with ha
  set M := orderOf x / l ^ a with hM
  have hmul : l ^ a * M = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
  have hM0 : M ≠ 0 := (Nat.ordCompl_pos l hn).ne'
  haveI : NeZero M := ⟨hM0⟩
  set u := (((l ^ a : ℕ) : ZMod M)⁻¹).val with hu
  have hz : Formalism.CyclotomicNorms.primeToPart l x = x ^ (l ^ a * u) := rfl
  have hone : (x ^ (l ^ a)) ^ M = 1 := by rw [← pow_mul, hmul, pow_orderOf_eq_one]
  have hmod : l ^ a * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow_left a hcop.symm)
  refine ⟨a, ?_⟩
  rw [hz, ← pow_mul, mul_comm, pow_mul]
  have := pow_eq_pow_of_modEq hmod hone
  rwa [pow_one] at this

theorem part_pow_compl {G : Type} [Monoid G] (l : ℕ) (x : G) :
    Formalism.CyclotomicNorms.primeToPart l x ^ (orderOf x / l ^ (orderOf x).factorization l) = 1 := by
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [← pow_mul, mul_right_comm, Nat.ordProj_mul_ordCompl_eq_self, pow_mul, pow_orderOf_eq_one, one_pow]

theorem eq_of_pow_eq {G : Type} [Monoid G] {M k : ℕ} (hM : M ≠ 0) (hk : k.Coprime M) {y z : G}
    (hy : y ^ M = 1) (hz : z ^ M = 1) (h : y ^ k = z ^ k) : y = z := by
  haveI : NeZero M := ⟨hM⟩
  set u := ((k : ZMod M)⁻¹).val with hu
  have hmod : k * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hk
  have h1 := pow_eq_pow_of_modEq hmod hy
  have h2 := pow_eq_pow_of_modEq hmod hz
  rw [pow_one, pow_mul] at h1 h2
  rw [← h1, h, h2]

theorem part_eq_iff {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x y : G} (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) :
    (∃ n : ℕ, x ^ (l ^ n) = y ^ (l ^ n)) ↔ Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l y := by
  obtain ⟨a, ha⟩ := part_pow hl hx
  obtain ⟨b, hb⟩ := part_pow hl hy
  have h1 : ∀ n, x ^ (l ^ (a + b + n)) = Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ (a + b + n)) := fun n => by
    rw [add_assoc, pow_add, pow_mul, pow_mul, ha]
  have h2 : ∀ n, y ^ (l ^ (a + b + n)) = Formalism.CyclotomicNorms.primeToPart l y ^ (l ^ (a + b + n)) := fun n => by
    rw [add_comm a b, add_assoc, pow_add, pow_mul, pow_mul, hb]
  constructor
  · rintro ⟨n, hn⟩
    have hx0 : orderOf x ≠ 0 := hx.orderOf_pos.ne'
    have hy0 : orderOf y ≠ 0 := hy.orderOf_pos.ne'
    refine eq_of_pow_eq (M := (orderOf x / l ^ (orderOf x).factorization l) *
      (orderOf y / l ^ (orderOf y).factorization l)) (k := l ^ (a + b + n))
      (mul_ne_zero (Nat.ordCompl_pos l hx0).ne' (Nat.ordCompl_pos l hy0).ne')
      (Nat.Coprime.pow_left _ (Nat.Coprime.mul_right (Nat.coprime_ordCompl hl hx0)
        (Nat.coprime_ordCompl hl hy0))) ?_ ?_ ?_
    · rw [pow_mul, part_pow_compl, one_pow]
    · rw [mul_comm, pow_mul, part_pow_compl, one_pow]
    · rw [← h1, ← h2, add_comm, pow_add, pow_mul, pow_mul, hn]
  · intro h
    exact ⟨a + b + 0, by rw [h1, h2, h]⟩

variable {p : ℕ} [Fact p.Prime]

theorem thetaOf_gen (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1)
    (n : ℕ) : GlobalTheory.GLq.thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  have hfin : IsOfFinOrder (L.gen d) := by
    rw [← orderOf_pos_iff, L.gen_order d hd]; exact hp
  unfold GlobalTheory.GLq.thetaOf
  rw [dif_pos h]
  have h1 := hfin.pow_eq_pow_iff_modEq.1 h.choose_spec
  rw [L.gen_order d hd] at h1
  exact (pow_eq_pow_of_modEq h1 (by rw [← map_pow, hx, map_one])).symm

theorem pow_eq_iff (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {θ θ' : Tor p d →* ℂˣ} {x x' : Fbar p}
    (h : LabelsChar L θ x) (h' : LabelsChar L θ' x') (m : ℕ) : θ ^ m = θ' ^ m ↔ x ^ m = x' ^ m := by
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  haveI : NeZero (p ^ d - 1) := ⟨hp.ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have hx0 : x ≠ 0 := fun e => by
    have := h.1; rw [e, zero_pow hp.ne'] at this; exact zero_ne_one this
  have hx0' : x' ≠ 0 := fun e => by
    have := h'.1; rw [e, zero_pow hp.ne'] at this; exact zero_ne_one this
  constructor
  · intro e
    let u : Tor p d := rootsOfUnity.mkOfPowEq (L.gen d) hprim.pow_eq_one
    have hu : ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ 1 := by rw [pow_one]; rfl
    have e1 := h.2 u
    have e2 := h'.2 u
    rw [hu, thetaOf_gen L hd h.1, pow_one] at e1
    rw [hu, thetaOf_gen L hd h'.1, pow_one] at e2
    have e3 : ((θ u : ℂˣ) : ℂ) ^ m = ((θ' u : ℂˣ) : ℂ) ^ m := by
      have := congrArg (fun f : Tor p d →* ℂˣ => ((f u : ℂˣ) : ℂ)) e
      simpa using this
    refine L.teich_inj _ _ (pow_ne_zero _ hx0) (pow_ne_zero _ hx0') ?_
    rw [map_pow, map_pow, ← e1, ← e2, e3]
  · intro e
    refine MonoidHom.ext fun u => Units.ext ?_
    have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hu
    have e1 := h.2 u
    have e2 := h'.2 u
    rw [← hn, thetaOf_gen L hd h.1] at e1
    rw [← hn, thetaOf_gen L hd h'.1] at e2
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, e1, e2,
      ← pow_mul, ← pow_mul, mul_comm n m, pow_mul, pow_mul, ← map_pow L.teich x m, ← map_pow L.teich x' m, e]

theorem eq_and_congr : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (d : ℕ), 0 < d → ∀ (θ θ' : Tor p d →* ℂˣ) (x x' : Fbar p), LabelsChar L θ x → LabelsChar L θ' x' → (θ = θ' ↔ x = x') ∧ ∀ l : ℕ, l.Prime → (CongrMod l θ θ' ↔ Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l x') := by
  intro p _ L d hd θ θ' x x' h h'
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  refine ⟨by simpa using pow_eq_iff L hd h h' 1, fun l hl => ?_⟩
  rw [← part_eq_iff hl (isOfFinOrder_iff_pow_eq_one.2 ⟨_, hp, h.1⟩) (isOfFinOrder_iff_pow_eq_one.2 ⟨_, hp, h'.1⟩)]
  refine exists_congr fun n => ?_
  rw [div_pow, div_eq_one]
  exact pow_eq_iff L hd h h' _

end GlobalTheory.ParamLabel.Congr
