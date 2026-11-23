import Mathlib
import Formalism.CyclotomicNorms.StatementI

namespace GlobalTheory

private lemma card_pow_eq_one_le_of_isCyclic {α : Type*} [Group α] [Finite α] [IsCyclic α] {n : ℕ}
    (hn : 0 < n) : Nat.card {a : α // a ^ n = 1} ≤ n := by
  classical
  let _ := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert IsCyclic.card_pow_eq_one_le (α := α) hn

theorem card_pow_eq_one_le_index_mul {G : Type*} [CommGroup G] [Finite G] (H : Subgroup G)
    [IsCyclic H] {d : ℕ} (hd : 0 < d) : Nat.card {x : G // x ^ d = 1} ≤ H.index * d := by
  classical

  set K : Subgroup G := (powMonoidHom d : G →* G).ker with hKdef
  have hK : Nat.card {x : G // x ^ d = 1} = Nat.card K :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp [hKdef]))
  have hsplit := (H.subgroupOf K).card_mul_index
  have hidx : (H.subgroupOf K).index ≤ H.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.relIndex_dvd_index_of_normal (H := H) (K := K))
  have hsmall : Nat.card (H.subgroupOf K) ≤ d := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : H.subgroupOf K => (⟨⟨(x.1 : G), Subgroup.mem_subgroupOf.mp x.2⟩, ?_⟩ :
        {h : H // h ^ d = 1})) ?_) (card_pow_eq_one_le_of_isCyclic hd)
    · apply Subtype.ext
      have hx : (x.1 : G) ^ d = 1 := x.1.2
      simpa using hx
    · intro x y hxy
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg (fun z : {h : H // h ^ d = 1} => ((z.1 : H) : G)) hxy
  rw [hK, ← hsplit]
  calc Nat.card (H.subgroupOf K) * (H.subgroupOf K).index ≤ d * H.index :=
        Nat.mul_le_mul hsmall hidx
    _ = H.index * d := Nat.mul_comm _ _

theorem card_pow_eq_one_le_units {M : Type*} [Monoid M] [Finite M] {d : ℕ} (hd : 0 < d) :
    Nat.card {x : M // x ^ d = 1} ≤ Nat.card {x : Mˣ // x ^ d = 1} := by
  refine Nat.card_le_card_of_injective
    (fun x => ⟨Units.ofPowEqOne x.1 d x.2 hd.ne', Units.pow_ofPowEqOne _ _⟩) ?_
  intro x y hxy
  apply Subtype.ext
  have := congrArg (fun z : {u : Mˣ // u ^ d = 1} => ((z.1 : Mˣ) : M)) hxy
  simpa using this

theorem card_pow_eq_one_le_of_isCyclic_units (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] {d : ℕ}
    (hd : 0 < d) : Nat.card {x : ZMod n // x ^ d = 1} ≤ d :=
  (card_pow_eq_one_le_units hd).trans (card_pow_eq_one_le_of_isCyclic hd)

theorem card_pow_eq_one_two_pow_le (w : ℕ) (hw : 1 ≤ w) {d : ℕ} (hd : 0 < d) :
    Nat.card {x : ZMod (2 ^ w) // x ^ d = 1} ≤ 2 * d := by
  have : NeZero (2 ^ w) := ⟨by positivity⟩
  obtain _ | _ | n := w
  · omega
  ·
    have : IsCyclic (ZMod (2 ^ 1))ˣ := (ZMod.isCyclic_units_two_pow_iff 1).mpr (by norm_num)
    exact (card_pow_eq_one_le_of_isCyclic_units _ hd).trans (by omega)
  ·
    let u : (ZMod (2 ^ (n + 2)))ˣ :=
      ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right _ (by norm_num))
    have hu : orderOf u = 2 ^ n := by
      rw [← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, ZMod.orderOf_five]
    have hG : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ n * 2 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp [pow_succ]
    have hidx : (Subgroup.zpowers u).index = 2 := by
      have h := (Subgroup.zpowers u).card_mul_index
      rw [Nat.card_zpowers, hu, hG] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h
    calc Nat.card {x : ZMod (2 ^ (n + 2)) // x ^ d = 1}
        ≤ Nat.card {x : (ZMod (2 ^ (n + 2)))ˣ // x ^ d = 1} := card_pow_eq_one_le_units hd
      _ ≤ (Subgroup.zpowers u).index * d := card_pow_eq_one_le_index_mul _ hd
      _ = 2 * d := by rw [hidx]

theorem rootsOfUnityCount : Formalism.CyclotomicNorms.RootsOfUnityCount := by
  intro ℓ w d hℓ hw hd
  have : NeZero (ℓ ^ w) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  by_cases h2 : ℓ = 2
  · subst h2
    exact ⟨fun h => absurd rfl h, card_pow_eq_one_two_pow_le w hw hd⟩
  ·
    have := ZMod.isCyclic_units_of_prime_pow ℓ hℓ h2 w
    have h := card_pow_eq_one_le_of_isCyclic_units (ℓ ^ w) (d := d) hd
    exact ⟨fun _ => h.trans (Nat.le_mul_of_pos_right _ (pow_pos hℓ.pos _)), h.trans (by omega)⟩

end GlobalTheory
