import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardLiftMatrix

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

scoped instance starO : StarRing (𝓞 K) where
  star := conjO K
  star_involutive := L3.conjO_conjO
  star_mul a b := by
    show conjO K (a * b) = conjO K b * conjO K a
    rw [map_mul, mul_comm]
  star_add := map_add (conjO K)

theorem star_def (a : 𝓞 K) : star a = conjO K a := rfl

scoped instance starQ [hF : Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    StarRing (𝓞 K ⧸ extP K 𝔭 ^ k) where
  star := NormLifting.conjQ _ (conjO_mem_pow hF.out 𝔭 k)
  star_involutive a := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    show NormLifting.conjQ _ _ (NormLifting.conjQ _ _ _) = _
    rw [NormLifting.conjQ_mk, NormLifting.conjQ_mk, L3.conjO_conjO]
  star_mul a b := by
    show NormLifting.conjQ _ _ (a * b) = NormLifting.conjQ _ _ b * NormLifting.conjQ _ _ a
    rw [map_mul, mul_comm]
  star_add := map_add _

theorem star_mk [Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    star (Ideal.Quotient.mk (extP K 𝔭 ^ k) a) = Ideal.Quotient.mk (extP K 𝔭 ^ k) (star a) := NormLifting.conjQ_mk _ _ a

theorem absNorm_extP_eq_sq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : Ideal.absNorm (extP K 𝔭) = Ideal.absNorm 𝔭 ^ 2 := by
  have h := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 K) 𝔭
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K, MeanB.finrank_eq_two hK hF] at h
  exact h

theorem absNorm_extP_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  have h1 : Ideal.absNorm (extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
    rw [map_pow, absNorm_extP_eq_sq hK hF h𝔭, ← pow_mul]
  rw [← h1, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem finite_quot {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := by
  have h0 : extP K 𝔭 ^ k ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact map_ne_bot_of_isMaximal h𝔭)
  first
  | exact Ideal.finiteQuotientOfFreeOfNeBot _ h0
  | exact (Ideal.absNorm_ne_zero_iff _).mp (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h0)

def piQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) →+* (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ k))

theorem piQ_mk (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    piQ K 𝔭 k (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

theorem piQ_surjective (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Function.Surjective (piQ K 𝔭 k) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

theorem piQ_star [Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :
    piQ K 𝔭 k (star a) = star (piQ K 𝔭 k a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [star_mk, piQ_mk, piQ_mk, star_mk]

theorem mk_mem_ker_piQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) a ∈ RingHom.ker (piQ K 𝔭 k) ↔ a ∈ extP K 𝔭 ^ k := by
  rw [RingHom.mem_ker, piQ_mk, Ideal.Quotient.eq_zero_iff_mem]

theorem card_ker_piQ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Nat.card (RingHom.ker (piQ K 𝔭 k)) = Ideal.absNorm 𝔭 ^ 2 := by
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  have hA := absNorm_extP_pow hK hF h𝔭 (k + 1)
  have hB := absNorm_extP_pow hK hF h𝔭 k
  have hC : Nat.card ((𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) ⧸ RingHom.ker (piQ K 𝔭 k)) =
      Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) :=
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (piQ_surjective (K := K) 𝔭 k)).toEquiv
  have hmul : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) = Nat.card (RingHom.ker (piQ K 𝔭 k)) *
      Nat.card ((𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) ⧸ RingHom.ker (piQ K 𝔭 k)) := by
    first
    | exact Submodule.card_eq_card_quotient_mul_card _
    | (rw [mul_comm]; exact Submodule.card_eq_card_quotient_mul_card _)
    | (rw [mul_comm]; exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (RingHom.ker (piQ K 𝔭 k)).toAddSubgroup)
    | exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (RingHom.ker (piQ K 𝔭 k)).toAddSubgroup
  rw [hC, hA, hB] at hmul
  have hN : 0 < Ideal.absNorm 𝔭 ^ (2 * k) :=
    pow_pos (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact ne_bot h𝔭)) _
  have e : Ideal.absNorm 𝔭 ^ (2 * (k + 1)) = Ideal.absNorm 𝔭 ^ 2 * Ideal.absNorm 𝔭 ^ (2 * k) := by
    ring
  rw [e] at hmul
  exact (Nat.eq_of_mul_eq_mul_right hN hmul).symm

def idQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k j : ℕ) :
    Ideal (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  (extP K 𝔭 ^ j).map (Ideal.Quotient.mk _)

theorem mem_idQ {𝔭 : Ideal (𝓞 F)} {k j : ℕ} {a : 𝓞 K ⧸ extP K 𝔭 ^ k} :
    a ∈ idQ K 𝔭 k j ↔ ∃ z ∈ extP K 𝔭 ^ j, Ideal.Quotient.mk _ z = a := by
  show a ∈ (extP K 𝔭 ^ j).map (Ideal.Quotient.mk _) ↔ _
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]

theorem mk_mem_idQ {𝔭 : Ideal (𝓞 F)} {k j : ℕ} (hjk : j ≤ k) {z : 𝓞 K} :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) z ∈ idQ K 𝔭 k j ↔ z ∈ extP K 𝔭 ^ j := by
  rw [mem_idQ]
  constructor
  · rintro ⟨z', hz', he⟩
    rw [Ideal.Quotient.eq] at he
    have h1 : z' - z ∈ extP K 𝔭 ^ j := Ideal.pow_le_pow_right hjk he
    have h2 : z = z' - (z' - z) := by ring
    rw [h2]
    exact Ideal.sub_mem _ hz' h1
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem star_mem_idQ [hF : Fact (IsFixF K F)] {𝔭 : Ideal (𝓞 F)} {k j : ℕ}
    {a : 𝓞 K ⧸ extP K 𝔭 ^ k} (ha : a ∈ idQ K 𝔭 k j) : star a ∈ idQ K 𝔭 k j := by
  obtain ⟨z, hz, rfl⟩ := mem_idQ.mp ha
  rw [star_mk]
  exact mem_idQ.mpr ⟨star z, conjO_mem_pow hF.out 𝔭 j z hz, rfl⟩

theorem mul_eq_zero_idQ {𝔭 : Ideal (𝓞 F)} {k j : ℕ} (hjk : k ≤ 2 * j)
    {a b : 𝓞 K ⧸ extP K 𝔭 ^ k} (ha : a ∈ idQ K 𝔭 k j) (hb : b ∈ idQ K 𝔭 k j) : a * b = 0 := by
  obtain ⟨x, hx, rfl⟩ := mem_idQ.mp ha
  obtain ⟨y, hy, rfl⟩ := mem_idQ.mp hb
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have h1 : x * y ∈ extP K 𝔭 ^ (j + j) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hx hy
  exact Ideal.pow_le_pow_right (by omega) h1

theorem ker_piQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) : RingHom.ker (piQ K 𝔭 k) = idQ K 𝔭 (k + 1) k := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [mk_mem_ker_piQ, mk_mem_idQ (Nat.le_succ k)]

end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
