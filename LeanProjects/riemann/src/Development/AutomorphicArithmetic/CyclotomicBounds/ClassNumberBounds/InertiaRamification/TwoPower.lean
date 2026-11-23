import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDvd
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Average

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N]

private theorem twoPower_exists_odd {k : ℕ} (hk : 2 ^ k ∣ N) (h2 : 2 ≤ k) :
    ∃ ψ ∈ condDvd N (2 ^ k), ψ.Odd := by
  have h4 : 4 ∣ 2 ^ k := (pow_dvd_pow 2 h2 : 2 ^ 2 ∣ 2 ^ k)
  have h4N : 4 ∣ N := h4.trans hk
  let χ : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
  refine ⟨changeLevel h4N χ, ?_, ?_⟩
  · rw [(mem_condDvd_iff _ _).1]
    exact (conductor_dvd_of_mem_conductorSet _ (changeLevel_factorsThrough χ h4N)).trans h4
  · have h := changeLevel_eq_cast_of_dvd' χ h4N (a := -1) (isCoprime_one_left.neg_left)
    have h' : ZMod.χ₄ (-1) = -1 := by decide
    unfold DirichletCharacter.Odd
    push_cast at h
    rw [h]
    simp [χ, h']

theorem card_evenPart_condDvd_two_pow {k : ℕ} (hk : 2 ^ k ∣ N) :
    Nat.card (evenPart (condDvd N (2 ^ k))) = 2 ^ (k - 2) := by
  have hc : Nat.card (condDvd N (2 ^ k)) = Nat.totient (2 ^ k) :=
    (mem_condDvd_iff (2 ^ k) 1).2 hk
  rcases Nat.lt_or_ge k 2 with h | h
  · have h1 : Nat.totient (2 ^ k) = 1 := by
      interval_cases k <;> simp
    have hle : Nat.card (evenPart (condDvd N (2 ^ k))) ≤ Nat.card (condDvd N (2 ^ k)) :=
      Subgroup.card_le_of_le inf_le_left
    have hpos : 0 < Nat.card (evenPart (condDvd N (2 ^ k))) := Nat.card_pos
    rw [show k - 2 = 0 by omega, pow_zero]
    omega
  · have h2 := (card_evenPart (condDvd N (2 ^ k))).2 (twoPower_exists_odd hk h)
    rw [hc, Nat.totient_prime_pow Nat.prime_two (by omega),
      show k - 1 = (k - 2) + 1 by omega, pow_succ] at h2
    omega

theorem fieldCond_evenPart_condDvd_two_pow {k : ℕ} (hk : 2 ^ k ∣ N) (h3 : 3 ≤ k) :
    fieldCond (evenPart (condDvd N (2 ^ k))) = 2 ^ k ∧
      ramIdx 2 (evenPart (condDvd N (2 ^ k))) = 2 ^ (k - 2) ∧
      resDeg 2 (evenPart (condDvd N (2 ^ k))) = 1 := by
  have hcard := card_evenPart_condDvd_two_pow hk
  set X := evenPart (condDvd N (2 ^ k)) with hX
  have hXle : X ≤ condDvd N (2 ^ k) := inf_le_left
  have hF := (fieldCond_sup X X 1).2.2
  have hram : ramIdx 2 X = Nat.card X := by
    have hbot : (localPart N 2).ker ⊓ X = ⊥ := by
      rw [eq_bot_iff]
      rintro ψ ⟨h1, h2⟩
      have h1' : ¬ 2 ∣ ψ.conductor := (localPart_eq_one_iff 2 ψ).2.1 h1
      have h2' : ψ.conductor ∣ 2 ^ k := (mem_condDvd_iff _ _).1.1 (hXle h2)
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2'
      rw [Subgroup.mem_bot, eq_one_iff_conductor_eq_one, hj]
      rcases j with _ | j
      · rfl
      · exact absurd (hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)) h1'
    unfold ramIdx
    rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_right, hbot, Subgroup.relIndex_bot_left]
  refine ⟨?_, hram.trans hcard, ?_⟩
  · obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 ((hF _).2 hXle)
    rw [hj]
    rcases hjk.eq_or_lt with rfl | hlt
    · rfl
    · exfalso
      have hle : X ≤ condDvd N (2 ^ (k - 1)) :=
        (hF _).1 (hj ▸ pow_dvd_pow 2 (by omega))
      have hle' : X ≤ evenPart (condDvd N (2 ^ (k - 1))) := le_inf hle inf_le_right
      have h := Subgroup.card_le_of_le hle'
      rw [hcard, card_evenPart_condDvd_two_pow ((pow_dvd_pow 2 (Nat.sub_le k 1)).trans hk)] at h
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h
      omega
  · have e2 : ramIdxUnits 2 (charKer X) * (inertiaUnits N 2 ⊔ charKer X).index =
        (charKer X).index := by
      unfold ramIdxUnits
      rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← Subgroup.relIndex_sup_right,
        Subgroup.relIndex_mul_index le_sup_right]
    rw [← ramIdx_eq_ramIdxUnits, hram, ← (annihilator_charKer X ⊥).2.2] at e2
    have hpos : 0 < Nat.card X := Nat.card_pos
    have h1 : (inertiaUnits N 2 ⊔ charKer X).index = 1 :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [e2, mul_one])
    unfold resDeg
    rw [Subgroup.index_eq_one.1 h1, Subgroup.relIndex_top_left]

end KStar.Ram
