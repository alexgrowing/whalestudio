import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SympModN

theorem omegaStd_nsmul_left {h : ℕ} (N : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    omegaStd (N • a) b = N * omegaStd a b := by
  unfold omegaStd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring

theorem omegaStd_single_inr {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (.inr i) 1) = a (.inl i) := by
  simp [omegaStd, Pi.single_apply]

theorem omegaStd_single_inl {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (.inl i) 1) = -a (.inr i) := by
  simp [omegaStd, Pi.single_apply]

theorem omegaStd_add_nsmul_modEq {h : ℕ} (N : ℕ) (x y b c : Fin h ⊕ Fin h → ℤ) :
    omegaStd (x + N • b) (y + N • c) ≡ omegaStd x y [ZMOD N] := by
  rw [Int.modEq_iff_dvd]
  unfold omegaStd
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  exact ⟨-(b (.inl i) * y (.inr i) + x (.inl i) * c (.inr i) + N * b (.inl i) * c (.inr i)) +
    (b (.inr i) * y (.inl i) + x (.inr i) * c (.inl i) + N * b (.inr i) * c (.inl i)), by ring⟩

theorem exists_eq_nsmul_iff {ι : Type*} (N : ℕ) (hN : N ≠ 0) (a : ι → ℤ) :
    (∃ b, a = N • b) ↔ ∀ j, (N : ℤ) ∣ a j := by
  constructor
  · rintro ⟨b, rfl⟩ j
    simp [nsmul_eq_mul]
  · intro hd
    refine ⟨fun j => a j / N, funext fun j => ?_⟩
    simp [nsmul_eq_mul, Int.mul_ediv_cancel' (hd j)]

theorem symplecticSimilitude_modN : ∀ (h N m : ℕ) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)), N ≠ 0 →
    m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) →
    (∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b) ∧ (∀ a, ∃ a' b, T a' = a + N • b) ∧
    ∃ T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x, ∃ b, T (T' x) = x + N • b) ∧
      ∀ m' : ℕ, m * m' ≡ 1 [MOD N] → ∀ x y, omegaStd (T' x) (T' y) ≡ m' * omegaStd x y [ZMOD N] := by
  intro h N m T hN hm hT
  have h1 : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b := by
    rintro a ⟨b, hb⟩
    have hd : ∀ y, (N : ℤ) ∣ omegaStd a y := by
      intro y
      have e := hT a y
      rw [hb, omegaStd_nsmul_left] at e
      have hdm : (N : ℤ) ∣ (m : ℤ) * omegaStd a y := by
        have h3 := Int.modEq_iff_dvd.1 e
        have h2 : (N : ℤ) ∣ (N : ℤ) * omegaStd b (T y) := dvd_mul_right _ _
        simpa using dvd_add h3 h2
      exact (Nat.isCoprime_iff_coprime.2 hm.symm).dvd_of_dvd_mul_left hdm
    refine (exists_eq_nsmul_iff N hN a).2 fun j => ?_
    rcases j with i | i
    · simpa [omegaStd_single_inr] using hd (Pi.single (.inr i) 1)
    · simpa [omegaStd_single_inl] using hd (Pi.single (.inl i) 1)
  haveI : NeZero N := ⟨hN⟩
  let red : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ZMod N) := fun a j => (a j : ZMod N)
  let lift : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ℤ) := fun v j => ((v j).val : ℤ)
  have hred0 : ∀ a, red a = 0 ↔ ∃ b, a = N • b := by
    intro a
    rw [exists_eq_nsmul_iff N hN a, funext_iff]
    exact forall_congr' fun j => ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hredlift : ∀ v, red (lift v) = v := by
    intro v; funext j; simp [red, lift]
  have hred_sub : ∀ a a', red (a - a') = red a - red a' := by
    intro a a'; funext j; simp [red]
  have finj : Function.Injective fun v => red (T (lift v)) := by
    intro v w hvw
    have e : red (T (lift v - lift w)) = 0 := by
      rw [map_sub, hred_sub]; exact sub_eq_zero.2 hvw
    obtain ⟨b', hb'⟩ := h1 _ ((hred0 _).1 e)
    have e2 : red (lift v - lift w) = 0 := (hred0 _).2 ⟨b', hb'⟩
    rw [hred_sub, hredlift, hredlift] at e2
    exact sub_eq_zero.1 e2
  have fsurj := Finite.injective_iff_surjective.1 finj
  have h2 : ∀ a, ∃ a' b, T a' = a + N • b := by
    intro a
    obtain ⟨v, hv⟩ := fsurj (red a)
    have e : red (T (lift v) - a) = 0 := by
      rw [hred_sub]; exact sub_eq_zero.2 hv
    obtain ⟨b, hb⟩ := (hred0 _).1 e
    exact ⟨lift v, b, by rw [← hb]; abel⟩
  choose v b hvb using fun i : Fin h ⊕ Fin h => h2 (Pi.single i 1)
  let T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) :=
    ∑ i, (LinearMap.proj i : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ).smulRight (v i)
  have hT' : ∀ x, T' x = ∑ i, x i • v i := by
    intro x; simp [T']
  have h3 : ∀ x, T (T' x) = x + N • ∑ i, x i • b i := by
    intro x
    rw [hT', map_sum]
    simp only [map_zsmul, hvb, smul_add, Finset.sum_add_distrib]
    congr 1
    · funext j
      simp [Finset.sum_apply, Pi.single_apply]
    · rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  refine ⟨h1, h2, T', fun x => ⟨_, h3 x⟩, ?_⟩
  intro m' hmm' x y
  have e1 := hT (T' x) (T' y)
  rw [h3, h3] at e1
  have e2 := omegaStd_add_nsmul_modEq N x y (∑ i, x i • b i) (∑ i, y i • b i)
  have e3 : (m : ℤ) * omegaStd (T' x) (T' y) ≡ omegaStd x y [ZMOD N] := e1.symm.trans e2
  have hmm'' : (m : ℤ) * m' ≡ 1 [ZMOD N] := by
    unfold Nat.ModEq at hmm'
    unfold Int.ModEq
    exact_mod_cast hmm'
  calc omegaStd (T' x) (T' y) = 1 * omegaStd (T' x) (T' y) := by ring
    _ ≡ ((m : ℤ) * m') * omegaStd (T' x) (T' y) [ZMOD N] := Int.ModEq.mul_right _ hmm''.symm
    _ = m' * ((m : ℤ) * omegaStd (T' x) (T' y)) := by ring
    _ ≡ m' * omegaStd x y [ZMOD N] := Int.ModEq.mul_left _ e3

end GlobalTheory.SympModN
