import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationAlgebraMapEqStatement

open IsDiscreteValuationRing

namespace GlobalTheory.PolyCycloValue

theorem card_double_min (S : Set ℕ) (a : ℕ → ℕ) (q : ℕ → ℝ) (w : ℕ) (hw : w ∈ S)
    (hq : ∀ k, 1 ≤ k → 0 < q k) (hqa : ∀ k k', 1 ≤ k → k < k' → q k' < q k) :
    ∃ BB : Finset ℕ, BB.card ≤ w + a w ∧ ∀ k, 1 ≤ k → k ∉ BB → ∀ i ∈ S, ∀ j ∈ S,
      (∀ m ∈ S, (a i : ℝ) + i * q k ≤ a m + m * q k) →
      (∀ m ∈ S, (a j : ℝ) + j * q k ≤ a m + m * q k) → i = j := by
  classical
  let M : ℕ → ℕ → Prop := fun k i => i ∈ S ∧ ∀ m ∈ S, (a i : ℝ) + i * q k ≤ a m + m * q k
  let B : Set ℕ := {k | 1 ≤ k ∧ ∃ i j, i < j ∧ M k i ∧ M k j}
  have hch : ∀ k, ∃ i j, k ∈ B → i < j ∧ M k i ∧ M k j := by
    intro k
    by_cases hk : k ∈ B
    · obtain ⟨-, i, j, h⟩ := hk
      exact ⟨i, j, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hk⟩
  choose I J hIJ using hch

  have hA : ∀ k, 1 ≤ k → ∀ i m, M k i → m ∈ S → m ≤ i → a i ≤ a m := by
    intro k hk i m hi hm hmi
    have h1 := hi.2 m hm
    have h2 : (m : ℝ) * q k ≤ i * q k :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmi) (hq k hk).le
    have : (a i : ℝ) ≤ a m := by linarith
    exact_mod_cast this
  have hA' : ∀ k, 1 ≤ k → ∀ i m, M k i → m ∈ S → m < i → a i < a m := by
    intro k hk i m hi hm hmi
    have h1 := hi.2 m hm
    have h2 : (m : ℝ) * q k < i * q k :=
      mul_lt_mul_of_pos_right (by exact_mod_cast hmi) (hq k hk)
    have : (a i : ℝ) < a m := by linarith
    exact_mod_cast this
  have hB : ∀ k k', 1 ≤ k → k < k' → ∀ m m', M k m → M k' m' → m ≤ m' := by
    intro k k' hk hkk m m' hm hm'
    by_contra hlt
    have hlt' : (m' : ℝ) < m := by exact_mod_cast (not_le.mp hlt)
    have h1 := hm.2 m' hm'.1
    have h2 := hm'.2 m hm.1
    have h3 := hqa k k' hk hkk
    nlinarith [mul_pos (sub_pos.mpr hlt') (sub_pos.mpr h3)]
  let φ : ℕ → ℕ := fun k => if I k < w then I k else w + a (J k)
  have hmaps : Set.MapsTo φ B (Finset.range (w + a w) : Set ℕ) := by
    intro k hk
    obtain ⟨hlt, hi, hj⟩ := hIJ k hk
    simp only [Finset.coe_range, Set.mem_Iio, φ]
    split_ifs with h
    · omega
    · have := hA' k hk.1 (J k) w hj hw (by omega)
      omega
  have hne : ∀ k ∈ B, ∀ k' ∈ B, k < k' → φ k ≠ φ k' := by
    intro k hk k' hk' hkk
    obtain ⟨hlt, hi, hj⟩ := hIJ k hk
    obtain ⟨hlt', hi', hj'⟩ := hIJ k' hk'
    have h1 := hB k k' hk.1 hkk _ _ hj hi'
    have h2 := hA' k' hk'.1 (J k') (J k) hj' hj.1 (by omega)
    simp only [φ]
    split_ifs <;> omega
  have hinj : Set.InjOn φ B := by
    intro k hk k' hk' h
    rcases lt_trichotomy k k' with h1 | h1 | h1
    · exact absurd h (hne k hk k' hk' h1)
    · exact h1
    · exact absurd h.symm (hne k' hk' k hk h1)
  have hfin : B.Finite := Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _)
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · have := Finset.card_le_card_of_injOn (s := hfin.toFinset) (t := Finset.range (w + a w)) φ
      (by simpa using hmaps) (by simpa using hinj)
    simpa using this
  · intro k hk hkB i hi j hj hmi hmj
    rw [Set.Finite.mem_toFinset] at hkB
    by_contra hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hkB ⟨hk, i, j, h, ⟨hi, hmi⟩, ⟨hj, hmj⟩⟩
    · exact hkB ⟨hk, j, i, h, ⟨hj, hmj⟩, ⟨hi, hmi⟩⟩

section Val

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_ne_top {x : R} (hx : x ≠ 0) : addVal R x ≠ ⊤ := by
  rwa [Ne, addVal_eq_top_iff]

theorem toNat_addVal_pos {x : R} (hx : x ≠ 0) (hu : ¬ IsUnit x) : 0 < (addVal R x).toNat := by
  have h1 := addVal_ne_top hx
  have h2 : addVal R x ≠ 0 := by rwa [Ne, addVal_eq_zero_iff]
  exact Nat.pos_of_ne_zero (by simp [ENat.toNat_eq_zero, h1, h2])

theorem nval_mul_pow (l : ℕ) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (x * y ^ n) =
      Formalism.MainNotions.BlochKatoReduction.Gen.nval R l x + n * Formalism.MainNotions.BlochKatoReduction.Gen.nval R l y := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hx)
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hy)
  have : addVal R (x * y ^ n) = ((s + n * t : ℕ) : ℕ∞) := by
    rw [(addVal R).map_mul, (addVal R).map_pow, ← hs, ← ht]; simp
  rw [this, ← hs, ← ht]
  simp only [ENat.toNat_coe]
  push_cast
  ring

theorem addVal_lt_of_nval_lt (l : ℕ) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Formalism.MainNotions.BlochKatoReduction.Gen.nval R l x < Formalism.MainNotions.BlochKatoReduction.Gen.nval R l y) : addVal R x < addVal R y := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval at h
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hx)
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hy)
  rw [← hs, ← ht] at h ⊢
  simp only [ENat.toNat_coe] at h
  have : (s : ℝ) < t := lt_of_not_ge fun hge =>
    absurd h (not_lt.mpr (div_le_div_of_nonneg_right hge (Nat.cast_nonneg _)))
  exact_mod_cast this

theorem sum_unique_min (l : ℕ) (S : Finset ℕ) (t : ℕ → R) (ht : ∀ i ∈ S, t i ≠ 0) (i₀ : ℕ)
    (hi₀ : i₀ ∈ S)
    (h : ∀ i ∈ S, i ≠ i₀ → Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i₀) < Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i)) :
    ∑ i ∈ S, t i ≠ 0 ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (∑ i ∈ S, t i) = Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i₀) := by
  have h0 := addVal_ne_top (ht i₀ hi₀)
  have h1 : addVal R (t i₀) < addVal R (∑ i ∈ S.erase i₀, t i) :=
    (addVal R).map_lt_sum h0 fun i hi =>
      addVal_lt_of_nval_lt l (ht i₀ hi₀) (ht i (Finset.mem_of_mem_erase hi))
        (h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
  have h2 : addVal R (∑ i ∈ S, t i) = addVal R (t i₀) := by
    rw [← Finset.add_sum_erase S t hi₀]
    exact (addVal R).map_add_eq_of_lt_left h1
  refine ⟨fun hz => h0 ?_, ?_⟩
  · rw [← h2, hz]; simp
  · unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval; rw [h2]

end Val

theorem value_at_root_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), l.Prime → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (h : Polynomial O) (w : ℕ), h.coeff w ≠ 0 → ∃ (BB : Finset ℕ) (c : ℕ → ℝ), BB.card ≤ w + (IsDiscreteValuationRing.addVal O (h.coeff w)).toNat ∧ ∀ k, 1 ≤ k → k ∉ BB → c k ≤ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff w) + w / (Nat.totient (l ^ k) : ℝ) ∧ ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → Polynomial.aeval (ζ - 1) h ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (Polynomial.aeval (ζ - 1) h) = c k := by
  intro O _ _ _ l hl hl0 hlu h w hw
  set e : ℝ := ((addVal O (l : O)).toNat : ℝ) with he
  have hepos : 0 < e := by rw [he]; exact_mod_cast toNat_addVal_pos hl0 hlu
  have hphi : ∀ k, (0 : ℝ) < (Nat.totient (l ^ k) : ℝ) := fun k => by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hl.pos k)
  let a : ℕ → ℕ := fun i => (addVal O (h.coeff i)).toNat
  let q : ℕ → ℝ := fun k => e / (Nat.totient (l ^ k) : ℝ)
  have hwS : w ∈ h.support := Polynomial.mem_support_iff.mpr hw
  obtain ⟨BB, hcard, hBB⟩ := card_double_min (h.support : Set ℕ) a q w hwS
    (fun k _ => div_pos hepos (hphi k)) (by
      intro k k' hk hkk
      refine div_lt_div_of_pos_left hepos (hphi k) ?_
      rw [Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl (by omega)]
      have h1 : l ^ (k - 1) < l ^ (k' - 1) := Nat.pow_lt_pow_right hl.one_lt (by omega)
      have h2 : 0 < l - 1 := by have := hl.one_lt; omega
      exact_mod_cast Nat.mul_lt_mul_of_pos_right h1 h2)
  have hmin : ∀ k, ∃ i ∈ h.support, ∀ m ∈ h.support, (a i : ℝ) + i * q k ≤ a m + m * q k :=
    fun k => Finset.exists_min_image h.support (fun i => (a i : ℝ) + i * q k) ⟨w, hwS⟩
  choose I hIS hI using hmin
  have hform : ∀ k i : ℕ, Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff i) + i / (Nat.totient (l ^ k) : ℝ)
      = ((a i : ℝ) + i * q k) / e := by
    intro k i
    have := hphi k
    simp only [Formalism.MainNotions.BlochKatoReduction.Gen.nval, a, q, ← he]
    field_simp
  refine ⟨BB, fun k => ((a (I k) : ℝ) + I k * q k) / e, hcard, fun k hk hkB => ⟨?_, ?_⟩⟩
  · rw [hform]
    exact div_le_div_of_nonneg_right (hI k w hwS) hepos.le
  · intro O' _ _ _ _ _ hinj ζ hζ
    have hl0' : (l : O') ≠ 0 := by
      rw [← map_natCast (algebraMap O O')]
      exact fun h0 => hl0 (hinj (by rw [h0, map_zero]))
    have hlu' : ¬ IsUnit (l : O') := by
      rw [← map_natCast (algebraMap O O')]
      exact fun h0 => hlu (IsLocalHom.map_nonunit _ h0)
    obtain ⟨hz, hv⟩ := GlobalTheory.T.normalizedValuation_primitiveRoot_prime_pow_sub_one O' l k hl hk hl0' hlu' ζ hζ
    have hc : ∀ i ∈ h.support, algebraMap O O' (h.coeff i) ≠ 0 := fun i hi h0 =>
      Polynomial.mem_support_iff.mp hi (hinj (by rw [h0, map_zero]))
    have hval : ∀ i ∈ h.support,
        Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' (h.coeff i) * (ζ - 1) ^ i)
          = ((a i : ℝ) + i * q k) / e := by
      intro i hi
      rw [nval_mul_pow l (hc i hi) hz, hv, GlobalTheory.T.normalizedValuation_algebraMap_eq O O' hinj, ← hform, mul_one_div]
    have key := sum_unique_min l h.support
      (fun i => algebraMap O O' (h.coeff i) * (ζ - 1) ^ i)
      (fun i hi => mul_ne_zero (hc i hi) (pow_ne_zero _ hz)) (I k) (hIS k) (by
        intro i hi hne
        rw [hval i hi, hval _ (hIS k)]
        refine div_lt_div_of_pos_right ?_ hepos
        refine lt_of_le_of_ne (hI k i hi) fun heq => hne ?_
        exact hBB k hk hkB i hi (I k) (hIS k) (fun m hm => heq ▸ hI k m hm) (hI k))
    rw [hval _ (hIS k)] at key
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    exact key

end GlobalTheory.PolyCycloValue
