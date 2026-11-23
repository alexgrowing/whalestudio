import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries

section Ln03DescendDvd

variable {O : Type} [CommRing O]

def powerSeriesBlockSum (ι : PowerSeries O →ₐ[O] PowerSeries O) (m : ℕ) (b : Fin m → PowerSeries O) :
    PowerSeries O :=
  ∑ i : Fin m, X ^ (i : ℕ) * ι (b i)

def powerSeriesBlockSplit (m : ℕ) (g : ℕ → O) : Fin m → PowerSeries O :=
  fun i => PowerSeries.mk fun j => g (m * j + i)

theorem blockSum_add (ι : PowerSeries O →ₐ[O] PowerSeries O) (m : ℕ) (b b' : Fin m → PowerSeries O) :
    powerSeriesBlockSum ι m (b + b') = powerSeriesBlockSum ι m b + powerSeriesBlockSum ι m b' := by
  simp only [powerSeriesBlockSum, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem blockSum_sub (ι : PowerSeries O →ₐ[O] PowerSeries O) (m : ℕ) (b b' : Fin m → PowerSeries O) :
    powerSeriesBlockSum ι m (b - b') = powerSeriesBlockSum ι m b - powerSeriesBlockSum ι m b' := by
  simp only [powerSeriesBlockSum, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem blockSum_zero (ι : PowerSeries O →ₐ[O] PowerSeries O) (m : ℕ) :
    powerSeriesBlockSum ι m 0 = 0 := by
  simp [powerSeriesBlockSum]

theorem blockSplit_add (m : ℕ) (g h : ℕ → O) :
    powerSeriesBlockSplit m (g + h) = powerSeriesBlockSplit m g + powerSeriesBlockSplit m h := by
  funext i
  ext j
  simp [powerSeriesBlockSplit]

theorem blockSplit_zero (m : ℕ) : powerSeriesBlockSplit m (0 : ℕ → O) = 0 := by
  funext i
  ext j
  simp [powerSeriesBlockSplit]

theorem X_pow_mul_dvd_algHom_of_X_pow_dvd {ι : PowerSeries O →ₐ[O] PowerSeries O} {m : ℕ} {w : PowerSeries O}
    (hX : ι X = w * X ^ m) (J : ℕ) (b : PowerSeries O) (hb : X ^ J ∣ b) : X ^ (m * J) ∣ ι b := by
  obtain ⟨c, rfl⟩ := hb
  refine ⟨w ^ J * ι c, ?_⟩
  rw [map_mul, map_pow, hX, mul_pow, ← pow_mul]
  ring

theorem coeff_blockSum_eq_zero {ι : PowerSeries O →ₐ[O] PowerSeries O} {m : ℕ} {w : PowerSeries O}
    (hX : ι X = w * X ^ m) (hm : 0 < m) (h : ℕ → O) (n : ℕ) (hh : ∀ n' ≤ n, h n' = 0) :
    coeff n (powerSeriesBlockSum ι m (powerSeriesBlockSplit m h)) = 0 := by
  unfold powerSeriesBlockSum
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeff_X_pow_mul']
  split_ifs with hi
  · have hdiv : X ^ ((n - i) / m + 1) ∣ powerSeriesBlockSplit m h i := by
      rw [X_pow_dvd_iff]
      intro j hj
      simp only [powerSeriesBlockSplit, coeff_mk]
      apply hh
      have h1 : j ≤ (n - i) / m := by omega
      have h2 := Nat.mul_le_mul (le_refl m) h1
      have h3 := Nat.div_add_mod (n - i) m
      omega
    have hd := X_pow_mul_dvd_algHom_of_X_pow_dvd hX _ _ hdiv
    rw [X_pow_dvd_iff] at hd
    apply hd
    rw [Nat.mul_add, Nat.mul_one]
    have h3 := Nat.div_add_mod (n - i) m
    have h4 := Nat.mod_lt (n - i) hm
    omega
  · rfl

private theorem div_eq_and_mod_eq_of_mul_add_eq {m j r n : ℕ} (hm : 0 < m) (hr : r < m) (h : m * j + r = n) :
    n / m = j ∧ n % m = r :=
  (Nat.div_mod_unique hm).mpr ⟨by omega, hr⟩

theorem coeff_blockSum_single {ι : PowerSeries O →ₐ[O] PowerSeries O} {m : ℕ} {w : PowerSeries O}
    (hX : ι X = w * X ^ m) (hm : 0 < m) (n : ℕ) (x : O) :
    coeff n (powerSeriesBlockSum ι m (powerSeriesBlockSplit m fun n' => if n' = n then x else 0)) =
      x * constantCoeff w ^ (n / m) := by
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin m, (i0 : ℕ) = n % m := ⟨⟨n % m, Nat.mod_lt _ hm⟩, rfl⟩
  have key : ∀ (i : Fin m) (j : ℕ), m * j + (i : ℕ) = n ↔ (i = i0 ∧ j = n / m) := by
    intro i j
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := div_eq_and_mod_eq_of_mul_add_eq hm i.isLt h
      exact ⟨Fin.ext (by omega), by omega⟩
    · rintro ⟨h1, h2⟩
      have h3 := Nat.div_add_mod n m
      have h4 : (i : ℕ) = n % m := by rw [h1, hi0]
      rw [h2, h4]
      exact h3
  have hb : ∀ i : Fin m, powerSeriesBlockSplit m (fun n' => if n' = n then x else 0) i =
      if i = i0 then x • (X : PowerSeries O) ^ (n / m) else 0 := by
    intro i
    ext j
    simp only [powerSeriesBlockSplit, coeff_mk]
    by_cases hi : i = i0
    · rw [if_pos hi, map_smul, coeff_X_pow, smul_eq_mul]
      by_cases hj : j = n / m
      · rw [if_pos ((key i j).mpr ⟨hi, hj⟩), if_pos hj, mul_one]
      · rw [if_neg (fun h => hj ((key i j).mp h).2), if_neg hj, mul_zero]
    · rw [if_neg hi, map_zero, if_neg (fun h => hi ((key i j).mp h).1)]
  unfold powerSeriesBlockSum
  rw [Finset.sum_eq_single i0]
  · rw [hb i0, if_pos rfl, map_smul, map_pow, hX]
    have e : (X : PowerSeries O) ^ (i0 : ℕ) * x • (w * X ^ m) ^ (n / m) =
        x • (w ^ (n / m) * X ^ n) := by
      rw [mul_smul_comm, mul_pow, ← pow_mul, hi0]
      congr 1
      rw [show (X : PowerSeries O) ^ n = X ^ (n % m) * X ^ (m * (n / m)) by
        rw [← pow_add, Nat.mod_add_div]]
      ring
    rw [e, map_smul, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_pow, smul_eq_mul]
  · intro i _ hi
    rw [hb i, if_neg hi, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem coeff_blockSum_triangular {ι : PowerSeries O →ₐ[O] PowerSeries O} {m : ℕ} {w : PowerSeries O}
    (hX : ι X = w * X ^ m) (hm : 0 < m) (g : ℕ → O) (n : ℕ) :
    coeff n (powerSeriesBlockSum ι m (powerSeriesBlockSplit m g)) =
      coeff n (powerSeriesBlockSum ι m (powerSeriesBlockSplit m fun n' => if n' < n then g n' else 0)) +
        g n * constantCoeff w ^ (n / m) := by
  have hsplit : g = (fun n' => if n' < n then g n' else 0) + (fun n' => if n' = n then g n else 0)
      + (fun n' => if n < n' then g n' else 0) := by
    funext n'
    simp only [Pi.add_apply]
    rcases lt_trichotomy n' n with h | rfl | h
    · rw [if_pos h, if_neg h.ne, if_neg (not_lt.mpr h.le), add_zero, add_zero]
    · simp
    · rw [if_neg (not_lt.mpr h.le), if_neg h.ne', if_pos h, zero_add, zero_add]
  conv_lhs => rw [hsplit]
  rw [blockSplit_add, blockSplit_add, blockSum_add, blockSum_add, map_add, map_add,
    coeff_blockSum_single hX hm n (g n),
    coeff_blockSum_eq_zero hX hm (fun n' => if n < n' then g n' else 0) n
      (fun n' hn' => if_neg (not_lt.mpr hn')), add_zero]

theorem eq_zero_of_blockSum_eq_zero {ι : PowerSeries O →ₐ[O] PowerSeries O} {m : ℕ} {w : PowerSeries O}
    (hX : ι X = w * X ^ m) (hm : 0 < m) (hw0 : IsUnit (constantCoeff w)) (g : ℕ → O)
    (h0 : powerSeriesBlockSum ι m (powerSeriesBlockSplit m g) = 0) (n : ℕ) : g n = 0 := by
  suffices H : ∀ N, ∀ k < N, g k = 0 from H (n + 1) n (Nat.lt_succ_self n)
  intro N
  induction N with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ N ih =>
    intro k hk
    by_cases hkN : k < N
    · exact ih k hkN
    · have hk' : k = N := by omega
      rw [hk']
      have h1 : (fun n' => if n' < N then g n' else 0) = (0 : ℕ → O) := by
        funext n'
        split_ifs with h
        · exact ih n' h
        · rfl
      have := coeff_blockSum_triangular hX hm g N
      rw [h0, h1, blockSplit_zero, blockSum_zero] at this
      simp only [map_zero, zero_add] at this
      exact ((hw0.pow (N / m)).mul_left_eq_zero).mp this.symm

def blockInverse (ι : PowerSeries O →ₐ[O] PowerSeries O) (m : ℕ) (wi : O) (f : PowerSeries O)
    (n : ℕ) : O :=
  wi ^ (n / m) * (coeff n f - coeff n (powerSeriesBlockSum ι m (powerSeriesBlockSplit m fun n' =>
    if _h : n' < n then blockInverse ι m wi f n' else 0)))
termination_by n

theorem blockSum_blockInverse {ι : PowerSeries O →ₐ[O] PowerSeries O} {m : ℕ} {w : PowerSeries O}
    (hX : ι X = w * X ^ m) (hm : 0 < m) (hw0 : IsUnit (constantCoeff w)) (f : PowerSeries O) :
    powerSeriesBlockSum ι m (powerSeriesBlockSplit m (blockInverse ι m (↑hw0.unit⁻¹) f)) = f := by
  ext n
  have hu : ((hw0.unit⁻¹ : Oˣ) : O) ^ (n / m) * constantCoeff w ^ (n / m) = 1 := by
    rw [← mul_pow, hw0.val_inv_mul, one_pow]
  have hI : blockInverse ι m (↑hw0.unit⁻¹) f n = ((hw0.unit⁻¹ : Oˣ) : O) ^ (n / m) *
      (coeff n f - coeff n (powerSeriesBlockSum ι m (powerSeriesBlockSplit m fun n' =>
        if n' < n then blockInverse ι m (↑hw0.unit⁻¹) f n' else 0))) := by
    rw [blockInverse]
    try simp only [dite_eq_ite]
  rw [coeff_blockSum_triangular hX hm _ n, hI, mul_right_comm, hu, one_mul]
  ring

theorem blockSplit_coeff {m : ℕ} (hm : 0 < m) (b : Fin m → PowerSeries O) :
    powerSeriesBlockSplit m (fun n => coeff (n / m) (b ⟨n % m, Nat.mod_lt _ hm⟩)) = b := by
  funext i
  ext j
  simp only [powerSeriesBlockSplit, coeff_mk]
  obtain ⟨h1, h2⟩ := div_eq_and_mod_eq_of_mul_add_eq hm i.isLt (rfl : m * j + (i : ℕ) = m * j + i)
  have hfin : (⟨(m * j + (i : ℕ)) % m, Nat.mod_lt _ hm⟩ : Fin m) = i := Fin.ext h2
  rw [hfin, h1]

end Ln03DescendDvd

private theorem power_series_block_sum_injective {O : Type} [CommRing O] {ι : PowerSeries O →ₐ[O] PowerSeries O} {m : ℕ} {w : PowerSeries O}
    (hX : ι X = w * X ^ m) (hm : 0 < m) (hw0 : IsUnit (constantCoeff w))
    {b b' : Fin m → PowerSeries O} (h : powerSeriesBlockSum ι m b = powerSeriesBlockSum ι m b') : b = b' := by
  have e := blockSplit_coeff hm (b - b')
  have hd : powerSeriesBlockSum ι m (powerSeriesBlockSplit m fun n => coeff (n / m) ((b - b') ⟨n % m, Nat.mod_lt _ hm⟩)) = 0 := by
    rw [e, blockSum_sub, h, sub_self]
  have hz : (fun n => coeff (n / m) ((b - b') ⟨n % m, Nat.mod_lt _ hm⟩)) = (0 : ℕ → O) :=
    funext fun n => eq_zero_of_blockSum_eq_zero hX hm hw0 _ hd n
  rw [hz, blockSplit_zero] at e
  exact sub_eq_zero.mp e.symm

theorem descendDvd : DescendDvdStatement := by
  unfold DescendDvdStatement
  intro O _ ι m hm hex
  obtain ⟨w, hw⟩ := hex
  have hw0 : IsUnit (constantCoeff (w : PowerSeries O)) := (Units.isUnit w).map constantCoeff
  have e0 : ∀ a : PowerSeries O, powerSeriesBlockSum ι m (fun i => if (i : ℕ) = 0 then a else 0) = ι a := by
    intro a
    unfold powerSeriesBlockSum
    rw [Finset.sum_eq_single ⟨0, hm⟩]
    · simp
    · intro i _ hi
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨?_, ?_⟩
  · intro p q hpq
    have hb := power_series_block_sum_injective hw hm hw0 (b := fun i => if (i : ℕ) = 0 then p else 0)
      (b' := fun i => if (i : ℕ) = 0 then q else 0) (by rw [e0, e0, hpq])
    have := congrFun hb ⟨0, hm⟩
    simpa using this
  · rintro p a ⟨c, hc⟩
    obtain ⟨d, hd⟩ : ∃ d : Fin m → PowerSeries O, powerSeriesBlockSum ι m d = c :=
      ⟨_, blockSum_blockInverse hw hm hw0 c⟩
    have key : powerSeriesBlockSum ι m (fun i => p * d i) =
        powerSeriesBlockSum ι m (fun i => if (i : ℕ) = 0 then a else 0) := by
      rw [e0, hc, ← hd]
      unfold powerSeriesBlockSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]
      ring
    have h0 : p * d ⟨0, hm⟩ = a := by
      simpa using congrFun (power_series_block_sum_injective hw hm hw0 key) ⟨0, hm⟩
    exact ⟨d ⟨0, hm⟩, h0.symm⟩

end LevelStatements.Lv
