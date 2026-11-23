import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.CharacterBoxes.PairGood
import Development.AutomorphicArithmetic.MeanSquareBounds.PairExists
import Development.AutomorphicArithmetic.MeanSquareBounds.Kappa4Loglog
import Development.AutomorphicArithmetic.MeanSquareBounds.IndDrop

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem pairEx_lift {N L : ℕ} [NeZero L] (h : N ∣ L) (ξ : DirichletCharacter ℂ N) (n : ℕ) (hn : n.Coprime L) :
    DirichletCharacter.changeLevel h ξ (n : ZMod L) = ξ (n : ZMod N) := by
  have ha : IsCoprime (n : ℤ) (L : ℤ) := Nat.isCoprime_iff_coprime.mpr hn
  have key := DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ h ha
  simpa using key

private theorem pairEx_box (M : ℕ) (hM : 0 < M) (C τ Y X z z' : ℝ) (q d : ℕ) (hR : Rows z z' q d) (hq : 8 * M < q)
    (hQ : GoodQ (8 * M) C τ Y X z q) (hD : GoodD (8 * M) C τ Y X z z' q d)
    (f : ℕ → ℂ) (ξ : DirichletCharacter ℂ (8 * M)) (hf : ∀ n : ℕ, n.Coprime (8 * M) → ξ (n : ZMod (8 * M)) = f n)
    (i j : Fin 2) (hij : i ≠ 0 ∨ j ≠ 0) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hI : Formalism.HC.An.Induces χ (UpperTheory.Top.tw f q d i j) (2 * M * q * d)) :
    Box (8 * M * Real.exp z * Real.exp z' ^ (j : ℕ)) C τ Y X χ := by
  have hq2 : q ≠ 2 := by
    intro h2
    have hm := hR.q_mod
    rw [h2] at hm
    norm_num at hm
  have hqN : ¬ q ∣ 8 * M := by
    intro hd
    have hle := Nat.le_of_dvd (by omega) hd
    omega
  have h8 : ∀ n : ℕ, n.Coprime (2 * M * q * d) → n.Coprime (8 * M) := by
    intro n hn
    have h2 : n.Coprime 2 := Nat.Coprime.coprime_dvd_right ⟨M * q * d, by ring⟩ hn
    have hM' : n.Coprime M := Nat.Coprime.coprime_dvd_right ⟨2 * q * d, by ring⟩ hn
    have h8' : n.Coprime 8 := by simpa using Nat.Coprime.pow_right 3 h2
    exact Nat.Coprime.mul_right h8' hM'
  have hlev : 2 * M * q * d ≠ 0 :=
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hM) hR.q_prime.pos) hR.d_prime.pos).ne'
  obtain ⟨hprim, hval⟩ := hI
  fin_cases j
  · fin_cases i
    · simp at hij
    · have hInd : Ind χ (fun n ↦ ξ n * J q n) (2 * M * q * d) := by
        refine ⟨hprim, fun n hn => ?_⟩
        rw [hval n hn]
        simp [UpperTheory.Top.tw, J, hf n (h8 n hn)]
      have hInd' := ind_drop (8 * M) q (2 * M * q * d) ξ N χ (by omega) hR.q_prime hq2 hqN hlev hInd
      have hB := hQ ξ N χ hInd'
      refine (congrArg (fun Q => Box Q C τ Y X χ) ?_).mpr hB
      simp
  · have hInd : Ind χ (fun n ↦ ξ n * J q n ^ (i : ℕ) * J d n) (8 * M * q * d) := by
      refine ⟨hprim, fun n hn => ?_⟩
      have hn' : n.Coprime (2 * M * q * d) := Nat.Coprime.coprime_dvd_right ⟨4, by ring⟩ hn
      rw [hval n hn']
      simp [UpperTheory.Top.tw, J, hf n (h8 n hn')]
    have hB := hD ξ (i : ℕ) (Nat.lt_succ_iff.mp i.isLt) N χ hInd
    refine (congrArg (fun Q => Box Q C τ Y X χ) ?_).mpr hB
    simp [Real.exp_add, mul_assoc]

private theorem pairEx_g {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h : χ ≠ 1) (y : ℝ) :
    Formalism.HC.An.gChi χ y = Gchi χ y := by
  unfold Formalism.HC.An.gChi
  rw [if_neg h]
  unfold Formalism.HC.An.sumLamChi Gchi
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hfl : 0 < ⌊y⌋₊ := lt_of_lt_of_le Nat.zero_lt_one (le_trans hn.1 hn.2)
  have hy1 : 1 ≤ y := Nat.floor_pos.mp hfl
  have hny : (n : ℝ) ≤ y := le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))
  have hnn : 0 ≤ y / n - 1 := by
    rw [sub_nonneg, le_div_iff₀ (by linarith)]
    linarith
  rw [max_eq_left hnn]

private theorem log_exp_product_bounds (M : ℕ) (hM : 0 < M) (ε Y : ℝ) (hε : 0 < ε)
    (hY : Real.exp (1 + Real.log (8 * M)) ≤ Y) (j : ℕ) (hj : j ≤ 1) :
    Y ^ (ε / 6) ≤ Real.log (8 * M * Real.exp (Y ^ (ε / 5)) * Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2) ^ j) ∧
    Real.log (8 * M * Real.exp (Y ^ (ε / 5)) * Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2) ^ j)
      ≤ 3 * Y ^ (ε / 5) * Real.log Y ^ 2 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM8 : (1 : ℝ) ≤ 8 * M := by linarith
  have hlog8 : 0 ≤ Real.log (8 * M) := Real.log_nonneg hM8
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_exp (by linarith)) hY
  have hYpos : 0 < Y := by linarith
  have hL : 1 + Real.log (8 * M) ≤ Real.log Y := (Real.le_log_iff_exp_le hYpos).mpr hY
  have hw1 : 1 ≤ Y ^ (ε / 5) := Real.one_le_rpow hY1 (by linarith)
  have h65 : Y ^ (ε / 6) ≤ Y ^ (ε / 5) := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  set w := Y ^ (ε / 5) with hw
  set L := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hwL : L ^ 2 ≤ w * L ^ 2 := by nlinarith
  have hlogQ : Real.log (8 * M * Real.exp w * Real.exp (w * L ^ 2) ^ j)
      = Real.log (8 * M) + w + j * (w * L ^ 2) := by
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add,
      Real.log_mul (ne_of_gt (by linarith)) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hj' : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hz0 : 0 ≤ w * L ^ 2 := by positivity
  rw [hlogQ]
  constructor
  · nlinarith
  · have a1 : w ≤ w * L ^ 2 := by nlinarith
    have a2 : (j : ℝ) * (w * L ^ 2) ≤ w * L ^ 2 := by nlinarith
    linarith

theorem pairEx :
    UpperTheory.Top.PairEx := by
  intro M hM eps A heps heps' hA
  obtain ⟨C, hC, hpair⟩ := pair_exists
  obtain ⟨Y₀, hY₀⟩ := hpair eps (eps / 2) A (8 * M) heps heps' (by linarith) hA (by omega)
  obtain ⟨Y₁, hY₁⟩ := kappa4 eps 3 heps heps' (by norm_num)
  refine ⟨max (max Y₀ Y₁) (Real.exp (1 + Real.log (8 * M))), fun Y hY => ?_⟩
  have hYa : Y₀ ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hYb : Y₁ ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hYc : Real.exp (1 + Real.log (8 * M)) ≤ Y := le_trans (le_max_right _ _) hY
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog8 : 0 ≤ Real.log (8 * M) := Real.log_nonneg (by linarith)
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_exp (by linarith)) hYc
  have hz0 : 0 ≤ Y ^ (eps / 5) * Real.log Y ^ 2 := by
    have := Real.log_nonneg hY1
    positivity
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  obtain ⟨q, d, hR, hq, hQ, hD⟩ := hY₀ Y hYa (Y ^ A) (Y ^ (eps / 5) * Real.log Y ^ 2) le_rfl le_rfl
    (le_mul_of_one_le_left hz0 hA2)
  have hq2 : q ≠ 2 := by
    intro h2
    have hm := hR.q_mod
    rw [h2] at hm
    norm_num at hm
  haveI : NeZero (8 * M) := ⟨by omega⟩
  have hM8 : M ∣ 8 * M := Dvd.intro_left 8 rfl
  refine ⟨q, d, ?_, ?_, ?_, ?_⟩
  · refine ⟨hR.q_prime, hR.q_mod, hR.q_gt, hR.q_le, hR.d_prime, hR.d_mod, hR.d_gt, hR.d_le, ?_, ?_⟩
    · exact Nat.dvd_of_mod_eq_zero (hR.d_class q hR.q_prime hq2 (Or.inr rfl))
    · intro p hp hp2 hpl
      exact Nat.dvd_of_mod_eq_zero (hR.d_class p hp hp2 (Or.inl hpl))
  · have hqM : ¬ q ∣ M := fun h => by
      have := Nat.le_of_dvd hM h
      omega
    have hdM : ¬ d ∣ M := fun h => by
      have := Nat.le_of_dvd hM h
      have := hR.q_lt_d
      omega
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hR.q_prime).mpr hqM).symm
      ((Nat.Prime.coprime_iff_not_dvd hR.d_prime).mpr hdM).symm
  · intro ξ i j hij N _ χ hI y hy1 hy2
    have hB := pairEx_box M hM C (eps / 2) Y (Y ^ A) (Y ^ (eps / 5)) (Y ^ (eps / 5) * Real.log Y ^ 2) q d
      hR hq hQ hD (fun a ↦ ξ a) (DirichletCharacter.changeLevel hM8 ξ)
      (fun n hn => pairEx_lift hM8 ξ n hn) i j hij N χ hI
    obtain ⟨hgood, _, hG⟩ := hB
    have hne : χ ≠ 1 := hgood.1
    constructor
    · rw [pairEx_g χ hne]
      exact hG y ⟨hy1, hy2⟩
    · obtain ⟨hk1, hk2⟩ := log_exp_product_bounds M hM eps Y heps hYc (j : ℕ) (Nat.lt_succ_iff.mp j.isLt)
      have hk := hY₁ Y hYb _ N χ hk1 hk2 hgood
      have hlog : Real.log Y ≤ Real.log y := Real.log_le_log (by linarith) hy1
      exact le_trans hk (by linarith)
  · intro ρ hρ hρN i j hij N _ χ hI
    have hB := pairEx_box M hM C (eps / 2) Y (Y ^ A) (Y ^ (eps / 5)) (Y ^ (eps / 5) * Real.log Y ^ 2) q d
      hR hq hQ hD ρ.val (DirichletCharacter.changeLevel hρN ρ.χ)
      (fun n hn => pairEx_lift hρN ρ.χ n hn) i j hij N χ hI
    exact hB.1.2.2

end QH
