import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.PadicSubsetSums.StableGradedCounts.PadicValCardGL
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory.TypePrimeEta

theorem sum_two_mul_Icc (r : ℕ) : ∑ a ∈ Finset.Icc 1 r, 2 * a = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

theorem padicValNat_pow_sub_one_le (g g' a : ℕ) (hg : g.Prime) (hg' : 2 ≤ g') (hgg : g' ≤ g ^ 2)
    (ha : 1 ≤ a) : padicValNat g (g' ^ a - 1) ≤ 2 * a := by
  haveI : Fact g.Prime := ⟨hg⟩
  have h1 : 1 < g' ^ a := Nat.one_lt_pow (by omega) (by omega)
  have hpos : 0 < g' ^ a - 1 := by omega
  have hle : g ^ padicValNat g (g' ^ a - 1) ≤ g' ^ a - 1 := Nat.le_of_dvd hpos pow_padicValNat_dvd
  have hlt : g ^ padicValNat g (g' ^ a - 1) < g ^ (2 * a) := by
    calc g ^ padicValNat g (g' ^ a - 1) ≤ g' ^ a - 1 := hle
      _ < g' ^ a := by omega
      _ ≤ (g ^ 2) ^ a := Nat.pow_le_pow_left hgg a
      _ = g ^ (2 * a) := by rw [← pow_mul]
  by_contra h
  have h := Nat.lt_of_not_le h
  have := Nat.pow_le_pow_right hg.pos h.le
  omega

theorem val_card_le (g g' r f : ℕ) (hg : g.Prime) (hg' : g'.Prime) (hne : g ≠ g')
    (hgg : g' ≤ g ^ 2) :
    padicValNat g (Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g)) ^ f *
      Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g')) ^ f) ≤ 2 * f * r ^ 2 := by
  haveI : Fact g.Prime := ⟨hg⟩
  haveI : Fact g'.Prime := ⟨hg'⟩
  have h0 : ∀ q : ℕ, [Fact q.Prime] → Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod q)) ≠ 0 :=
    fun q _ => Nat.card_pos.ne'
  obtain ⟨h1, h2⟩ := Formalism.IrreducibleCountingLemmas.WindowSums.padicValCardGeneralLinear g g' r hne
  rw [padicValNat.mul (pow_ne_zero _ (h0 g)) (pow_ne_zero _ (h0 g')), padicValNat.pow,
    padicValNat.pow, h1, h2]
  have hs : ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1) ≤ r * (r + 1) := by
    rw [← sum_two_mul_Icc]
    exact Finset.sum_le_sum fun a ha =>
      padicValNat_pow_sub_one_le g g' a hg hg'.two_le hgg (Finset.mem_Icc.1 ha).1
  have hd : r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
  have he : r * (r - 1) + r * (r + 1) = 2 * r ^ 2 := by
    cases r with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  calc f * (r * (r - 1) / 2) + f * ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1)
      ≤ f * (r * (r - 1)) + f * (r * (r + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hd) (Nat.mul_le_mul_left _ hs)
    _ = 2 * f * r ^ 2 := by rw [← mul_add, he]; ring

theorem val_cardG0g_le (D : D7) (k k' : Fin 2) (hkk : k ≠ k')
    (hlog : Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ)) :
    padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard ≤ 2 * D.R.f * D.R.r ^ 2 := by
  have hg := D.host.g_prime k
  have hg' := D.host.g_prime k'
  have hgg : D.host.g k' ≤ D.host.g k ^ 2 := by
    have h1 : (0 : ℝ) < D.host.g k' := by exact_mod_cast hg'.pos
    have h0 : (0 : ℝ) < (D.host.g k : ℝ) ^ 2 := pow_pos (by exact_mod_cast hg.pos) 2
    have h2 : Real.log (D.host.g k' : ℝ) ≤ Real.log ((D.host.g k : ℝ) ^ 2) := by
      rw [Real.log_pow]; push_cast; linarith
    have := (Real.log_le_log_iff h1 h0).1 h2
    exact_mod_cast this
  have hk : (k = 0 ∧ k' = 1) ∨ (k = 1 ∧ k' = 0) := by
    fin_cases k <;> fin_cases k' <;> simp_all
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two]
    exact val_card_le _ _ _ _ hg hg' D.host.g_ne hgg
  · rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two, mul_comm]
    exact val_card_le _ _ _ _ hg hg' D.host.g_ne.symm hgg

theorem first_le (f r t CT N r' e n : ℕ) (C : ℝ) (hC : 8 * (CT : ℝ) ≤ C) (hN2 : 2 ≤ N)
    (hN : N ≤ n + 1) (hr4 : 4 * r' ≤ N ^ 2) (hn : r + t = n) :
    ((f * (2 * ((2 * r + t * 2) * (CT * (N * r' + (e + t + 1) * (N + r'))))) : ℕ) : ℝ) ≤
      4 * (f : ℝ) * n * (C * (n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
  have hn1 : (1 : ℝ) ≤ n := by have : 1 ≤ n := by omega
                               exact_mod_cast this
  have hnR : (n : ℝ) = r + t := by rw [← hn]; push_cast; ring
  have a1 : (4 : ℝ) * r' ≤ (N : ℝ) ^ 2 := by exact_mod_cast hr4
  have a2 : (N : ℝ) ≤ 2 * n := by
    have : N ≤ 2 * n := by omega
    exact_mod_cast this
  have a0 : (0 : ℝ) ≤ N := by positivity
  have a3 : (N : ℝ) ^ 2 ≤ (2 * n) ^ 2 := pow_le_pow_left₀ a0 a2 2
  have hNr : 4 * ((N : ℝ) * r') ≤ 4 * (2 * (n : ℝ) ^ 3) := by
    calc 4 * ((N : ℝ) * r') = N * (4 * r') := by ring
      _ ≤ N * N ^ 2 := mul_le_mul_of_nonneg_left a1 a0
      _ = N ^ 3 := by ring
      _ ≤ (2 * n) ^ 3 := pow_le_pow_left₀ a0 a2 3
      _ = 4 * (2 * (n : ℝ) ^ 3) := by ring
  have hs : (N : ℝ) + r' ≤ 3 * (n : ℝ) ^ 2 := by nlinarith
  have he0 : (0 : ℝ) ≤ e := by positivity
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hr0 : (0 : ℝ) ≤ r' := by positivity
  have hm : ((e : ℝ) + t + 1) * (N + r') ≤ ((e : ℝ) + t + n) * (3 * (n : ℝ) ^ 2) :=
    mul_le_mul (by linarith) hs (by positivity) (by positivity)
  have hX : (N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r') ≤ 5 * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
    nlinarith [pow_nonneg (show (0:ℝ) ≤ n by linarith) 2]
  have hY : (0 : ℝ) ≤ (n : ℝ) ^ 2 * ((n : ℝ) + e + t) := by positivity
  have hCT : (0 : ℝ) ≤ CT := by positivity
  have hCX : (CT : ℝ) * ((N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r')) ≤
      C * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
    nlinarith [mul_le_mul_of_nonneg_left hX hCT, mul_le_mul_of_nonneg_right hC hY]
  calc ((f * (2 * ((2 * r + t * 2) * (CT * (N * r' + (e + t + 1) * (N + r'))))) : ℕ) : ℝ)
      = 4 * (f : ℝ) * n * ((CT : ℝ) * ((N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r'))) := by
        push_cast; rw [hnR]; ring
    _ ≤ 4 * (f : ℝ) * n * (C * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t))) :=
        mul_le_mul_of_nonneg_left hCX (by positivity)
    _ = 4 * (f : ℝ) * n * (C * (n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by ring

end GlobalTheory.TypePrimeEta

namespace GlobalTheory

theorem typePrimeBound_of_etaBound : ∀ (D : D7) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C →
    CongruenceAtTypePrimes (D := D) CT (EtaBound CT) → PairedCharacterCondition.aux₃ (D := D) C CT := by
  intro D C CT hC hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨c, hη, hL⟩ := hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h6 h7 h8
  have hv : (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ 2 * D.R.f * (D.R.r : ℝ) ^ 2 := by
    exact_mod_cast TypePrimeEta.val_cardG0g_le D k k' hkk h2
  have key : ∀ π ∈ D.nd.Zgood i,
      (c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ rhs C eta i ρ π := by
    intro π hπ
    obtain ⟨N, r', hN2, hN, hr1, hr4, hc⟩ := hL π hπ
    have hA := TypePrimeEta.first_le D.R.f D.R.r D.R.t CT N r' eta D.R.nV C hC hN2 hN hr4 rfl
    unfold rhs eT
    linarith
  have hη' : (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i,
      (D.nd.mult i π : ℝ) * ((c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ)) := by
    exact_mod_cast hη
  exact hη'.trans (Finset.sum_le_sum fun π hπ => mul_le_mul_of_nonneg_left (key π hπ) (Nat.cast_nonneg _))

end GlobalTheory
