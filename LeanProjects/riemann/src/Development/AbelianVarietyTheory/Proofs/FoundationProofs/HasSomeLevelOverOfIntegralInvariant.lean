import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegrality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeOfDvdStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsRangeOfMonicRootStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

private theorem gamma_le_of_dvd' {N N' : ℕ} (hd : N ∣ N') :
    CongruenceSubgroup.Gamma N' ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have key : ∀ x : ℤ, (x : ZMod N) = ZMod.castHom hd (ZMod N) (x : ZMod N') := fun x => by
    rw [map_intCast]
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, h1, map_one]
  · rw [key, h2, map_zero]
  · rw [key, h3, map_zero]
  · rw [key, h4, map_one]

theorem exists_common_lv {E : Subring ℂ} {n : ℕ} (M : ℕ) (hM : 0 < M) (r : Fin n → ℍ → ℂ)
    (hr : ∀ j, InR E (r j)) : ∃ N w : ℕ, 0 < N ∧ M ∣ N ∧ ∀ j, Lv E N w (r j) := by
  choose Nj wj hNj hLv using hr
  have hpos : 0 < M * ∏ j, Nj j := Nat.mul_pos hM (Finset.prod_pos fun j _ => hNj j)
  refine ⟨M * ∏ j, Nj j, ∑ j, wj j, hpos, dvd_mul_right _ _, fun j => ?_⟩
  exact GlobalTheory.T.lv_mono_of_dvd_of_le E (Nj j) _ (wj j) _ (r j) hpos
    (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) M)
    (Finset.single_le_sum (fun i _ => Nat.zero_le (wj i)) (Finset.mem_univ j)) (hLv j)

theorem mdifferentiable_DD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) DD := CuspForm.discriminant.holo'

theorem mdifferentiable_comp_smul {h : ℍ → ℂ} (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun τ => h (γ • τ) := by
  have e : (fun τ => h (γ • τ)) = h ∣[(0 : ℤ)] γ := by
    funext τ
    rw [ModularForm.SL_slash_apply]
    simp
  rw [e]
  exact hh.slash 0 _

theorem DD_vadd (N : ℕ) (τ : ℍ) : DD ((N : ℝ) +ᵥ τ) = DD τ := by
  have hT : (ModularGroup.T ^ (N : ℤ)) • τ = (N : ℝ) +ᵥ τ := by
    rw [UpperHalfPlane.modular_T_zpow_smul]; simp
  have hden : UpperHalfPlane.denom (ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) τ = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
  rw [← hT, ReciprocityTheory.ChartRestriction.L1.DD_smul, hden, one_pow, one_mul]

theorem comp_smul_vadd {N : ℕ} {h : ℍ → ℂ}
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, h (γ • τ) = h τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    h (γ • ((N : ℝ) +ᵥ τ)) = h (γ • τ) := by
  have hT : (ModularGroup.T ^ (N : ℤ)) • τ = (N : ℝ) +ᵥ τ := by
    rw [UpperHalfPlane.modular_T_zpow_smul]; simp
  have h1 : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  have h2 := (CongruenceSubgroup.Gamma_normal N).conj_mem _ h1 γ
  rw [← hT, ← mul_smul,
    show γ * ModularGroup.T ^ (N : ℤ) = (γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹) * γ by group, mul_smul]
  exact hinv _ h2 _

theorem inR_of_integral : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (h : ℍ → ℂ)
    (r : Fin n → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, h (γ • τ) = h τ) → (∀ j, InR ε.range (r j)) →
    (∀ τ, h τ ^ n + ∑ j, r j τ * h τ ^ (j : ℕ) = 0) → InR ε.range h := by
  intro Ω _ _ ε M n h r hM hh hinv hr heq
  obtain ⟨N, w, hN, hMN, hlv⟩ := exists_common_lv M hM r hr
  have hinvN : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, h (γ • τ) = h τ :=
    fun γ hγ τ => hinv γ (gamma_le_of_dvd' hMN hγ) τ
  refine ⟨N, w, hN, hinvN, fun γ => ?_⟩
  have hH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => DD τ ^ w * h (γ • τ)) :=
    (mdifferentiable_DD.pow w).mul (mdifferentiable_comp_smul hh γ)
  have hper : ∀ τ : ℍ, DD ((N : ℝ) +ᵥ τ) ^ w * h (γ • ((N : ℝ) +ᵥ τ)) = DD τ ^ w * h (γ • τ) := by
    intro τ; rw [DD_vadd, comp_smul_vadd hinvN γ τ]
  let s : Fin n → ℍ → ℂ := fun j τ => DD τ ^ (w * (n - (j : ℕ))) * r j (γ • τ)
  have hs : ∀ j, QAll (· ∈ ε.range) N (s j) := by
    intro j
    have h1 := (hlv j).2 γ
    have h2 : QAll (· ∈ ε.range) N fun τ => DD τ ^ (w * (n - 1 - (j : ℕ))) :=
      QAllSubring.pow _ (eis_qAll N hN DD (Or.inr (Or.inr rfl)) ε.range)
    refine (congrArg (QAll (· ∈ ε.range) N) (funext fun τ => ?_)).mp (QAllSubring.mul h2 h1)
    have hj := j.isLt
    have e : w * (n - 1 - (j : ℕ)) + w = w * (n - (j : ℕ)) := by
      rw [← Nat.mul_succ]; congr 1; omega
    simp only [s]
    rw [← mul_assoc, ← pow_add, e]
  have heqH : ∀ τ, (DD τ ^ w * h (γ • τ)) ^ n +
      ∑ j, s j τ * (DD τ ^ w * h (γ • τ)) ^ (j : ℕ) = 0 := by
    intro τ
    have e := heq (γ • τ)
    calc _ = DD τ ^ (w * n) * (h (γ • τ) ^ n + ∑ j, r j (γ • τ) * h (γ • τ) ^ (j : ℕ)) := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          · rw [mul_pow, pow_mul]
          · refine Finset.sum_congr rfl fun j _ => ?_
            have hj := j.isLt
            have e2 : w * n = w * (n - (j : ℕ)) + w * (j : ℕ) := by
              rw [← Nat.mul_add]; congr 1; omega
            simp only [s]
            rw [e2, pow_add, mul_pow, ← pow_mul]; ring
      _ = 0 := by rw [e, mul_zero]
  exact GlobalTheory.T.qExpansionAllCoeffs_range_of_monic_root Ω ε N n _ s hN hH hper hs heqH

end GlobalTheory.FN
