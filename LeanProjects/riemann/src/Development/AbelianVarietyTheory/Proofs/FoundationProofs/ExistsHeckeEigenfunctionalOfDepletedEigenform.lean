import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvdStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorRaisesLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeTAdjointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeUAdjointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormConjugateCoefficientsInvCharStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUVCauchyProductIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearFunctionalEqCoeffLinearCombinationFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralWeightedLinearFormsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerLevelEqPowMulHeckeVStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerHeckeVEigenformStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eigF_of_prim : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (α β : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → Prim k N χ g → Wt (N * l) ρ → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (k - 1) → ∃ (B : ℕ) (c : ℕ → ℂ), EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = pet k ρ (qs (Vo l fun n => conj (g n))) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs fun n => conj (g n)) (qs a) := by
  intro k N l χ g ρ α β hk hN hl hlN hg hρ hab hαβ
  haveI : NeZero N := ⟨by omega⟩
  set h : ℕ → ℂ := fun n => conj (g n) with hh_def
  have hNl : 0 < N * l := Nat.mul_pos hN hl.pos
  have hdvd : N ∣ N * l := dvd_mul_right N l
  have hP : Prim k N χ⁻¹ h := (GlobalTheory.T.cuspForm_conjugate_coefficients_inv_char k N χ g).2 hg
  have hMFh : MF k N (ch χ⁻¹) h := hP.cf.1
  have lin := GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) (ch χ⁻¹)
  have hCFh : CF k (N * l) (ch χ⁻¹) h := (GlobalTheory.T.modularFormCoeffSeq_linear_structure k N (ch χ⁻¹)).2.2.2.2.2 (N * l) h hdvd hP.cf
  have hCFV : CF k (N * l) (ch χ⁻¹) (Vo l h) := (GlobalTheory.T.coeffHeckeVOperator_raises_level k N l (ch χ⁻¹) h hl.pos).2 hP.cf
  have petlin := GlobalTheory.T.halfPeterssonIntegralWeighted_linear_forms k (N * l) (N * l) N χ⁻¹ ρ hk hNl hdvd hρ

  have hsc : ∀ (h' a : ℕ → ℂ) (x : ℂ), CF k (N * l) (ch χ⁻¹) h' → MF k (N * l) (ch χ⁻¹) a →
      pet k ρ (qs (x • h')) (qs a) = conj x * pet k ρ (qs h') (qs a) := by
    intro h' a x hh' ha
    have e : qs (x • h') = fun τ => x * qs h' τ + 0 * qs h' τ := by
      rw [(lin.2.2.1 x h' hh'.1).2]; funext τ; simp
    rw [e, petlin.2 h' h' a x 0 hh' hh' ha.1]; simp
  have hconj : ∀ x : ZMod N, conj (χ x) = χ⁻¹ x := fun x => MulChar.star_apply' χ x
  have hch : ∀ n : ℕ, ch χ⁻¹ (n : ℤ) = χ⁻¹ (n : ZMod N) := by intro n; simp [ch]
  set φ : (ℕ → ℂ) → ℂ := fun a => pet k ρ (qs (Vo l h)) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs h) (qs a) with hφ_def
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_sturmBound_isModularFormCoeffSeq k (N * l) N χ⁻¹ hNl hdvd
  obtain ⟨c, hc⟩ := GlobalTheory.T.linearFunctional_eq_coeffLinearCombinationFinite {a | MF k (N * l) (ch χ⁻¹) a} B φ lin.1
    (by
      intro a ha b hb
      refine ⟨(lin.2.1 a b ha hb).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a b 1 1 hCFV ha.1 hb.1
      have e2 := petlin.1 h a b 1 1 hCFh ha.1 hb.1
      simp only [one_smul, one_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    (by
      intro x a ha
      refine ⟨(lin.2.2.1 x a ha).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a a x 0 hCFV ha.1 ha.1
      have e2 := petlin.1 h a a x 0 hCFh ha.1 ha.1
      simp only [zero_smul, add_zero, zero_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    hB
  have hφ : ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = φ a := fun a ha => (hc a ha).symm
  refine ⟨B, c, ⟨?_, ?_⟩, hφ⟩
  ·
    intro a ha q hq hqNl
    have hqN : ¬ q ∣ N := fun d => hqNl (dvd_mul_of_dvd_left d l)
    have hql : q ≠ l := fun e => hqNl (e ▸ dvd_mul_left q N)
    have hcop : q.Coprime l := (Nat.coprime_primes hq hl).2 hql
    have hTa := GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ⁻¹ a hk hdvd hq hqNl ha
    rw [hφ _ hTa, hφ _ ha]
    have eigh : To k (ch χ⁻¹ q) q h = h q • h := by
      rw [hP.eig q hq hqN]; funext n; simp
    have eigV : To k (ch χ⁻¹ q) q (Vo l h) = h q • Vo l h := by
      rw [(GlobalTheory.T.coeffHecke_UV_cauchyProduct_identities ℂ l hl.pos).2.2.2.2.1 k q _ h hcop hq.pos, eigh]
      funext n; simp only [Vo, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
    have adj0 := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k (N * l) N q χ⁻¹ ρ h a hk hNl hdvd hq hqNl hρ hCFh ha
    have adj1 := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k (N * l) N q χ⁻¹ ρ (Vo l h) a hk hNl hdvd hq hqNl hρ hCFV ha
    rw [eigh, hsc h a _ hCFh ha] at adj0
    rw [eigV, hsc (Vo l h) a _ hCFV ha] at adj1
    have hgq : conj (h q) = g q := by simp [hh_def]
    simp only [hφ_def]
    rw [adj0, adj1]
    simp only [hgq, hch]
    ring
  ·
    intro a ha
    have hper : ∀ d : ℤ, ch χ⁻¹ (d + ((N * l : ℕ) : ℤ)) = ch χ⁻¹ d := by
      intro d; simp only [ch]; congr 1; push_cast; simp
    have hUa := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ⁻¹) a hk hl (dvd_mul_left l N) hper ha).1
    rw [hφ _ hUa, hφ _ ha]
    have adjU0 := GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint k (N * l) N l χ⁻¹ ρ h a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFh ha
    have adjU1 := GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint k (N * l) N l χ⁻¹ ρ (Vo l h) a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFV ha
    have tr0 := GlobalTheory.T.sum_slash_heckeRepLowerLevel_eq_pow_mul_heckeV k N l χ⁻¹ h hk hl.pos hMFh
    have eigl : To k (ch χ⁻¹ l) l h = h l • h := by
      rw [hP.eig l hl hlN]; funext n; simp
    have tr1 := GlobalTheory.T.sum_slash_heckeRepLower_heckeV_eigenform k N l χ⁻¹ h (h l) hk hN hl hlN hMFh eigl
    have f0 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ)
        = fun τ => ((l : ℂ) ^ k) * qs (Vo l h) τ + 0 * qs (Vo l h) τ := by
      funext τ; rw [tr0]; ring
    have f1 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ)
        = fun τ => (ch χ⁻¹⁻¹ l * h l) * qs (Vo l h) τ + (-(ch χ⁻¹⁻¹ l * (l : ℂ)⁻¹)) * qs h τ := by
      funext τ; rw [tr1]; ring
    rw [f0, petlin.2 (Vo l h) (Vo l h) a _ 0 hCFV hCFV ha.1] at adjU0
    rw [f1, petlin.2 (Vo l h) h a _ _ hCFV hCFh ha.1] at adjU1
    have e1 : conj (ch χ⁻¹⁻¹ (l : ℤ)) = χ⁻¹ (l : ZMod N) := by
      rw [inv_inv]; simp only [ch, Int.cast_natCast]; exact hconj _
    have hgl : conj (h l) = g l := by simp [hh_def]
    have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
    have key : (l : ℂ) ^ (k - 1) / (l : ℂ) ^ k = (l : ℂ)⁻¹ := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]; field_simp
    simp only [map_mul, map_neg, map_inv₀, map_pow, Complex.conj_natCast, map_zero, e1, hgl, zero_mul, add_zero] at adjU0 adjU1
    simp only [hφ_def, adjU0, adjU1]
    set P0 := pet k ρ (qs h) (qs a)
    set P1 := pet k ρ (qs (Vo l h)) (qs a)
    have hcan : (l : ℂ) ^ k / (l : ℂ) ^ k = 1 := div_self (pow_ne_zero _ hl0)
    linear_combination (-P1) * hab + (P0 / (l : ℂ) ^ k) * hαβ + (χ⁻¹ (l : ZMod N) * P0) * key + (-β * P1) * hcan

end GlobalTheory.EisM
