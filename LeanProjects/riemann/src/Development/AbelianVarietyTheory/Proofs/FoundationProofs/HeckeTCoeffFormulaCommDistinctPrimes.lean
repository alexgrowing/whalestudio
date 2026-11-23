import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGamma1InterGamma0ExtQExpansionCoeffStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommutesDiamondStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCongrStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixModularFormGamma1InterGamStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCompMulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffHeckeTOperatorGamma1InterGamma0Statement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitModularFormStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma isDia_mul_of_isDia {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : IsDia N l d σ)
    (hτ : IsDia N l e τ) : IsDia N l (d * e) (σ * τ) := by
  obtain ⟨h1, h2⟩ := hσ
  obtain ⟨h3, h4⟩ := hτ
  have h1' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) h1
    simpa using this
  refine ⟨?_, ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1, h3]; ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1', h2, h4]; ring

lemma heckeT_congr_dia {N l q : ℕ} {k : ℤ} {σ τ : SL(2, ℤ)} (hN : 0 < N)
    (hσ : IsDia N l q σ) (hτ : IsDia N l q τ) (f : ModularForm (lev N l) k) :
    heckeT k q σ ⇑f = heckeT k q τ ⇑f := by
  have := GlobalTheory.T.diamondOperatorOfMatrix_congr N l k q σ τ hN hσ hτ f
  unfold dia at this
  unfold heckeT
  rw [this]

lemma heckeT_coeff_formula_comm_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) (kq kr : ℂ)
    (a b c e : ℕ → ℂ) (n : ℕ) :
    a (r * (q * n)) + kr * (if r ∣ q * n then b (q * n / r) else 0)
      + kq * (if q ∣ n then c (r * (n / q)) + kr * (if r ∣ n / q then e (n / q / r) else 0)
        else 0)
    = a (q * (r * n)) + kq * (if q ∣ r * n then c (r * n / q) else 0)
      + kr * (if r ∣ n then b (q * (n / r)) + kq * (if q ∣ n / r then e (n / r / q) else 0)
        else 0) := by
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hqr
  have i1 : r ∣ q * n ↔ r ∣ n := hcop.symm.dvd_mul_left
  have i2 : q ∣ r * n ↔ q ∣ n := hcop.dvd_mul_left
  have ha : r * (q * n) = q * (r * n) := by ring
  simp only [ha, i1, i2]
  by_cases hqn : q ∣ n <;> by_cases hrn : r ∣ n
  · have i3 : r ∣ n / q := by
      obtain ⟨m, rfl⟩ := hqn
      rw [Nat.mul_div_cancel_left _ hq.pos]
      exact (hcop.symm.dvd_mul_left).1 hrn
    have i4 : q ∣ n / r := by
      obtain ⟨m, rfl⟩ := hrn
      rw [Nat.mul_div_cancel_left _ hr.pos]
      exact (hcop.dvd_mul_left).1 hqn
    have d1 : q * n / r = q * (n / r) := Nat.mul_div_assoc q hrn
    have d2 : r * n / q = r * (n / q) := Nat.mul_div_assoc r hqn
    have d3 : n / r / q = n / q / r := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    simp only [hqn, hrn, i3, i4, if_true, d1, d2, d3]
    ring
  · have i3 : ¬ r ∣ n / q := by
      intro h
      exact hrn (h.trans (Nat.div_dvd_of_dvd hqn))
    have d2 : r * n / q = r * (n / q) := Nat.mul_div_assoc r hqn
    simp only [hqn, hrn, i3, if_true, if_false, d2]
    ring
  · have i4 : ¬ q ∣ n / r := by
      intro h
      exact hqn (h.trans (Nat.div_dvd_of_dvd hrn))
    have d1 : q * n / r = q * (n / r) := Nat.mul_div_assoc q hrn
    simp only [hqn, hrn, i4, if_true, if_false, d1]
    ring
  · simp only [hqn, hrn, if_false]
    ring

theorem heckeT_comm : ∀ (N l q r : ℕ) (k : ℤ) (σ τ : SL(2, ℤ)), 0 < N → q.Prime → r.Prime →
    ¬ q ∣ N * l → ¬ r ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l r τ →
    ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
      GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.heckeT k r τ ⇑f) = GlobalTheory.Hk.heckeT k r τ (GlobalTheory.Hk.heckeT k q σ ⇑f) := by
  intro N l q r k σ τ hN hq hr hqN hrN hσ hτ f
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨g, hg⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k τ hN hq hqN hτ f
    rw [heckeT_congr_dia hN hσ hτ f, ← hg, heckeT_congr_dia hN hσ hτ g]
  · obtain ⟨gr, hgr⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l r k τ hN hr hrN hτ f
    obtain ⟨gq, hgq⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k σ hN hq hqN hσ f
    obtain ⟨h1, hh1⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k σ hN hq hqN hσ gr
    obtain ⟨h2, hh2⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l r k τ hN hr hrN hτ gq
    obtain ⟨fσ, hfσ⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k q σ hN hσ f
    obtain ⟨fτ, hfτ⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k r τ hN hτ f
    have dσ : dia k σ ⇑gr = heckeT k r τ ⇑fσ := by
      rw [hgr, hfσ, GlobalTheory.T.hecke_operator_commutes_diamond N l r k q τ σ hN hr hrN hτ hσ f]
    have dτ : dia k τ ⇑gq = heckeT k q σ ⇑fτ := by
      rw [hgq, hfτ, GlobalTheory.T.hecke_operator_commutes_diamond N l q k r σ τ hN hq hqN hσ hτ f]
    have dd : dia k τ ⇑fσ = dia k σ ⇑fτ := by
      have h' : IsDia N l ((r : ℤ) * q) (σ * τ) := by
        rw [mul_comm]; exact isDia_mul_of_isDia hσ hτ
      rw [hfσ, hfτ, GlobalTheory.T.diamondOperatorOfMatrix_comp_mul N l k q r σ τ (σ * τ) hN hσ hτ (isDia_mul_of_isDia hσ hτ) f,
        GlobalTheory.T.diamondOperatorOfMatrix_comp_mul N l k r q τ σ (σ * τ) hN hτ hσ h' f]
    have key : h1 = h2 := by
      apply GlobalTheory.T.modularForm_gamma1InterGamma0_ext_qExpansionCoeff N l k hN
      intro n
      rw [hh1, hh2, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ gr, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ gq,
        dσ, dτ, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ fσ, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ fτ,
        hgr, hgq, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ f, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ f,
        dd, hfσ, hfτ]
      exact heckeT_coeff_formula_comm_distinct_primes hq hr hqr _ _ _ _ _ _ n
    rw [← hgr, ← hgq, ← hh1, ← hh2, key]

end GlobalTheory.Hk
