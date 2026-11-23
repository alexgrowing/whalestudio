import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionHolds
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecPowSuccAndConstTermPowSucc
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvalIsHomogeneousMemCuspForms
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsBddSecOfIntegral

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem cuspForm_of_integral_over_cuspForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ (la : Wt X.Ψ r) (N k m : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (cf : ℕ → MvPolynomial (Fin N) ℂ) (g : Frame X.Ψ r → ℂ), (∀ i, w i ∈ X.SS la) → 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → X.IsSec (k • la) g → (∀ x ∈ X.dom, g x * g x ^ m + ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i = 0) → g ∈ X.SS (k • la) := by
  intro E _ _ _ r X la N k m w cf g hw hk hcf hg heq
  have hb : X.IsBddSec (k • la) g :=
    isBddSec_of_integral E r X la N k m w cf g (fun i => (hw i).1) hcf hg heq
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ :=
    siegelSpaceAlgebra_holds (E := E) r X ((m + 1) • (k • la)) ((m + 1) • (k • la)) 0
  have hterm : ∀ i ∈ Finset.range m,
      (fun x => MvPolynomial.eval (fun s => w s x) (cf i)) * g ^ (i + 1) ∈
        X.SS ((m + 1) • (k • la)) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.1 hi
    have h1 := eval_isHomogeneous_mem_cuspForms E r X la N ((m - i) * k) w (cf i) hw
      (Nat.mul_pos (Nat.sub_pos_of_lt hi') hk) (hcf i hi')
    have h2 := (bddSec_pow_succ_and_constTerm_pow_succ E r X (k • la) g hb i).1
    have h3 := (siegelSpaceAlgebra_holds (E := E) r X (((m - i) * k) • la) ((i + 1) • (k • la)) 0).2.1 _ h1 _ h2
    have e : ((m - i) * k) • la + (i + 1) • (k • la) = (m + 1) • (k • la) := by
      rw [mul_smul, ← add_smul]
      congr 1
      omega
    rwa [e] at h3
  have hsum := Finset.sum_induction _ (fun P => P ∈ X.SS ((m + 1) • (k • la)))
    (fun a b ha hb => hadd a ha b hb) h0 hterm
  have hneg := hsmul (-1) _ hsum
  refine cuspForm_of_bddSec_of_pow_succ E r X (k • la) g m hb
    ((DomCongr.bddSec_cusp_congr E r X _ _ _ fun x hx => ?_).2 hneg)
  have h := heq x hx
  have e : ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i =
      ∑ i ∈ Finset.range m, MvPolynomial.eval (fun s => w s x) (cf i) * g x ^ (i + 1) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e] at h
  simp only [Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  linear_combination -h

end GlobalTheory
