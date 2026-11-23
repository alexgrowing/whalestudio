import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionHolds
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddOfMemHolSub

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem isBddSec_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ (la : Wt X.Ψ r) (N k m : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (cf : ℕ → MvPolynomial (Fin N) ℂ) (g : Frame X.Ψ r → ℂ), (∀ i, X.IsBddSec la (w i)) → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → X.IsSec (k • la) g → (∀ x ∈ X.dom, g x * g x ^ m + ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i = 0) → X.IsBddSec (k • la) g := by
  intro E _ _ _ r X la N k m w cf g hw hcf hg heq
  refine ⟨hg, ?_⟩
  choose B hB using fun i => (hw i).2
  obtain ⟨C, hC0, hC⟩ := IntegralCusp.exists_root_bound N k m cf hcf
  refine ⟨C * (∑ i, |B i|) ^ k, fun x hx => ?_⟩
  have h2 := hC _ _ (heq x hx)
  set ν := X.nfac la x with hν
  have hν0 : 0 ≤ ν := Formalism.L2.PjFree.pnorm_fac_nonneg _ _ _
  have h3 : ‖fun i => w i x‖ * ν ≤ ∑ i, |B i| := by
    rw [mul_comm, ← Real.norm_of_nonneg hν0, ← norm_smul,
      pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    intro i
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hν0, mul_comm]
    exact ((hB i x hx).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  show ‖g x‖ * X.nfac _ x ≤ _
  rw [IntegralCusp.nfac_nsmul X la (k • la) k (fun τ i => by simp), ← hν]
  calc _ ≤ C * ‖fun i => w i x‖ ^ k * ν ^ k :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = C * (‖fun i => w i x‖ * ν) ^ k := by ring
    _ ≤ _ := by gcongr

end GlobalTheory
