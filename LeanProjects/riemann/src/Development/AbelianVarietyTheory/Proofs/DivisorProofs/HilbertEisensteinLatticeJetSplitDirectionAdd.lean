import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinJetSplitLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreDerivativePolynomialValueAdd

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma piFinset_range_succ_eq_Iic {ι : Type} [Fintype ι] [DecidableEq ι] (κ : ι → ℕ) :
    Fintype.piFinset (fun i => Finset.range (κ i + 1)) = Finset.Iic κ := by
  ext μ
  simp [Fintype.mem_piFinset, Finset.mem_range, Finset.mem_Iic, Pi.le_def, Nat.lt_succ_iff]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.jet_split_add : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ), Even k → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) μ τ c t := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t v κ hk ha hτ
  have hμ := fun μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ =>
    ((_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ c t μ hk ha hτ).mul_left
      (((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i))))
  have hs := hasSum_sum (s := Finset.Iic κ) fun μ _ => hμ μ
  refine (_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ (c + v) t κ hk ha hτ).unique
    (hs.congr_fun fun ξ => ?_)
  simp_rw [_root_.GlobalTheory.HilbFam.lag_add, Finset.prod_univ_sum, piFinset_range_succ_eq_Iic,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

end GlobalTheory.HilbFam
