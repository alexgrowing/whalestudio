import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.NormUniq

theorem wd_rat_mem_TT : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}, Crv D cc δ → ∀ {N N' : ℕ} {x : VC D N N'} {M : ℕ}, 0 < M → M • x ∈ La0 D (tor0 D cc δ) N N' → ∀ {F : VC D N N' → ℂ}, F ∈ TT D (tor0 D cc δ) N N' → Wd D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) N N' := by
  intro D cc δ hc N N' x M hM hx F hF
  obtain ⟨hd, m, hm, hFm⟩ := hF
  have hg := (GlobalTheory.InducedType.induced_type D).1
  have hint := (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg cc δ hc N N' (La0 D (tor0 D cc δ) N N')
    (GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D N) (GlobalTheory.NormSum.VacMove.moves_one D N'))).2.2.1
  refine ⟨GlobalTheory.FinWeil.RatTransl.differentiable_wd x hd, m * M, Nat.mul_pos hm hM, fun y hy => ?_⟩
  have h0 : Wd D (tor0 D cc δ) ((m * M) • y) F = F := by
    rw [mul_smul]; exact hFm _ (AddSubgroup.nsmul_mem _ hy M)
  obtain ⟨k, hk⟩ := hint _ (AddSubgroup.nsmul_mem _ hy m) _ hx
  have e : (m * M) • y = M • (m • y) := by rw [mul_comm, mul_smul]
  funext w
  exact GlobalTheory.FinWeil.RatTransl.wd_wd_of_int h0 k (by rw [e, GlobalTheory.FinWeil.RatTransl.hf_nsmul, hk]) w

end GlobalTheory.FunObj.NormUniq
