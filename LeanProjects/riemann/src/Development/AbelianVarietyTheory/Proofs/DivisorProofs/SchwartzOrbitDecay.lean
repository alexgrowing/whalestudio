import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSiegelDomainDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SoDecayOfUnifStatement

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.ThKSoDecay

theorem soDecayUnif (hP : KP) : SoDecayUnif := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair φ hφ hφS N
  obtain ⟨q, x, y, hxy, Cc, c, C0, A, hCc, hc, hcov⟩ :=
    GlobalTheory.T.exists_siegel_domain_reduction hP.siegelSetUnitary F E σ B n X r s hPair.base hPair.herm
  obtain ⟨C1, k, hC1⟩ := GlobalTheory.T.schwartz_siegel_domain_decay hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy Cc hCc c hc φ hφ hφS (A * N)
  have hB := GlobalTheory.T.theta_basic_properties hP.base F E σ B n d X W M χX χW om r s r' s' hPair
  refine ⟨max C0 0 ^ N * C1, k, fun f g h => ?_⟩
  obtain ⟨γ, hγ, t, a, κ, ht', ha, hκ, hg, hht⟩ := hcov g
  have hΦ : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have e : theta om (pureA F f φ) g h = theta om (pureA F f φ) (a * κ) h := by
    rw [← hg]
    have := (hB.1 _ hΦ).2.1 γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    exact this.symm
  have hP0 : (0 : ℝ) ≤ 1 + ∏ i, t i :=
    add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => hc.le.trans (ht' i))
  have hq : (qht g : ℝ) ≤ max C0 0 * (1 + ∏ i, t i) ^ A := by
    have h1 : qht g ≤ ht (a * κ) := by
      rw [← hg]
      exact ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ X.J)
    exact (NNReal.coe_le_coe.2 h1).trans (hht.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hP0 A)))
  have hC0 : (0 : ℝ) ≤ max C0 0 := le_max_right _ _
  calc ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N
      ≤ ‖theta om (pureA F f φ) (a * κ) h‖ * (max C0 0 * (1 + ∏ i, t i) ^ A) ^ N := by
        rw [e]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hq N) (norm_nonneg _)
    _ = max C0 0 ^ N * (‖theta om (pureA F f φ) (a * κ) h‖ * (1 + ∏ i, t i) ^ (A * N)) := by
        rw [mul_pow, pow_mul]; ring
    _ ≤ max C0 0 ^ N * (C1 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (hC1 f t a κ h ht' ha hκ) (pow_nonneg hC0 N)
    _ = max C0 0 ^ N * C1 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k := by ring

theorem soDecay (hP : KP) : SoDecay := GlobalTheory.T.soDecay_of_prints_of_soDecayUnif hP.base (soDecayUnif hP)

end GlobalTheory.ThKSoDecay
