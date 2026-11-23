import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqUnitaryEmbeddingOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompSmulLatticeEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtAbsNormLeProdNormCmTypeEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeNormRationalTranslateStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.LongSum

theorem long_sum : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (Λ : Lat Y) (x : GA D Y) (s : ℝ), IsSelfDualC Y Λ → 0 ≤ s → s ≤ 1 → Long θ A Λ x s → Long θ B (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) s ∧ (∀ τ, nrm θ B (stabilizerEmbedding d x) τ (zv d) = 1) ∧ ∀ (γ : GA D V) z, γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z → ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  intro D θ hθ Y V d A B hAd Λ x s _ hs0 hs1 hL
  have hzero : ∀ τ, nrm θ A x τ 0 = 0 := fun τ => by
    have e : (fun i => tauE D τ ((0 : Fin Y.rank → D.host.E) i)) = 0 := by funext i; simp
    unfold nrm
    rw [e, mulVec_zero, mulVec_zero]
    simp [eu]
  have hz : ∀ τ (u : D.host.E), nrm θ B (stabilizerEmbedding d x) τ (u • zv d) = ‖tauE D τ u‖ := fun τ u => by
    have h := GlobalTheory.T.norm_sq_unitaryEmbedding_orthogonal D θ hθ Y V d A B hAd x τ 0 u
    rw [mulVec_zero, zero_add, hzero] at h
    have h2 : nrm θ B (stabilizerEmbedding d x) τ (u • zv d) ^ 2 = ‖tauE D τ u‖ ^ 2 := by rw [h]; ring
    have h0 : 0 ≤ nrm θ B (stabilizerEmbedding d x) τ (u • zv d) := Real.sqrt_nonneg _
    exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).1 h2
  have hge : ∀ τ y (u : D.host.E), nrm θ A x τ y ≤ nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) := fun τ y u => by
    have h := GlobalTheory.T.norm_sq_unitaryEmbedding_orthogonal D θ hθ Y V d A B hAd x τ y u
    have h0 : 0 ≤ nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) := Real.sqrt_nonneg _
    have h1 : 0 ≤ nrm θ A x τ y := Real.sqrt_nonneg _
    nlinarith [sq_nonneg ‖tauE D τ u‖]
  refine ⟨?_, fun τ => ?_, fun γ z hγ hz' τ => GlobalTheory.T.one_le_norm_rational_translate D θ hθ Y V d B x γ z hγ hz' τ⟩
  · intro 𝔪 h𝔪 w hw hw0
    obtain ⟨y, hy, u, hu, rfl⟩ := GlobalTheory.T.exists_decomp_smul_lattice_embedding D Y V d Λ x 𝔪 w hw
    by_cases hy0 : y = 0
    · subst hy0
      rw [mulVec_zero, zero_add] at hw0 ⊢
      have hu0 : u ≠ 0 := by
        rintro rfl; exact hw0 (by simp)
      have e : ∏ τ, nrm θ B (stabilizerEmbedding d x) τ ((u : D.host.E) • zv d) = ∏ τ, ‖tauE D τ (u : D.host.E)‖ :=
        Finset.prod_congr rfl fun τ _ => hz τ _
      rw [e]
      refine le_trans ?_ (GlobalTheory.T.sqrt_absNorm_le_prod_norm_cmTypeEmbeddings D 𝔪 u hu hu0)
      have h1 : s ^ Fintype.card D.what₂.Tau ≤ 1 := pow_le_one₀ hs0 hs1
      have h2 : 0 ≤ Real.sqrt (Ideal.absNorm 𝔪) := Real.sqrt_nonneg _
      nlinarith
    · refine le_trans (hL 𝔪 h𝔪 y hy hy0) ?_
      exact Finset.prod_le_prod (fun τ _ => Real.sqrt_nonneg _) fun τ _ => hge τ y u
  · have h := hz τ 1
    rw [one_smul, map_one, norm_one] at h
    exact h

end GlobalTheory.SepPer.LongSum

end
