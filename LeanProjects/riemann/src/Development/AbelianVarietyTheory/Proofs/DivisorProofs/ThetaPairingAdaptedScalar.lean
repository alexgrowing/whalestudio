import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetSmoothModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicThetaLiftNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactPolDataPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataWittFrameScaledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataSoWittFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermNonzeroVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermIsotropicVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicLinearCombinationConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicSubScalarMulStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThKDecayAny

theorem decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      ∀ Φ ∈ PolData B G.M, ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      IsCT H' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) 0 →
      ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ N ≤ C := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH' c Φ hΦd Φ' hΦ' hCT N
  have h : IsCMExt F E σ := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma h
  obtain ⟨c₁, hc₁, hc₁σ⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ h
  have hJ₁ := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B (a + a') G.W _ _ hT.geo.hW c₁ hc₁ hc₁σ
  obtain ⟨K, hK, hAV, hAV'⟩ := GlobalTheory.T.max_compact_pol_data_pair F E σ hσ B a a' G X om om' hKP hT c₁ hc₁ hc₁σ Φ hΦd Φ' hΦ'
  have hA : GlobalTheory.UAut.IsAut σ (c₁ • G.W.J.map σ) K (fun x => G.M.I om Φ ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ G.W.J hc₁).symm x) -
      c * G.M'.I om' Φ' ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ G.W.J hc₁).symm x)) :=
    GlobalTheory.StdPar.isAutOn_empty.1 (GlobalTheory.T.automorphic_sub_scalar_mul F E σ (a + a') _ 0 (0 : Matrix (Fin (a + a')) (Fin 0) E) 0 ∅ K _ _ c
      (GlobalTheory.StdPar.isAutOn_empty.2 hAV) (GlobalTheory.StdPar.isAutOn_empty.2 hAV'))
  obtain ⟨hx0, hxiso, hct⟩ := GlobalTheory.T.constant_term_nonzero_vector F E σ hσ B (a + a') d₁ G.W W₁ H' i₀ i₁ _ _ hT.geo.hW hH' c₁ hc₁ _ hCT
  have hcusp := GlobalTheory.ThKOrthCusp.core h hJ₁ hKP.automorphicFormsUnitary.2 hK hA
    (fun x hx hxi => GlobalTheory.T.constant_term_isotropic_vectors F E σ h (a + a') _ hJ₁ _ hA.mod.left _ x hx0 hxiso hx hxi hct)
    (fun r Xf Yf hW S hS => by
      have h1 := GlobalTheory.T.pol_data_witt_frame_scaled F E σ hσ B a a' G X om om' hKP hT c₁ hc₁ hc₁σ Φ hΦd r Xf Yf hW K hK hAV S hS
      have h2 := GlobalTheory.T.pol_data_so_witt_frame F E σ hσ B a a' G X om om' hKP hT c₁ hc₁ hc₁σ Φ' hΦ' r Xf Yf hW K hK hAV' S hS
      have := GlobalTheory.T.automorphic_linear_combination_const F E σ h (a + a') _ hJ₁ r Xf Yf hW K S _ _ 0 0 c (GlobalTheory.StdPar.isAutOn_empty.2 hAV)
        (GlobalTheory.StdPar.isAutOn_empty.2 hAV') h1 h2
      convert this using 1
      funext x; simp)
  have hφ₁ : ∀ (g : UA σ G.W.J) (g' : GAd σ (c₁ • G.W.J.map σ)), g.1 = g'.1 →
      (fun x => G.M.I om Φ ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ G.W.J hc₁).symm x) -
        c * G.M'.I om' Φ' ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ G.W.J hc₁).symm x)) g' = G.M.I om Φ g - c * G.M'.I om' Φ' g := by
    intro g g' e
    have : (GlobalTheory.ThK.SquareIntegrability.toGAd hσ G.W.J hc₁).symm g' = g := Subtype.ext e.symm
    simp only [this]
  exact GlobalTheory.SiegelSet.rapidDecay_qht hKP.siegelSetUnitary F E σ h _ G.W.J c₁ hc₁ hJ₁ _ _ hφ₁ hA.mod hcusp N

end GlobalTheory.ThKDecayAny
