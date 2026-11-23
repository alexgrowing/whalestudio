import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSqFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalCompactInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalCompactInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFramePolynomialDataInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFramePolynomialDataDualStatement

noncomputable section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut

namespace GlobalTheory.ThK.SquareIntegrability

theorem sqInt_of_negExp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hP : GlobalTheory.Published.AutomorphicFormsUnitary) (hcm : IsCMExt F E σ) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0) (hH : IsHermND σ (c • J.map σ)) (f : UA σ J → ℂ)
    (hA : ∃ K, IsMaxCpt σ (c • J.map σ) K ∧ IsAut σ (c • J.map σ) K (fun x => f ((toGAd hσ J hc).symm x)))
    (hE : ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ (c • J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • J.map σ) K → IsAut σ (c • J.map σ) K (fun x => f ((toGAd hσ J hc).symm x)) →
          ∀ S s, GlobalTheory.StdPar.IsCuspExp σ (c • J.map σ) Xf Yf S K (fun x => f ((toGAd hσ J hc).symm x)) s →
            ∀ k ∈ S, ∑ i with i ≤ k, (s i).re < 0)
    (μ : Measure (UA σ J)) (𝓕 : Set (UA σ J)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (ratU σ J) 𝓕 μ) :
    IntegrableOn (fun h => ‖f h‖ ^ 2) 𝓕 μ := by
  obtain ⟨r, Xf, Yf, hW⟩ := exists_isWittFrame hcm hH
  obtain ⟨K, hK, hAut⟩ := hA
  have h1 := (GlobalTheory.StdPar.isSqInt_iff hP.1 hcm hH hW hK hAut).2 (hE r Xf Yf hW K hK hAut)
  have h2 := GlobalTheory.T.integrableOn_sq_fundamental_domain F E σ hσ n J c hc _ h1 μ 𝓕 hμ h𝓕
  simpa using h2

end GlobalTheory.ThK.SquareIntegrability

open GlobalTheory.ThK.SquareIntegrability in

theorem GlobalTheory.ThK.sqInt : GlobalTheory.ThK.KP → GlobalTheory.ThK.SqInt := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT μ 𝓕 hμ h𝓕
  have hcm := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hcm
  obtain ⟨c, hc, hcs⟩ := GlobalTheory.T.exists_purely_imaginary_element F E σ hcm
  have hH := GlobalTheory.T.isHermND_smul_skew_form F E σ B _ G.W _ _ hT.geo.hW c hc hcs
  refine ⟨fun Φ hΦ => ?_, fun Φ' hΦ' => ?_⟩
  · exact sqInt_of_negExp hK.automorphicFormsUnitary hcm hσ G.W.J hc hH _
      (GlobalTheory.T.exists_maximal_compact_invariant F E σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ)
      (GlobalTheory.T.witt_frame_polynomial_data_invariant F E σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ) μ 𝓕 hμ h𝓕
  · exact sqInt_of_negExp hK.automorphicFormsUnitary hcm hσ G.W.J hc hH _
      (GlobalTheory.T.exists_maximal_compact_invariant_dual F E σ hσ B a a' G X om om' hK hT c hc hcs Φ' hΦ')
      (GlobalTheory.T.witt_frame_polynomial_data_dual F E σ hσ B a a' G X om om' hK hT c hc hcs Φ' hΦ') μ 𝓕 hμ h𝓕

example : GlobalTheory.ThK.KP → GlobalTheory.ThK.SqInt := GlobalTheory.ThK.sqInt

end
