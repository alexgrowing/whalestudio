import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneMeasureNormalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneHaarDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfClosedCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneJacobianIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneIntertwiningIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KfinOfInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneLeviActionFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneConstantTermFormulaStatement
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

namespace GlobalTheory.ThK.CuspTransfer

theorem exists_cuspOn_transfer : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ χ : Chr F E, (∀ t : Eˣ, χ (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) = 1) → Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K₁ →
      ∀ ψ : GAd σ (c₀ • W₁.J.map σ) → ℂ, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ ψ →
      ∃ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K' ∧
        ∃ Ψ : GAd σ (c₀ • W.J.map σ) → ℂ, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W.J.map σ) X' Y' (insert 0 (S'.map (Fin.succEmb r))) K' Ψ ∧
          ∀ (t : (AE F E)ˣ) (m : UA σ W.J) (y : GAd σ (c₀ • W₁.J.map σ)), IsLevi (W₁ := W₁) H t 1 m →
            Ψ (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (m * M ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm y))) = (χ t : ℂ) * ψ y := by
  intro hKP F E _ _ _ _ _ σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc S' χ hχ hχc K₁ hK₁ ψ hψ
  obtain ⟨K', hK', Kc, d, ψs, a, Ψ, hI, hψs, h0, ha1, c1, c2, c3, c4, c5⟩ := GlobalTheory.T.skew_plane_measure_normalization F E σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc S' χ hχ hχc K₁ hK₁ ψ hψ
  have hcont := GlobalTheory.ThK.CuspTransfer.continuous_of_isInd F E σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc S' χ hχ hχc K₁ hK₁ K' hK' Kc (d + 1) ψs a Ψ hI hψs c1 c3
  obtain ⟨hlN, hlM⟩ := GlobalTheory.T.skew_plane_haar_decomposition F E σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc S' χ hχ hχc K₁ hK₁ K' hK' Kc (d + 1) ψs a Ψ hI hψs
  refine ⟨K', hK', Ψ, ⟨⟨hlN, hlM, ?_, hcont, GlobalTheory.T.skew_plane_jacobian_identity F E σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc S' χ hχ hχc K₁ hK₁ K' hK' Kc (d + 1) ψs a Ψ hI hψs c1 c3 c4, GlobalTheory.T.skew_plane_intertwining_identity F E σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc S' χ hχ hχc K₁ hK₁ K' hK' Kc (d + 1) ψs a Ψ hI hψs c1 c3 c4 c5,
    GlobalTheory.ThK.CuspTransfer.kfin_of_ind F E σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc S' χ hχ hχc K₁ hK₁ K' hK' Kc (d + 1) ψs a Ψ hI hψs c1 c5, GlobalTheory.T.skew_plane_levi_action_formula hKP F E σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc S' χ hχ hχc K₁ hK₁ K' hK' Kc (d + 1) ψs a Ψ hI hψs c1 c3 c4 c5⟩, GlobalTheory.T.skew_plane_constant_term_formula F E σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc S' χ hχ hχc K₁ hK₁ K' hK' Kc (d + 1) ψs a Ψ hI hψs c1 hcont⟩, ?_⟩
  · obtain ⟨U, hU, hU'⟩ := c2
    refine ⟨U, hU, fun k hk hkf g => ?_⟩
    obtain ⟨u, hu, t, m, y, k₀, hk₀, hm, rfl⟩ := hI.1 g
    obtain ⟨hk1, hk2⟩ := hU' k hk hkf k₀ hk₀
    rw [mul_assoc, hI.2 u hu t m y _ hk1 hm, hI.2 u hu t m y k₀ hk₀ hm]
    simp only [hk2]
  · intro t m y hm
    have e := hI.2 1 (one_mem _) t m y 1 c1.2.1 hm
    rw [one_mul, mul_one] at e
    rw [map_mul]
    refine e.trans ?_
    simp [ha1, h0]

end GlobalTheory.ThK.CuspTransfer
