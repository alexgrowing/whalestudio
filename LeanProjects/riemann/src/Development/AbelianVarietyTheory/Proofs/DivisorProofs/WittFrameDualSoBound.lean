import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterExponentListStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMaximalCompactLocalConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelGlExponentsStatement

noncomputable section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.SplitWeil GlobalTheory.SmGL

open GlobalTheory.LeviBlockExponent in
theorem GlobalTheory.ThK.RealPartAlt.realPart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) →
          ∀ S s, GlobalTheory.StdPar.IsCuspExp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) s →
            (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → ∀ i ∈ S, ∃ j : ℕ, j ≤ i.val ∧
              ((s i).re = (1 - (a : ℝ)) / 2 + j ∨ (s i).re = (1 - (a' : ℝ)) / 2 + j) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ r Xf Yf hW K hKc hAut S s hs hS i hi
  have hcm := hT.base.cm
  have hH := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B _ G.W _ _ hT.geo.hW c hc hcs
  obtain ⟨ϖ, -, hϖ⟩ := GlobalTheory.CentralExponent.exists_nabs_lt_one (k := Fv F B.v₁)
  have hϖ0 := nabs_pos' (Fv F B.v₁) ϖ
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.T.unitary_maximal_compact_local_conj F E σ hcm (a + a') (c • G.W.J.map σ) hH r Xf Yf hW hK.automorphicFormsUnitary.2 B.v₁ B.τ₁
  obtain ⟨b, hb, χ, hbab, hχs, hχu, m, T, x, hTi, hφ⟩ := GlobalTheory.T.polynomial_theta_kernel_gl_exponents F E σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ B₀
  obtain ⟨hin, hmain⟩ := hB₀ K hKc _ hAut _ (pairInd _ b hb χ) (isSmooth_parInd _ _) m T x hTi hφ S s hs hS i hi
  obtain ⟨L, hL, hLp⟩ := GlobalTheory.T.local_character_exponent_list hK.geometricLemmaFiltration (Fv F B.v₁) (a + a') i hin b hb χ hχs hχu ϖ
  obtain ⟨c', hc'L, hc'⟩ := hmain hin ϖ L hLp
  obtain ⟨j, l, hl, hl'⟩ := hL c' hc'L
  have hre : (s i).re = (1 - (b j : ℝ)) / 2 + l := by
    have e := hc'.symm.trans hl'
    have e2 := congrArg Real.log e
    rw [Real.log_rpow hϖ0, Real.log_rpow hϖ0] at e2
    exact mul_right_cancel₀ (Real.log_neg hϖ0 hϖ).ne e2
  refine ⟨l, hl, ?_⟩
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  have hbj : b j = a ∨ b j = a' := by
    rcases hj with rfl | rfl <;> rcases hbab with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1]
  rcases hbj with e | e
  · exact Or.inl (by rw [hre, e])
  · exact Or.inr (by rw [hre, e])

end
