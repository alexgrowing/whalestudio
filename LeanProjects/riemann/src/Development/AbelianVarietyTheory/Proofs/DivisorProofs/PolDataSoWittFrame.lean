import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRationalFrameExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSubquotientPrincipalSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesIrreducibleStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThK.CuspidalComponentGap

theorem exists_gap {r : ℕ} {S : Finset (Fin r)} (h : ¬ ∀ k ∈ S, ∀ i ≤ k, i ∈ S) :
    ∃ k ∈ S, ∃ i : Fin r, i < k ∧ ∀ j : Fin r, i ≤ j → j < k → j ∉ S := by
  classical
  push Not at h
  obtain ⟨k, hk, i, hik, hi⟩ := h
  have hne : (S.filter (i ≤ ·)).Nonempty := ⟨k, Finset.mem_filter.2 ⟨hk, hik⟩⟩
  have h0 := Finset.mem_filter.1 (Finset.min'_mem _ hne)
  refine ⟨_, h0.1, i, lt_of_le_of_ne h0.2 fun e => hi (e ▸ h0.1), fun j hij hjk hj => ?_⟩
  exact absurd (Finset.min'_le _ j (Finset.mem_filter.2 ⟨hj, hij⟩)) (not_le.2 hjk)

theorem cuspComp_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ' ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M'.I om' Φ' ((toGAd hσ G.W.J hc).symm x)) →
          ∀ S : Finset (Fin r), ¬ (∀ k ∈ S, ∀ i ≤ k, i ∈ S) →
            GlobalTheory.StdPar.IsCuspComp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M'.I om' Φ' ((toGAd hσ G.W.J hc).symm x)) 0 := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S hno
  have hcm := hT.base.cm
  haveI : IsTotallyComplex E := hcm.2.1
  have hH := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B _ G.W _ _ hT.geo.hW c hc hcs
  obtain ⟨φc, hφc, -⟩ := (hKP.automorphicFormsUnitary.2 F E σ hcm (a + a') _ hH r Xf Yf hW K hK ∅ _
    (GlobalTheory.StdPar.isAutOn_empty.2 hA)).1 S (Finset.empty_subset _)
  by_cases h0 : φc = 0
  · exact h0 ▸ hφc
  exfalso
  obtain ⟨k, hk, i, hik, hgap⟩ := exists_gap hno
  obtain ⟨w, x, x', τ, χ₁, χ₂, s₁, s₂, h2, hu₁, hu₂, hn₁, hn₂, hs, V, _, _, Q, hQ, f, hf⟩ :=
    GlobalTheory.T.theta_integral_rational_frame_expansion F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S φc hφc h0 k hk i hik hgap
  have unr : ∀ {χ : (w.adicCompletion E)ˣ →* ℂˣ} (t : ℝ), GlobalTheory.SplitWeil.IsUnram χ →
      GlobalTheory.SmGL.IsSmoothChar (χ * GlobalTheory.SmGL.absPow (w.adicCompletion E) (t : ℂ)) := fun t h =>
    GlobalTheory.SmGL.isSmoothChar_of_isUnram fun u hu => by
      rw [MonoidHom.mul_apply, h u hu, GlobalTheory.SmGL.isUnram_absPow _ _ u hu, mul_one]
  obtain ⟨hx, hx'⟩ := GlobalTheory.T.generic_subquotient_principal_series E x x' τ w _ _ hKP.genericityGL (unr s₁ hu₁) (unr s₂ hu₂) V Q hQ f hf
  obtain rfl : x = 1 := by omega
  obtain rfl : x' = 1 := by omega
  exact GlobalTheory.T.unramified_principal_series_irreducible E τ w χ₁ χ₂ s₁ s₂ hKP.jacquetShalika.2 hu₁ hu₂ hn₁ hn₂ (hs rfl rfl) V Q hQ f hf

end GlobalTheory.ThK.CuspidalComponentGap
