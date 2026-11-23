import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensInclInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationBLocalZetaIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedHarmonicPolynomialDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedHarmonicPolynomialIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedHarmonicPolynomialVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationBArchimedeanIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationBGlobalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialsInclusionLeStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl

namespace GlobalTheory.FockInclCyc

theorem tensHarm_map_le' (halg : ∀ (P Q R S : ℕ) (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (x : ℚ),
    (harmTy P Q R S x).map (polIncl P Q r₀ s₀).toLinearMap ≤ harmTy P Q (R + 1) (S + 1) x) (F : Type) [Field F] [NumberField F] (P Q R S : ℕ) (r₀ : Fin (R + 1))
    (s₀ : Fin (S + 1)) (x : InfinitePlace F → ℚ) :
    (tensHarm F P Q R S x).map (tensIncl F P Q r₀ s₀) ≤ tensHarm F P Q (R + 1) (S + 1) x := by
  rw [tensHarm, Submodule.map_span_le]
  rintro _ ⟨f, hf, rfl⟩
  apply Submodule.subset_span
  refine ⟨fun w => polIncl P Q r₀ s₀ (f w), fun w => halg P Q R S r₀ s₀ (x w) ⟨f w, hf w, rfl⟩, ?_⟩
  simp [tensIncl, PiTensorProduct.map_tprod]

theorem exists_cyclic_pair : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ g₀ ∈ fockDeg G₁.M B.ψ B.emb (lowDegInf B G₁.M R₁.p), ∃ f₀ ∈ G.M.Pol B.ψ B.emb,
        R.p f₀ ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p) ∧ R.p f₀ ≠ 0 ∧
        ∀ (ι : Type) (s : Finset ι) (c : ι → ℂ) (k : ι → UA σ G.W.J) (k₁ : ι → UA σ G₁.W.J)
          (g : ι → SInf F (Fin a × Fin (a + b))) (f : ι → SInf F (Fin a × Fin (a + (b + 2)))),
          (∀ i ∈ s, k i ∈ KInf σ G.W B.emb ∧ k₁ i ∈ KInf σ G₁.W B.emb ∧ IsLevi H' 1 (k₁ i) (k i) ∧
            Acts (evI F) (om₁ (1, k₁ i)) g₀ (g i) ∧ Acts (evI F) (om (1, k i)) f₀ (f i)) →
          ∑ i ∈ s, c i • R₁.p (g i) = 0 → ∑ i ∈ s, c i • R.p (f i) = 0 := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hCfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  obtain ⟨P, Q, R₀, S₀, A, C₁, C, Φ₁, Φ, r₀, s₀, hD₁, hD, hAd, hCo⟩ :=
    GlobalTheory.T.configuration_b_local_zeta_identity hKP F E σ B a b G G₁ H H' hCfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hLow₁ := GlobalTheory.T.matched_harmonic_polynomial_integral hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hM₁ P Q R₀ S₀ A C₁ Φ₁ hD₁
  have hLow := GlobalTheory.T.matched_harmonic_polynomial_integral hKP F E σ B a (b + 2) G X om om' R Rf hM P Q (R₀ + 1) (S₀ + 1) A C Φ hD
  have hC₁ := GlobalTheory.T.matched_harmonic_polynomial_decomposition hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hM₁ P Q R₀ S₀ A C₁ Φ₁ hD₁
  have hC := GlobalTheory.T.matched_harmonic_polynomial_decomposition hKP F E σ B a (b + 2) G X om om' R Rf hM P Q (R₀ + 1) (S₀ + 1) A C Φ hD
  have hS₁ := GlobalTheory.T.matched_harmonic_polynomial_vanishing hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hM₁ P Q R₀ S₀ A C₁ Φ₁ hD₁
  have hE := GlobalTheory.T.configuration_b_global_integral hKP F E σ B a b G G₁ H H' hCfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ P Q R₀ S₀ A C₁ C Φ₁ Φ r₀ s₀
    hD₁ hD hAd hCo
  have hQ := GlobalTheory.T.configuration_b_archimedean_integral hKP F E σ B a b G G₁ H H' hCfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ P Q R₀ S₀ A C₁ C Φ₁ Φ r₀ s₀
    hD₁ hD hAd hCo
  have hA := tensHarm_map_le' GlobalTheory.T.harmonic_polynomials_inclusion_le F P Q R₀ S₀ r₀ s₀ (halfKap B)
  have hΦ₁ : Function.Injective Φ₁ := hD₁.2.1
  have hΦ : Function.Injective Φ := hD.2.1
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLow₁.2
  have hTi : tensIncl F P Q r₀ s₀ T ∈ tensHarm F P Q (R₀ + 1) (S₀ + 1) (halfKap B) := hA ⟨T, hT, rfl⟩
  have hf₀deg : Φ (tensIncl F P Q r₀ s₀ T) ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p) := hLow.1 ⟨_, hTi, rfl⟩
  have hf₀pol : Φ (tensIncl F P Q r₀ s₀ T) ∈ G.M.Pol B.ψ B.emb := fockDeg_le_pol _ _ _ _ hf₀deg
  refine ⟨Φ₁ T, hLow₁.1 ⟨T, hT, rfl⟩, Φ (tensIncl F P Q r₀ s₀ T), hf₀pol, ?_, ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨⟨_, hf₀deg, rfl⟩, ?_⟩
    intro k hk t ht f hf f₁ hff₁ hpf
    obtain ⟨f', hf', hpf'⟩ : ∃ f' ∈ G.M'.Pol B.ψ B.emb, R.p' f' = R.p f := by
      have hmem : R.p f ∈ (G.M'.Pol B.ψ B.emb).map R.p' := hM.real.quot'.onto ▸ Submodule.mem_top
      obtain ⟨f', hf', e⟩ := hmem
      exact ⟨f', hf', e⟩
    obtain ⟨Aop, hAop⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V' G.W G.M' om' X.α (X.α / X.β) hM.triple.base
      hM.triple.geo.hM' hM.triple.weil' k hk
    have h1 := hM.real.cpt k hk f hf f' hf' f₁ (Aop f') hff₁ (hAop f') hpf'.symm
    have h2 := hM.real.cpt k hk _ hf₀pol f' hf' _ (Aop f') (hE k hk t ht T) (hAop f') (hpf'.trans hpf).symm
    rw [h1, ← h2, map_smul]
  · intro h0
    apply hT0
    have h1 : Φ (tensIncl F P Q r₀ s₀ T) = 0 := hC _ ⟨_, hTi, rfl⟩ h0
    apply tensIncl_injective F P Q r₀ s₀
    apply hΦ
    rw [h1, map_zero, map_zero]
  · intro ι s c k k₁ g f hyp hsum
    have hg : ∀ i ∈ s, ∃ Ti ∈ tensHarm F P Q R₀ S₀ (halfKap B), Φ₁ Ti = g i := by
      intro i hi
      obtain ⟨hk, hk₁, hL, hg, hf⟩ := hyp i hi
      obtain ⟨Ti, hTi, e⟩ := hS₁ (k₁ i) hk₁ (Φ₁ T) ⟨T, hT, rfl⟩ (g i) hg
      exact ⟨Ti, hTi, e⟩
    choose! Tf hTf hgT using hg
    have hfT : ∀ i ∈ s, f i = Φ (tensIncl F P Q r₀ s₀ (Tf i)) := by
      intro i hi
      obtain ⟨hk, hk₁, hL, hg, hf⟩ := hyp i hi
      have h1 := hQ (k₁ i) hk₁ (k i) hk hL T (Tf i) (by rw [hgT i hi]; exact hg)
      exact (GlobalTheory.RealLift.actsLaws F _ _ (f i) _).2.2.2.1 _ hf h1
    have hsumT : ∑ i ∈ s, c i • Tf i = 0 := by
      have hmem : ∑ i ∈ s, c i • g i ∈ (tensHarm F P Q R₀ S₀ (halfKap B)).map Φ₁ :=
        Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (by rw [← hgT i hi]; exact ⟨Tf i, hTf i hi, rfl⟩)
      have h0 : R₁.p (∑ i ∈ s, c i • g i) = 0 := by simpa [map_sum, map_smul] using hsum
      have h2 := hC₁ _ hmem h0
      apply hΦ₁
      rw [map_sum, map_zero, ← h2]
      exact Finset.sum_congr rfl fun i hi => by rw [map_smul, hgT i hi]
    calc ∑ i ∈ s, c i • R.p (f i) = R.p (Φ (tensIncl F P Q r₀ s₀ (∑ i ∈ s, c i • Tf i))) := by
          simp only [map_sum, map_smul]
          exact Finset.sum_congr rfl fun i hi => by rw [hfT i hi]
      _ = 0 := by rw [hsumT, map_zero, map_zero, map_zero]

end GlobalTheory.FockInclCyc
