import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormIffLevelCoverPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChangeStatement

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CoverPull

theorem cusp_pullback_existsUnique : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), ∃! g, g ∈ Y.V (wtZ a n) ∧ Y.Pull f g := by
  intro D T j Y e o hT hj hG hu hm a n hD f hf
  have hL := GlobalTheory.LevGeo.laws_core D T j hT hj
  obtain ⟨hL', hbc⟩ := GlobalTheory.T.moduliLaws_coefficientFieldChange D j _ _ _ _ _ Y.c' Y.hle _ _ hL
  obtain ⟨hf', -⟩ := hbc a n hD ⟨f, hf⟩
  obtain ⟨hL₂, -, hP⟩ := GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hT hj hG hu hm
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q ∧ 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  rw [cuspW_wtZ] at hf hf'
  have hs := cusp_le_sec _ _ _ a n hf
  have hs' := cusp_le_sec _ _ _ a n hf'
  obtain ⟨g, ⟨hg, hgP⟩, huniq⟩ := (GlobalTheory.CoverSec.section_pullback_existsUnique _ _ _ _ _ _ Y.d hpq.2 hG.lev.1
    (Or.inl ⟨hpq.1, hL.levA⟩) a n).1 _ hs'
  refine ⟨g, ⟨?_, (hP a n f hs g).2 hgP⟩, fun g' hg' => huniq g' ⟨?_, (hP a n f hs g').1 hg'.2⟩⟩
  · rw [Deep.V, cuspW_wtZ]
    exact (GlobalTheory.T.cuspForm_iff_levelCover_pullback D j _ _ _ _ _ _ _ Y.d _ _ hL' hL₂ hG.lev.1 a n hD hD.2 _ hs' g hg hgP).2 hf'
  · have h := hg'.1
    rw [Deep.V, cuspW_wtZ] at h
    exact cusp_le_sec _ _ _ a n h

end GlobalTheory.CoverPull
