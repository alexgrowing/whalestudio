import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

namespace GlobalTheory.KerSubInf

theorem actsD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have h0 : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero]
  simpa using hasDerivAt_const (0:ℝ) (0:ℂ)

theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have h0 : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by
    funext y; simp [tens]
  rw [h0, map_zero]

theorem kerSub : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → GlobalTheory.Published.ThetaSubInf G.M B.ψ B.emb om (G.M.Pol B.ψ B.emb ⊓ LinearMap.ker R.p) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  have hP := GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hM.triple
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hP
  refine ⟨inf_le_left, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ hA
    exact ⟨hP1 γ hγ f hf f₁ hA, hM.real.quot.lie γ hγ f hf f₁ hA⟩
  · intro k hk f hf f₁ hA
    refine ⟨sub_mem (hP2 k hk f hf f₁ hA) hf, ?_⟩
    show R.p (f₁ - f) = 0
    rw [map_sub, hM.real.quot.cpt k hk f hf f₁ hA, sub_self]
  · intro γ hγ f hf f₁ hA
    obtain ⟨g, hg, _, hu⟩ := hP3 γ hγ f hf.1
    refine ⟨hu f₁ hA ▸ hg, ?_⟩
    show R.p f₁ = 0
    have hf0 : R.p f = 0 := hf.2
    have := hM.real.lie γ hγ f hf.1 0 (zero_mem _) f₁ 0 hA
      (actsD_zero (fun t => om' (1, γ (Multiplicative.ofAdd t)))) (by rw [hf0, map_zero])
    rw [this, map_zero]
  · intro k hk f hf f₁ hA
    obtain ⟨g, hg, _, hu⟩ := hP4 k hk f hf.1
    refine ⟨hu f₁ hA ▸ hg, ?_⟩
    show R.p f₁ = 0
    have hf0 : R.p f = 0 := hf.2
    have := hM.real.cpt k hk f hf.1 0 (zero_mem _) f₁ 0 hA
      (acts_zero (om' (1, k))) (by rw [hf0, map_zero])
    rw [this, map_zero]

end GlobalTheory.KerSubInf
