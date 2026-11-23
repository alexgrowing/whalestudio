import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspAlt
import Development.AutomorphicArithmetic.LocalEmbeddings.IterateDopSum
import Development.AutomorphicArithmetic.LocalEmbeddings.SmoothInfTransp
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem _root_.GlobalTheory.T.matched_rep_local_factor_second : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (L : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), GlobalTheory.ThKAdm.IsLevel G.W L → ∀ (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (e : I.GA →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), 1 ≤ g → GlobalTheory.ThKAdm.IsTransp B G.W L I g e → ∃ (N : InfinitePlace I.F → ℕ → ℕ) (c : ∀ v m, Fin (N v m) → ℂ), ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ v m x, (GlobalTheory.Dec.zOp I v m)^[N v m] (fun y => G.M'.I om' Ψ (e y)) x = ∑ i, c v m i * (GlobalTheory.Dec.zOp I v m)^[i.val] (fun y => G.M'.I om' Ψ (e y)) x := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM L _ I g e _ he
  have hT := hM.triple
  have hcm := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨x₀, hx⟩ := GlobalTheory.SkewToHerm.exists_sigma_ne σ hcm
  have hc : x₀ - σ x₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hcc : σ (x₀ - σ x₀) = -(x₀ - σ x₀) := by rw [map_sub, hσ, neg_sub]
  choose z hz ez using GlobalTheory.ThKCentreTransp.exists_central hcm hσ hc he
  choose N c hN using fun v m => GlobalTheory.ThKCentreSmall.exists_monic hσ hKP hT hc hcc (z v m) (hz v m)
  refine ⟨N, c, fun Ψ hΨ v m x => ?_⟩
  have hs := GlobalTheory.ThAutSmall.Smooth.isSm_theta_small F E σ hσ B a a' G X om om' hKP hT _ hc hcc Ψ hΨ
  have h1 := fun k => ez v m k _ hs
  simp only [MulEquiv.symm_apply_apply] at h1
  simp only [h1]
  rw [hN v m Ψ hΨ, Finset.sum_apply]
  rfl
