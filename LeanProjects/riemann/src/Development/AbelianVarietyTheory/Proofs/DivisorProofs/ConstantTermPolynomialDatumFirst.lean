import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaGoodPlaceLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentIntegralAdaptedPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneLocalVectorInvarianceStatement

noncomputable section

namespace GlobalTheory.CtTypLoc

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem locV : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ Φ ∈ PolData B G.M, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ g : UA σ G.W.J, ∃ p q : ℂ, ∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M.I om Φ) (m * g) = p * ((GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) + q * ((GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH Φ hΦ μ 𝓕 hμ h𝓕 h1 v hv w hw g
  obtain ⟨n, ψ, ℓ, hψ, hA, hJ, hm⟩ :=
    GlobalTheory.T.unipotent_integral_adapted_plane hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH Φ hΦ μ 𝓕 hμ h𝓕 h1 v g
  choose p q hpq using fun j =>
    GlobalTheory.T.adapted_plane_local_vector_invariance hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH v hv w hw (ψ j) (hψ j) (ℓ j) (hA j) (hJ j)
  refine ⟨∑ j, p j, ∑ j, q j, fun x m hml => ?_⟩
  have hmU := GlobalTheory.T.local_theta_good_place_lattice F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH v w hw x m hml
  obtain ⟨ψ₁, hψ₁, he⟩ := hm m hmU
  rw [he, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => hpq j x m hml hmU (ψ₁ j) (hψ₁ j).1 (hψ₁ j).2

end GlobalTheory.CtTypLoc
