import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFunctionTwistBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_function_twist_bounded : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ f : UA σ G.W.J → ℂ, (∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧ IsAut σ (c • G.W.J.map σ) K (fun x => f ((toGAd hσ G.W.J hc).symm x))) → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun a : idelesInf F E => fun a' : idelesInf F E => ctLevi σ G.W W₁ H' μ 𝓕 f h ((a' : (AE F E)ˣ) * a))) := by
  first | exact @GlobalTheory.TorFin.ctLevi_arch_finite | exact GlobalTheory.TorFin.ctLevi_arch_finite | (intros; apply GlobalTheory.TorFin.ctLevi_arch_finite <;> assumption)
