import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimKStableContinuousInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_K_stable_continuous_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s → Even d → ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ T : Submodule ℂ (UA σ W.J → ℂ), FiniteDimensional ℂ T → (∀ t ∈ T, Continuous t) → (∀ k, ∀ t ∈ T, rt (Subgroup.closure (KInf σ W B.emb)) k t ∈ T) → ∀ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) → ∀ A : Set (UA σ W.J → ℂ), A ⊆ typeSet (rt (Subgroup.closure (KInf σ W B.emb))) ⊤ T → (∀ φ ∈ A, IsSmoothModerate σ (c • W.J.map σ) (fun x => φ ((toGAd hσ W.J hc).symm x))) → (∀ φ ∈ A, ∀ k ∈ U, k ∈ finU σ W.J → ∀ x, φ (x * k) = φ x) → (∀ z, IsCentral σ (c • W.J.map σ) z → ∃ (N : ℕ) (b : Fin N → ℂ), ∀ φ ∈ A, (dop z)^[N] (fun x => φ ((toGAd hσ W.J hc).symm x)) = ∑ i : Fin N, b i • (dop z)^[i.val] (fun x => φ ((toGAd hσ W.J hc).symm x))) → FiniteDimensional ℂ (Submodule.span ℂ A) := by
  first | exact @GlobalTheory.HCFinU.automorphicForms_finite_skew | exact GlobalTheory.HCFinU.automorphicForms_finite_skew | (intros; apply GlobalTheory.HCFinU.automorphicForms_finite_skew <;> assumption)
