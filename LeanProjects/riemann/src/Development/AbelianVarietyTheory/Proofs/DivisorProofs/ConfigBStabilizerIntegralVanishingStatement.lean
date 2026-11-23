import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralVanishing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_constant_term_four_summands_hasLawC : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ s₁ : ℝ, ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ s : ℂ, s₁ < s.re →
      GlobalTheory.ConeSmallCT.LocUnifSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) T → ∃ T₂ T₃ T₄ : UA σ G.W.J → ℂ,
        IsCT H' (fun h => ∑' t : T, GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) (t.1 * h)) (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) + T₂ + T₃ + T₄) ∧
        GlobalTheory.ConeSmallCT.HasLawC G₁.W H' X.β (-s + ((a + b + 1 : ℕ) : ℂ) / 2) T₂ ∧
        GlobalTheory.ConeSmallCT.HasLawC G₁.W H' X.α (((b + 2 : ℕ) : ℂ) / 2) T₃ ∧
        GlobalTheory.ConeSmallCT.HasLawC G₁.W H' X.β (((a + 2 : ℕ) : ℂ) / 2) T₄ := by
  first | exact @GlobalTheory.ConeSmallSer.ctSeries | exact GlobalTheory.ConeSmallSer.ctSeries | (intros; apply GlobalTheory.ConeSmallSer.ctSeries <;> assumption)
