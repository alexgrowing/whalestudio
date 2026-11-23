import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

noncomputable section

namespace GlobalTheory.FlatEisHol

open scoped NNReal

theorem analyticOnNhd_cosetSum_npow {G : Type} [Group G] (P Γ : Subgroup G) (Φ : G → ℂ) (h : G → ℝ≥0)
    (hpos : ∀ x, 0 < h x) (s₀ : ℂ) (σ₀ : ℝ)
    (hc : ∀ s : ℂ, σ₀ < s.re → ∀ g, GlobalTheory.Eis.CosetConv P Γ (fun x => Φ x * GlobalTheory.Doubling.npow (h x) (s - s₀)) g)
    (g : G) :
    AnalyticOnNhd ℂ (fun s => GlobalTheory.Eis.cosetSum P Γ (fun x => Φ x * GlobalTheory.Doubling.npow (h x) (s - s₀)) g)
      {s : ℂ | σ₀ < s.re} :=
  GlobalTheory.Eis.analyticOnNhd_tsum_npow (f := fun q => Φ (((Quot.out q : Γ) : G) * g))
    (a := fun q => h (((Quot.out q : Γ) : G) * g)) (fun _ => hpos _) (fun s hs => hc s hs g)

end GlobalTheory.FlatEisHol

theorem GlobalTheory.FlatEisHol.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (W₂ : Spc F E (n + n)) (K₂ : Subgroup (UA σ W₂.J)) (φ₀ : UA σ W₂.J → ℂ) (s₂ : ℂ) (σ₀ : ℝ),
    (∀ s : ℂ, σ₀ < s.re → ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K₂ φ₀ s₂ s) g) →
    ∀ g, AnalyticOnNhd ℂ (fun s => GlobalTheory.Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K₂ φ₀ s₂ s) g) {s : ℂ | σ₀ < s.re} := by
  intro F E _ _ _ _ _ σ n W₂ K₂ φ₀ s₂ σ₀ hc g
  exact GlobalTheory.FlatEisHol.analyticOnNhd_cosetSum_npow _ _ φ₀ _ (fun x => GlobalTheory.Doubling.hgtOf_pos x) s₂ σ₀ hc g
