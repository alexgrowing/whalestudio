import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.SmoothLev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def SmModUA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : UA σ J → ℂ) : Prop :=
  ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • J.map σ) → ∀ φ' : GAd σ (c₀ • J.map σ) → ℂ,
    (∀ (g : UA σ J) (g' : GAd σ (c₀ • J.map σ)), g.1 = g'.1 → φ' g' = f g) →
    GlobalTheory.SiegelSet.IsSmoothModerate σ (c₀ • J.map σ) φ'

theorem exists_val_eq (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : IsCMExt F E σ) {c₀ : E}
    (hc₀ : c₀ ≠ 0) (g' : GAd σ (c₀ • J.map σ)) : ∃ g : UA σ J, g.1 = g'.1 := by
  have := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) (GlobalTheory.SiegelSet.sigma_sigma hσ) hc₀
  obtain ⟨x, hx⟩ := g'
  exact ⟨⟨x, (SetLike.ext_iff.1 this x).2 hx⟩, rfl⟩

end GlobalTheory.ThK.SmoothLev
