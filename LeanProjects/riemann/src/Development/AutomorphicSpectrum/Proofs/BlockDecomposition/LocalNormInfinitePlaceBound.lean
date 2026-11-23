import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH

theorem absEw_mul_locInf_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (J : Type) [Fintype J] (w : InfinitePlace F) (e : EmbOver E w)
    (u : J → E) (δ : (w.Completion ⊗[F] E)ˣ) (z : J → w.Completion ⊗[F] E) (c : ℝ≥0)
    (hz : ∀ f, z f = ((1 : w.Completion) ⊗ₜ[F] u f) * δ.1) (hc : ∀ f, ‖infEmb e (z f)‖₊ ≤ c) :
    GlobalTheory.Doubling.absEw F E w δ * locInf w u ≤ c ^ 2 := by
  classical
  have hnorm : ∀ (τ : EmbOver E w) (y : w.Completion ⊗[F] E), ‖infEmb τ y‖₊ = ‖infEmb e y‖₊ := by
    intro τ y
    rcases infEmb_eq_or_conj hσ e τ with h | h
    · rw [h]
    · rw [h, RingHom.comp_apply, RCLike.nnnorm_conj]
  have hterm : ∀ p : EmbOver E w × J, ‖infEmb e δ.1‖₊ * ‖p.1.1 (u p.2)‖₊ ≤ c := by
    rintro ⟨τ, f⟩
    have h1 : infEmb τ (z f) = τ.1 (u f) * infEmb τ δ.1 := by
      rw [hz f, map_mul, infEmb_tmul, map_one, one_mul]
    calc ‖infEmb e δ.1‖₊ * ‖τ.1 (u f)‖₊ = ‖infEmb τ δ.1‖₊ * ‖τ.1 (u f)‖₊ := by rw [hnorm τ]
      _ = ‖infEmb τ (z f)‖₊ := by rw [h1, nnnorm_mul, mul_comm]
      _ = ‖infEmb e (z f)‖₊ := hnorm τ _
      _ ≤ c := hc f
  have hsup : ‖infEmb e δ.1‖₊ * (Finset.univ.sup fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊) ≤ c := by
    rw [Finset.mul_sup₀]
    exact Finset.sup_le fun p _ => hterm p
  unfold locInf
  rw [GlobalTheory.Doubling.absEw_eq_sq hσ e, ← mul_pow]
  convert pow_le_pow_left' hsup 2
end GlobalTheory.CompanionTheory.GodementH

end
