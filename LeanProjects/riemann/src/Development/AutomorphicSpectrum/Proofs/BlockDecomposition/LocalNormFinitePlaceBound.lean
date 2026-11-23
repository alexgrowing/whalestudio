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

theorem absEv_mul_locFin_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Type) [Fintype J] (v : Pl F) (u : J → E) (δ : (Fv F v ⊗[F] E)ˣ) (z : J → Fv F v ⊗[F] E) (c : ℝ≥0),
    (∀ f, z f = ((1 : Fv F v) ⊗ₜ[F] u f) * δ.1) → (∀ f, absFin F v (z f) ≤ c) →
    GlobalTheory.Doubling.absEv F E v δ * locFin σ v u ≤ c ^ 2 := by
  intro F E _ _ _ _ _ σ hσ J _ v u δ z c hz hc
  have e2 : ∀ (τ : E →ₐ[F] FvBar F v) (w : Fv F v ⊗[F] E),
      finEmb F v τ (sigR (Fv F v) σ w) = finEmb F v (τ.comp σ) w := by
    intro τ w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hN := congrArg (fun y => absBar F v (finEmb F v (embBar F E v) y))
    (GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) δ.1)
  simp only [map_mul, absBar_mul, e2, AlgHom.commutes, absBar_algebraMap] at hN
  have key : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (finEmb F v τ δ.1) * supBar v τ u ≤ c := by
    intro τ
    unfold supBar
    rw [NNReal.mul_finset_sup]
    refine Finset.sup_le fun f _ => ?_
    refine le_trans (le_of_eq ?_) ((le_absFin F v τ (z f)).trans (hc f))
    rw [hz f, map_mul, absBar_mul, finEmb_tmul, map_one, one_mul, mul_comm]
  rw [GlobalTheory.Doubling.absEv_apply, hN]
  unfold locFin
  calc _ = (absBar F v (finEmb F v (embBar F E v) δ.1) * supBar v (embBar F E v) u) *
        (absBar F v (finEmb F v ((embBar F E v).comp σ) δ.1) * supBar v ((embBar F E v).comp σ) u) := by ring
    _ ≤ c * c := mul_le_mul' (key _) (key _)
    _ = c ^ 2 := (sq c).symm

end GlobalTheory.CompanionTheory.GodementH

end
