import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem map_infPart_of_nsmul {V W : HSp D} {y : WO V W} {M : ℕ} (hM : M ≠ 0) (h : (M • y).map (infPart D) = 0) :
    y.map (infPart D) = 0 := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul D.host.F] at h1
  exact (smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hM)

theorem map_infPart_of_mem_latO {V W : HSp D} {LV : Set (Fin V.rank → D.host.E)} {LW : Set (Fin W.rank → D.host.E)}
    {u : WO V W} (hu : u ∈ latO V W LV LW fun _ => True) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add, hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem trSp_theta_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (e : AE D) (M : ℕ) (O₁ : Subring ℂ), M ≠ 0 → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O₁,
      IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hv e M O₁ hM f hf
  have hvac : IsVacO ψ θ V W (fun _ => 1) sW (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f₀ :=
    hv.2.2.2.2.2.2.2.2
  let Sp : Submodule ℂ (WO V W → ℂ) :=
    Submodule.span ℂ (Set.range fun a : {a : WO V W // a.map (infPart D) = 0} => heisO ψ V W a f₀)
  have hle : trSp ψ V W ΛV ΛW f₀ e M O₁ ≤ Sp.restrictScalars O₁ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, -, hy, rfl⟩
    exact Submodule.subset_span ⟨⟨y, map_infPart_of_nsmul hM (map_infPart_of_mem_latO hy)⟩, rfl⟩
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hle hf)
  rw [← hc]
  exact ⟨GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ V W hvac.1.1 f₀ hvac.2.theta _ c.support (fun a => a.1) c
      fun a _ => a.2,
    fun τ => GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ V W hvac.1.1 hvac.2.inf f₀ hvac.2.theta τ _ (hvac.2.fock τ) _
      c.support (fun a => a.1) c fun a _ => a.2⟩

end GlobalTheory.LevelSeries
