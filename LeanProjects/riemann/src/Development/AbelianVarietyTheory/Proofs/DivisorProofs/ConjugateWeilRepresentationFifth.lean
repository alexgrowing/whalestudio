import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFockVacuumProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientConjugateThetaForm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.IoExtConj

open GlobalTheory.AdTh.IoExtPf
open scoped Classical

theorem deltaConj_ne {D : D7} (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : deltaConj (D := D) i σ ≠ 0 := by
  refine delta_ne _ _ _ _ (fun τ => ?_) ((rank_Wc i).le.trans (r_le_V i))
  show ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 ≤ _
  rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2, rank_Wc]
  have := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem exists_unit_of_isIoW {D : D7} {V W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S) (hs : LowSm M)
    (hl : ExtLine M) (c : CoefA V) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)) (Δ : PolF D W.rank V.rank) (hΔ : pt Δ ≠ 0)
    (hwt : ∀ (τ : D.what₂.Tau) (a : Fin W.rank → ℝ), ω (1, atTau θ W τ ((M.fr τ)⁻¹ *
      Matrix.diagonal (fun j => Complex.exp ((a j : ℂ) * Complex.I)) * M.fr τ)) (pt Δ) =
        Complex.exp (((∑ j, extWt M τ j * a j : ℝ) : ℂ) * Complex.I) • pt Δ)
    (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank) (h : IsIoW θ M c ω pt Δ io)
    (v' : ∀ ρ, lowT M ρ) (hv' : IsExtVec M (fun ρ => v' ρ)) :
    ∃ w : c.W, ‖w‖ = 1 ∧ io (PiTensorProduct.tprod ℂ v') w = Δ := by
  obtain ⟨-, hK, v, w, hv1, hw1, hio⟩ := h
  let f : LowT M →ₗ[ℂ] (WO V W → ℂ) := pt ∘ₗ io.flip w
  have hf : ∀ x, f x = pt (io x w) := fun x => rfl
  have hv0 : f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [hf, hio]
    exact hΔ
  have hv : IsExtVec M (fun ρ => v ρ) := by
    refine fun τ => ⟨hv1 τ, (v τ).2, fun a ha => ?_⟩
    have hm := GlobalTheory.LowKProj.lowKSub_stable _ _ _ _ ha _ (v τ).2
    let u : lowT M τ := ⟨⟨_, hs τ hm⟩, hm⟩
    have h1 := hK τ _ ha v u rfl w
    rw [hio, hwt τ a, ← hio, ← hf, ← hf] at h1
    have h2 := inj_factor M hs hl τ f (fun k => ω (1, atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)))
      (fun k hk v u hu => hK τ k hk v u hu w) v hv0
      (u - Complex.exp (((∑ j, extWt M τ j * a j : ℝ) : ℂ) * Complex.I) • v τ) (by
        rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, Function.update_eq_self, map_sub, map_smul, ← h1,
          sub_self])
    exact congrArg (fun y : lowT M τ => ((y : M.sm τ) : M.H τ)) (sub_eq_zero.1 h2)
  choose a ha1 ha using hl _ _ hv hv'
  have e : v' = fun ρ => a ρ • v ρ := funext fun ρ => Subtype.ext (ha ρ)
  have hn : ‖∏ ρ, a ρ‖ = 1 := by simp [norm_prod, ha1]
  have h0 : ∏ ρ, a ρ ≠ 0 := fun h => by simp [h] at hn
  refine ⟨(∏ ρ, a ρ)⁻¹ • w, by rw [norm_smul, norm_inv, hn, hw1]; simp, ?_⟩
  rw [e, MultilinearMap.map_smul_univ, map_smul, map_smul, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ h0, one_smul, hio]

end GlobalTheory.GalOne.IoExtConj
