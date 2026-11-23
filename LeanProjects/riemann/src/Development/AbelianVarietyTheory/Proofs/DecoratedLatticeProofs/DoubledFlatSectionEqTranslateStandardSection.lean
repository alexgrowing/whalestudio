import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem flat_swSec_eq_sect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A) (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f → ∀ Φ : schwartzA θ B.rank A.rank, Φ.1 = sch ψ A B ν 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f) → s0 B A.rank = sZero A B ∧ (∀ (z : ℂ) (g : GA D (dblSp A)), flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z g = npow (absA D (aP A p)) (sZero A B - z) * sect omS (hgtStd A a κ p) Φ z (κ (g * p))) ∧ ∀ g : GA D (dblSp A), (omS (κ (g * p)) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f) := by
  intro D ψ A B χB omh hW ν 𝓨 _ θ _ μ _ κ _ omS hT lam _ a p f hf Φ hΦ
  have h0 : s0 B A.rank = sZero A B := by unfold s0 sZero; ring
  have h3 : ∀ g : GA D (dblSp A), (omS (κ (g * p)) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f) := fun g => by
    rw [hT (g * p) _ (hW.om_pres _ f hf) Φ hΦ, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one,
      mul_inv_cancel_right]
  refine ⟨h0, fun z g => ?_, h3⟩
  have hp : 0 < absA D (aP A p) := hom_pos _ _
  have h1 : npow (absA D (aP A p)) (sZero A B - z) * npow (absA D (aP A p)) (z - sZero A B) = 1 := by
    rw [← npow_add hp, show sZero A B - z + (z - sZero A B) = 0 by ring, npow_zero]
  have h2 : hgtStd A a κ p (κ (g * p)) = hgt A a g * absA D (aP A p) := by
    rw [hgtStd, MulEquiv.symm_apply_apply, mul_inv_cancel_right]
  have h4 : sch ψ A B ν 𝓨 (omh (g, 1) f) 0 = swSec A B omh ν 𝓨 f g := mixS_dblDec_zero A B ψ ν 𝓨 _ 0
  have h5 : flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z g =
      swSec A B omh ν 𝓨 f g * npow (hgt A a g) (z - sZero A B) := rfl
  rw [h5, sect, h3, h4, h2, h0, npow_mul]
  linear_combination (-(swSec A B omh ν 𝓨 f g * npow (hgt A a g) (z - sZero A B))) * h1

end GlobalTheory.StdUnn
