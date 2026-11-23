import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
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

namespace GlobalTheory.RealVacPow

open scoped ComplexOrder

theorem vacuum_det_power : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (p : ℕ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) p) →
    ∃ k : D.what₂.Tau → ℤ, ∀ a ∈ GinfC V, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f →
      (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f) →
      om (a, 1) f = (∏ τ, (Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)).det ^ k τ) • f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP p BW hB
  have hP1 := hP.1
  obtain ⟨η, hη⟩ := hP1.eta
  choose b hb using hP1.expW
  have hsW : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ) := hP.2.2.2.2.2.2.2.1
  choose q hq1 hq using fun τ => GlobalTheory.OneMapRef.RealMove.detPlus_one (n := V.rank) (sW τ) (hsW τ).1
  refine ⟨fun τ => -(b τ) - (q τ : ℤ), fun a ha f hf hv => ?_⟩
  have hθ : IsInfFam θ := hP1.inf
  have hψ := hP1.weil.std
  have hgV : ∀ τ, gramAt D V τ = 1 := fun τ => by
    unfold gramAt; rw [hP1.std]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hS : ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun τ => by
    rw [hgV]; exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hdetV : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => by rw [hgV]; simp
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ V hdetV a ha
  have mt1 : Formalism.L2.Theta.mt W 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have hy : IsDetRoot W 1 1 := by
    unfold IsDetRoot
    have : ((matHom W 1).1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) = 1 := mt1
    rw [this, Matrix.det_one, one_mul, Units.val_one, map_one]
  have one : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := fun τ => by
    rw [mt1]; exact Matrix.map_one _ (by simp) (by simp)
  rw [GlobalTheory.WeilVacChar.vacuum_character D ψ hψ V W θ hθ χV χW om η hη hP1.weil (fun _ => 1) sW hS hsW a ha 1 (one_mem _)
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, Matrix.one_mul, Matrix.mul_one]) x 1 hx hy f hf hv]
  congr 1
  have hexp : ∀ τ, HasInfExp D (χW * (η ^ W.rank)⁻¹) τ ((b τ : ℤ) : ℚ) := fun τ => by
    have := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hb τ) (hη.2.2.2 τ) W.rank
    rwa [add_sub_cancel_right] at this
  have hνx := hxv _ b hexp
  have hinv : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)).det * (compAt θ τ (Formalism.L2.Theta.mt V a)).det = 1 := fun τ => by
    rw [GlobalTheory.OneMapRef.RealMove.det_compAt, GlobalTheory.OneMapRef.RealMove.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    have : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
      unfold Formalism.L2.Theta.mt; rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [this, Matrix.det_one, map_one, map_one]
  have hd0 : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V a)).det ≠ 0 := fun τ h => by
    have := hinv τ; rw [h, mul_zero] at this; exact zero_ne_one this
  have hdp : ∀ τ, GlobalTheory.WeilParts.detPlus 1 (sW τ) (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt W 1)) =
      ((compAt θ τ (Formalism.L2.Theta.mt V a)).det)⁻¹ ^ q τ := fun τ => by
    rw [one, (hq τ _ 1 (by rw [Matrix.one_mul, Matrix.mul_one])).1]
    have e : (1 / 2 : ℂ) • (1 + sW τ) * 1 + (1 / 2 : ℂ) • (1 - sW τ) = 1 := by rw [Matrix.mul_one]; module
    rw [e, Matrix.det_one, one_pow, one_mul, eq_inv_of_mul_eq_one_left (hinv τ)]
  rw [map_one, mul_one, Circle.coe_inv, hνx, Finset.prod_congr rfl fun τ _ => hdp τ, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [zpow_sub₀ (hd0 τ), _root_.zpow_neg, zpow_natCast, inv_pow, div_eq_mul_inv]

end GlobalTheory.RealVacPow

end
