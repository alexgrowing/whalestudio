import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMkTauE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
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

namespace GlobalTheory.LevelSeries

theorem phase_zpow_eq (z : ℂ) (hz : z ≠ 0) (b : ℤ) (r : ℕ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * b + (r : ℤ)) =
      z ^ (b + (r : ℤ)) * ((starRingEnd ℂ z) ^ b)⁻¹ * (((‖z‖ : ℝ) : ℂ) ^ r)⁻¹ := by
  have hN : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hc : starRingEnd ℂ z ≠ 0 := (map_ne_zero _).2 hz
  have hsq : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have h2b : ((‖z‖ : ℝ) : ℂ) ^ (2 * b) = z ^ b * (starRingEnd ℂ z) ^ b := by
    rw [_root_.zpow_mul, show ((‖z‖ : ℝ) : ℂ) ^ (2 : ℤ) = ((‖z‖ : ℝ) : ℂ) ^ (2 : ℕ) from zpow_ofNat _ 2, hsq, mul_zpow]
  have hzn : z ^ (2 * b + (r : ℤ)) = z ^ b * z ^ (b + (r : ℤ)) := by
    rw [← zpow_add₀ hz]; congr 1; ring
  rw [div_zpow, zpow_add₀ hN, h2b, hzn, zpow_natCast]
  have h1 : z ^ b ≠ 0 := zpow_ne_zero _ hz
  have h2 : (starRingEnd ℂ z) ^ b ≠ 0 := zpow_ne_zero _ hc
  have h3 : ((‖z‖ : ℝ) : ℂ) ^ r ≠ 0 := pow_ne_zero _ hN
  field_simp

theorem prod_norm_inv_pow {ι : Type} [Fintype ι] (z : ι → ℂ) (r : ℕ) :
    ∏ i, (((‖z i‖ : ℝ) : ℂ) ^ r)⁻¹ = (((∏ i, ‖z i‖ ^ 2) ^ (-(r : ℝ) / 2) : ℝ) : ℂ) := by
  rw [← Real.finset_prod_rpow _ _ (fun i _ => by positivity)]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_natCast_mul (norm_nonneg _)]
  rw [show ((2 : ℕ) : ℝ) * (-(r : ℝ) / 2) = -(r : ℝ) by push_cast; ring, Real.rpow_neg (norm_nonneg _),
    Real.rpow_natCast]
  push_cast
  rfl

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem conjugate_tauE_ne_tauE (D : D7) (τ τ' : D.what₂.Tau) :
    NumberField.ComplexEmbedding.conjugate (tauE D τ) ≠ tauE D τ' := by
  intro h
  have e := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, Formalism.L2.Theta.tauE_sqrtMinusD,
    Formalism.L2.Theta.tauE_sqrtMinusD] at e
  have e2 := congrArg Complex.im e
  simp at e2
  have : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  linarith

theorem mk_tauE_bij (D : D7) : Function.Bijective (fun τ : D.what₂.Tau => InfinitePlace.mk (tauE D τ)) := by
  refine ⟨fun τ τ' h => ?_, fun w => GlobalTheory.CharInfPlace.exists_mk_tauE D w⟩
  rcases InfinitePlace.mk_eq_iff.1 h with e | e
  · exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  · exact absurd e (conjugate_tauE_ne_tauE D τ τ')

theorem mk_tauE_complex (D : D7) (τ : D.what₂.Tau) : ¬ (InfinitePlace.mk (tauE D τ)).IsReal := by
  rw [InfinitePlace.isReal_mk_iff, NumberField.ComplexEmbedding.isReal_iff]
  exact conjugate_tauE_ne_tauE D τ τ

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem inf_eq_mul_normPow : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (χ : Formalism.L2.Host.HChar D.host.E), ChrEq χW χ → ∀ (k : Type) [Field k] (σ : k →+* ℂ), ConjIn D σ → ∀ a : D.host.Eˣ, ∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : D.host.E) : ℚ) : ℝ)| ^ (-(W.rank : ℝ) / 2) : ℝ) : ℂ) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hvp χ hc k _ σ hσ a
  choose b hb using hvp.1.expW
  obtain ⟨n, hn, hinf⟩ := GlobalTheory.HeckeInfExp.hasInfQ_of_hasInfExp D χW χ _ hc hb
  have hn' : ∀ τ, n τ = 2 * b τ + (W.rank : ℤ) := fun τ => by
    have : (n τ : ℚ) = ((2 * b τ + (W.rank : ℤ) : ℤ) : ℚ) := by rw [hn]; push_cast; ring
    exact_mod_cast this
  have hnorm : ∏ τ, ‖tauE D τ (a : D.host.E)‖ ^ 2 = |((Algebra.norm ℚ (a : D.host.E) : ℚ) : ℝ)| := by
    rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm]
    refine (Fintype.prod_bijective _ (mk_tauE_bij D) _ _ (fun τ => ?_))
    rw [NumberField.InfinitePlace.mult, if_neg (mk_tauE_complex D τ)]
    rfl
  have hA : ∏ τ, (tauE D τ (a : D.host.E) ^ ((b τ : ℤ) + (W.rank : ℤ)) *
      ((starRingEnd ℂ (tauE D τ (a : D.host.E))) ^ (b τ : ℤ))⁻¹) ∈ σ.fieldRange := by
    refine prod_mem fun τ _ => mul_mem (zpow_mem ?_ _) (inv_mem (zpow_mem ?_ _))
    · obtain ⟨y, hy⟩ := hσ (tauE D τ) a
      exact ⟨y, hy⟩
    · obtain ⟨y, hy⟩ := hσ ((starRingEnd ℂ).comp (tauE D τ)) a
      exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hA
  refine ⟨y, ?_⟩
  rw [hinf a, hy, ← hnorm, ← prod_norm_inv_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hn' τ]
  exact phase_zpow_eq _ ((map_ne_zero _).2 a.ne_zero) _ W.rank

end GlobalTheory.LevelSeries
