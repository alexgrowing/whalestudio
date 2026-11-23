import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ClsCoreFromMix

theorem heisO_smul_loc {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext v
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem mixS_smul_loc {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (c : ℂ) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 (c • f) x = c • d.mixS T ψ μ 𝓕 f x := by
  funext w
  simp only [HypDec.mixS, heisO_smul_loc, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]

theorem isThetaFunO_smul_loc {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Φ : WO S T → ℂ}
    (hΦ : IsThetaFunO ψ S T Φ) (c : ℂ) : IsThetaFunO ψ S T (c • Φ) := by
  refine ⟨fun γ w => ?_, ?_, continuous_const.mul hΦ.cont, fun k L hL hf w => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hΦ.quasi γ w]; ring
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U, hU, fun u hu hu' => ?_⟩
    funext w
    have := congrFun (h u hu hu') w
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]; ring
  · exact contDiff_const.mul (hΦ.smooth k L hL hf w)

theorem isHalf_mul {D : D7} {m n k : ℕ} {e : AE D} {u : Mx D m n} (h : IsHalf e u) (M : Mx D n k) :
    IsHalf e (u * M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, h i]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (p : Pieces V₀ W W₀ ρ σ) (y : Mx D V₀.rank σ) (β₁ : Mx D W.rank ρ → ℂ) (g' : WO V₀ W → ℂ) (Φ : WO V W → ℂ), IsThetaFunO ψ V₀ W g' → IsThetaFunO ψ V W Φ → (∀ x', dV.mixS W ψ vS.μ vS.𝓕 Φ x' = β₁ x' • g') → (∀ ξ ∈ p.B₁, heisO ψ V₀ W (dW.incX V₀ ξ) g' = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • g') → (∀ η ∈ p.B₂, heisO ψ V₀ W (dW.incY V₀ η) g' = g') → IsLatVac (heisO ψ V₀ W) (p.Γ₀.map (dW.inc0 V₀)) g' → (∀ ξ ∈ p.B₁, heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) Φ = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • Φ) ∧ (∀ η ∈ p.B₂, heisO ψ V W (dV.ext0 W (dW.incY V₀ η)) Φ = Φ) ∧ IsLatVac (fun w f => heisO ψ V W w f) (p.Γ₀.map ((dV.ext0 W).comp (dW.inc0 V₀))) Φ := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS p y β₁ g' Φ hg hΦ hmix hB1 hB2 hvac
  have hH := GlobalTheory.HeisMixSource.heis_mixS D ψ hψ V V₀ W ρ dV vS Φ hΦ
  have key : ∀ (w : WO V₀ W) (c : ℂ), heisO ψ V₀ W w g' = c • g' →
      heisO ψ V W (dV.ext0 W w) Φ = c • Φ := by
    intro w c hw
    have hth1 := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hΦ (dV.ext0 W w)
    have hth2 : IsThetaFunO ψ V W (c • Φ) := isThetaFunO_smul_loc hΦ c
    refine (GlobalTheory.T.thetaFunction_determined_by_mixedCoordinates D ψ hψ V W _ _ hth1 hth2).1 V₀ ρ dV vS (fun x => ?_)
    rw [hH.2.2.1 x w, hmix x, heisO_smul_loc, hw, mixS_smul_loc, hmix x, smul_comm]
  refine ⟨fun ξ hξ => key _ _ (hB1 ξ hξ), fun η hη => by rw [key _ 1 (by rw [one_smul]; exact hB2 η hη), one_smul], ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
    have h2 : (2 • (((dV.ext0 W).comp (dW.inc0 V₀)) w)) = dV.ext0 W (2 • dW.inc0 V₀ w) := by
      simp only [AddMonoidHom.comp_apply, map_nsmul]
    show heisO ψ V W _ Φ = Φ
    rw [h2, key _ 1 (by rw [one_smul]; exact hvac.1 _ (AddSubgroup.mem_map_of_mem _ hw)), one_smul]
  · intro e he u hu hh
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
    have hh' : IsHalf e (dW.inc0 V₀ w) := by
      have := isHalf_mul hh dV.j0
      simpa only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one] using this
    show heisO ψ V W _ Φ = Φ
    rw [AddMonoidHom.comp_apply, key _ 1 (by rw [one_smul]; exact hvac.2 e he _ (AddSubgroup.mem_map_of_mem _ hw) hh'),
      one_smul]

end GlobalTheory.ClsCoreFromMix
