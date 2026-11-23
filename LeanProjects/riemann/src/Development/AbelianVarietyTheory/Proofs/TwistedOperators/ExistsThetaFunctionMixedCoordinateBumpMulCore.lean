import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionSumMulMiddleCoordinate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumOverRationalHomThetaLawZeroCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPoincareSumOverRationalHomBumpStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumHalfWittHeisenbergLevelOfZeroCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffPoincareSumOverRationalHomRealDirectionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedCoordinatePoincareSumHalfWittEqBumpStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BumpMix

theorem coreA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (H Z T : HSp D) (ρ : ℕ) (dH : HypDec H Z ρ), Z.rank = 0 → ∀ (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∃ f, IsThetaFunO ψ H T f ∧ ∀ x, dH.mixS T ψ v.μ v.𝓕 f x 0 = β x := by
  intro D ψ hψ H Z T ρ dH hZ v β hβ
  exact ⟨poinX ψ dH T β, ⟨GlobalTheory.T.poincareSumOverRationalHom_thetaLaw_zeroCore D ψ hψ H Z T ρ dH hZ β, GlobalTheory.T.poincareSumHalfWitt_heisenberg_level_of_zero_core D ψ hψ H Z T ρ dH hZ β hβ,
    GlobalTheory.T.continuous_poincareSumOverRationalHom_bump D ψ hψ H Z T ρ dH β hβ, GlobalTheory.T.contDiff_poincareSumOverRationalHom_realDirections D ψ hψ H Z T ρ dH β hβ⟩, GlobalTheory.T.mixedCoordinate_poincareSum_halfWitt_eq_bump D ψ hψ H Z T ρ dH v β hβ⟩

theorem bump_mul_theta_mixS : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ) (g : WO S₀ T → ℂ), IsBump β → IsThetaFunO ψ S₀ T g → ∃ Φ, IsThetaFunO ψ S T Φ ∧ ∀ x, d.mixS T ψ v.μ v.𝓕 Φ x = β x • g := by
  intro D ψ hψ S S₀ T ρ d v β g hβ hg
  let P : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral ρ
  let dH : HypDec (GlobalTheory.Doubling.dblSp P) (GlobalTheory.Core.Rk.SWLaw.zeroSp D) ρ := GlobalTheory.Core.Rk.SWLaw.dblDec P
  have hZ : (GlobalTheory.Core.Rk.SWLaw.zeroSp D).rank = 0 := rfl
  obtain ⟨fH, hfH, hmix⟩ := coreA D ψ hψ _ _ T ρ dH hZ v β hβ
  refine ⟨_, isThetaFunO_prod 1 d.i₀ 1 (GlobalTheory.TowerSurj.embMat d dH) (GlobalTheory.TowerSurj.symplOH_split d dH T hZ) hg hfH,
    fun x => ?_⟩
  funext w₀
  have hz : ∀ z : WO (GlobalTheory.Core.Rk.SWLaw.zeroSp D) T, z = 0 := fun z => Matrix.ext fun _ j => by
    haveI : IsEmpty (Fin (GlobalTheory.Core.Rk.SWLaw.zeroSp D).rank) := by rw [hZ]; infer_instance
    exact isEmptyElim j
  have e2 : ∀ a : Mx D T.rank ρ, sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) =
      dH.extY T a + dH.extX T x + dH.ext0 T 0 := by
    intro a
    have hX : sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.jX = x := by
      rw [sandwich_apply, rat_one, Matrix.one_mul, GlobalTheory.TowerSurj.mul_embMat_jX, coord_jX]
    have hY : sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.jY = a := by
      rw [sandwich_apply, rat_one, Matrix.one_mul, GlobalTheory.TowerSurj.mul_embMat_jY, coord_jY]
    have h0 := hz (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.j0)
    rw [eq_coords dH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀)), hX, hY, h0]
    abel
  have e1 : ∀ a : Mx D T.rank ρ, sandwich (rat 1) (rat d.i₀) (d.extY T a + d.extX T x + d.ext0 T w₀) = w₀ := by
    intro a
    rw [sandwich_apply, rat_one, Matrix.one_mul]
    exact witt_extension_sum_mul_middle_coordinate d x a w₀
  have key : ∀ a : Mx D T.rank ρ,
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀)
        (fun w => g (sandwich (rat 1) (rat d.i₀) w) * fH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) w)))) 0 =
      g w₀ * heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 := by
    intro a
    rw [d.integrandS_eq, dH.integrandS_eq, symplOH_Y_X, symplOH_Y_X]
    show _ * (g _ * fH _) = _
    rw [e1, e2]
    ring
  have h2 : ∫ a in v.𝓕, heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 ∂v.μ =
      β x := hmix x
  show ∫ a in v.𝓕, _ ∂v.μ = β x * g w₀
  rw [show (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀)
        (fun w => g (sandwich (rat 1) (rat d.i₀) w) * fH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) w)))) 0) =
      fun a => g w₀ * heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 from funext key,
    integral_const_mul, h2, mul_comm]

end GlobalTheory.BumpMix

end
