import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS

theorem rowAct_mul_left {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (v g : GL (Fin 2) F) (w : F × F) :
    rowAct (v * g) w = rowAct g (rowAct v w) := by
  ext <;> simp only [rowAct, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem inn_unipotent_left {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (χ : AddChar F Circle) (Ψ : F × F → ℂ) (v g : GL (Fin 2) F)
    (hv : v ∈ Iwasawa.unipotent F 2) (u : Fˣ) :
    inn χ (Ψ ∘ rowAct (v * g)) u = (χ (v.val 0 1) : ℂ) * inn χ (Ψ ∘ rowAct g) u := by
  have h00 : v.val 0 0 = 1 := hv.2 0
  have h11 : v.val 1 1 = 1 := hv.2 1
  have h10 : v.val 1 0 = 0 := hv.1 (by decide : (0 : Fin 2) < 1)
  set x := v.val 0 1 with hx
  set h : F → ℂ := fun y => (Ψ ∘ rowAct g) ((u : F), (u : F) * y) * (χ (-y) : ℂ) with hh
  have key : ∀ y : F, (Ψ ∘ rowAct (v * g)) ((u : F), (u : F) * y) * (χ (-y) : ℂ) =
      (χ x : ℂ) * h (y + x) := by
    intro y
    have hrow : rowAct v ((u : F), (u : F) * y) = ((u : F), (u : F) * (y + x)) := by
      ext
      · simp only [rowAct, h00, h10]; ring
      · simp only [rowAct, h11, ← hx]; ring
    have hchi : (χ (-y) : ℂ) = (χ x : ℂ) * (χ (-(y + x)) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    simp only [hh, Function.comp_apply, rowAct_mul_left, hrow, hchi]
    ring
  have htr : ∫ y, h (y + x) ∂selfDualMeasure χ = ∫ y, h y ∂selfDualMeasure χ :=
    integral_add_right_eq_self h x
  calc inn χ (Ψ ∘ rowAct (v * g)) u
      = ∫ y, (χ x : ℂ) * h (y + x) ∂selfDualMeasure χ := by
        unfold inn
        exact integral_congr_ae (Eventually.of_forall key)
    _ = (χ x : ℂ) * inn χ (Ψ ∘ rowAct g) u := by
        rw [integral_const_mul, htr]
        rfl

theorem WL_unipotent_left : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (v g : GL (Fin 2) F), v ∈ Iwasawa.unipotent F 2 → GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ (v * g) = Whittaker.psiN (Circle.coeHom.compAddChar χ) v * GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ g := by
  intro F _ _ _ _ _ _ χ c₁ c₂ Ψ v g hv
  have h00 : v.val 0 0 = 1 := hv.2 0
  have h11 : v.val 1 1 = 1 := hv.2 1
  have h10 : v.val 1 0 = 0 := hv.1 (by decide : (0 : Fin 2) < 1)
  have hdetv : Matrix.GeneralLinearGroup.det v = 1 := by
    apply Units.ext
    simp [Matrix.det_fin_two, h00, h11, h10]
  have hdet : Matrix.GeneralLinearGroup.det (v * g) = Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, hdetv, one_mul]
  have hpsi : Whittaker.psiN (Circle.coeHom.compAddChar χ) v = (χ (v.val 0 1) : ℂ) := by
    have hs : Whittaker.superdiagSum (v : Matrix (Fin 2) (Fin 2) F) = v.val 0 1 := by
      simp [Whittaker.superdiagSum, Fin.sum_univ_two]
    rw [Whittaker.psiN, hs]
    rfl
  have hlin : lin χ c₁ c₂ (Ψ ∘ rowAct (v * g)) =
      (χ (v.val 0 1) : ℂ) * lin χ c₁ c₂ (Ψ ∘ rowAct g) := by
    unfold lin
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [den, inn_unipotent_left χ Ψ v g hv u]
    ring
  rw [WL, WL, hdet, hlin, hpsi]
  ring

end GlobalTheory.CompanionTheory.WS
