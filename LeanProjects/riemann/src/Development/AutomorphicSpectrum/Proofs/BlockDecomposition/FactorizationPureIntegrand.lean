import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.PT

section Mat
variable {R : Type*} [CommRing R]

theorem diagonal_mul_diagonal_alt (a b c d : Rˣ) : (dg2 a b : GL (Fin 2) R) * dg2 c d = dg2 (a * c) (b * d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
end Mat

theorem realPart_mul (x y : G2) : GroundTheory.Automorphic.GL2Classical.realPart (x * y) =
    GroundTheory.Automorphic.GL2Classical.realPart x * GroundTheory.Automorphic.GL2Classical.realPart y := by
  have h : (AdelicGLn.prodEquiv ℚ 2 (x * y)).1 =
      (AdelicGLn.prodEquiv ℚ 2 x).1 * (AdelicGLn.prodEquiv ℚ 2 y).1 := by
    rw [map_mul]; rfl
  change Matrix.GeneralLinearGroup.map RationalIdeles.realEquiv.toRingHom _ =
    Matrix.GeneralLinearGroup.map RationalIdeles.realEquiv.toRingHom _ *
    Matrix.GeneralLinearGroup.map RationalIdeles.realEquiv.toRingHom _
  rw [h, map_mul]

theorem eR_eq (x : InfiniteAdeleRing ℚ) : GP.eR (x GP.wR) = RationalIdeles.realEquiv x := by
  let φ : ℝ →+* ℝ := (GP.eR.toRingHom.comp (Pi.evalRingHom _ GP.wR)).comp
    RationalIdeles.realEquiv.symm.toRingHom
  have hφ : φ = RingHom.id ℝ := Subsingleton.elim _ _
  have h : φ (RationalIdeles.realEquiv x) = RationalIdeles.realEquiv x := by rw [hφ]; rfl
  have h2 : φ (RationalIdeles.realEquiv x) = GP.eR (x GP.wR) := by
    change GP.eR ((RationalIdeles.realEquiv.symm (RationalIdeles.realEquiv x)) GP.wR) = _
    rw [RingEquiv.symm_apply_apply]
  exact h2.symm.trans h

section Int
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

end Int

end GlobalTheory.CompanionTheory.GL2Factorization.PT
