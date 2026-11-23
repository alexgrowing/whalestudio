import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassMulLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiadditiveClassEqPoincarePullbackUniqueHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassSymmNaturalAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareClassAdditiveInDualVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFree
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdjCancel

variable {K : Type} [Field K]

theorem evc_zpow {A A' : AbVar K} {P : LB (A.X ⊗ A'.X).left} (hP : AbDual.IsDual A.X A'.X P)
    {Y : Over (Sp K)} (a : Y ⟶ A.X) (b : Y ⟶ A'.X) (k : ℤ) :
    AbDual.evc hP.isLB a (b ^ k) = k • AbDual.evc hP.isLB a b ∧ AbDual.evc hP.isLB a 1 = 0 := by
  let F : (Y ⟶ A'.X) →* Multiplicative (Pic Y.left) :=
    MonoidHom.mk' (fun b => Multiplicative.ofAdd (AbDual.evc hP.isLB a b)) (fun b b' => by
      rw [GlobalTheory.T.poincareClass_additive_in_dual_variable K A A' P hP Y a b b']; rfl)
  refine ⟨?_, ?_⟩
  · have := map_zpow F b k
    exact this
  · have := map_one F
    exact this

end GlobalTheory.AdjCancel
