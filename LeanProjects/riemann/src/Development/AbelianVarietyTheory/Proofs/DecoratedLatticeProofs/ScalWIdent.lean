import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def eV (a : Fin D.R.rS) : VA X.B.I := incl X.B.I (X.eR a)

def fV (a : Fin D.R.rS) : VA X.B.I := incl X.B.I (X.fR a)

def zV : VA X.B.I := incl X.B.I (X.zR u)

def prj (y : VA X.B.I) : VA X.B.I :=
  ∑ a, hA X.B.I (fV X a) y • eV X a + ∑ a, hA X.B.I (eV X a) y • fV X a
    - divN X.B.I (D.mem u).A.T (hA X.B.I (zV X u) y) • zV X u

def prjL : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I where
  toFun := prj X u
  map_add' y z := by
    simp only [prj, Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right, add_smul, Finset.sum_add_distrib, divN, mul_add]
    abel
  map_smul' c y := by
    simp only [prj, Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_right, mul_smul, smul_sub, smul_add, Finset.smul_sum, divN,
      RingHom.id_apply, mul_left_comm _ c]

def prjM : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := LinearMap.toMatrix' (prjL X u)

def hMat (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
  c • 1 + (1 - c) • prjM X u

def prj0 (y : VA X.B.I) : VA X.B.I :=
  ∑ a, hA X.B.I (X.f0 a) y • X.e0 a + ∑ a, hA X.B.I (X.e0 a) y • X.f0 a - hA X.B.I X.z0 y • X.z0

theorem prjM_mulVec (y : VA X.B.I) : prjM X u *ᵥ y = prj X u y := by
  rw [prjM, LinearMap.toMatrix'_mulVec]; rfl

theorem hMat_mulVec (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (y : VA X.B.I) :
    hMat X u c *ᵥ y = c • y + (1 - c) • prj X u y := by
  rw [hMat, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_mulVec, prjM_mulVec]

theorem scalW_ident {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (mb mc m6 tt dd : R) (S1 S2 S3 S4 z' w0 : V) :
    (mb * mc * m6 * tt) • (S1 + S2 - dd • z' - (S3 + S4 - w0)) = (mc * m6 * tt) • (mb • (S1 - S3)) + (mc * m6 * tt) • (mb • (S2 - S4))
      - (mb * m6) • (mc • ((tt * dd) • z' - w0)) - (mb * mc) • ((m6 * (1 - tt)) • w0) := by
  module

end GlobalTheory.ScalW
