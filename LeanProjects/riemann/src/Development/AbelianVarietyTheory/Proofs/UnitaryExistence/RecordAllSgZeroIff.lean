import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FlagSectionAction

noncomputable section

namespace GlobalTheory.RecBCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
  Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction

variable {D : D7} (T : Core D)

def cuEquiv {j : ℕ} (hj : InR D j) : T.Cu j ≃ Cusps T j where
  toFun cu := cu.1
  invFun cu := ⟨cu, hj⟩
  left_inv _ := rfl
  right_inv _ := rfl

def cuTo {j : ℕ} (cu : T.Cu j) : Cusps T j := cu.1

def fjIncl {j : ℕ} (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)) (w : WeightFamilies.Wt D j) :
    domSec T j (cuTo T cu) w →ₗ[T.Q.c.F] T.FJt j cu χ w :=
  Submodule.subtype _

variable {T} (h : LawsCore T)

def recCu {j : ℕ} (cu : (recB h).Cu j) : (record h).Cu j := cuTo T cu

end GlobalTheory.RecBCompare
