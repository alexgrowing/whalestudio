import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianSchemeCharts.FinSys
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianSchemeCharts.IsOpenImmersionProdChart

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.AXO

variable {R : Type} [CommRing R]

theorem sep_tensor (A : Over (Sp R)) [IsSeparated A.hom] : IsSeparated (A ⊗ A).hom := by
  rw [Over.tensorObj_hom, Limits.pullback.condition]
  infer_instance

def Sq (P : Type) : Type := P × P

instance (P : Type) [SemilatticeInf P] : SemilatticeInf (Sq P) := inferInstanceAs (SemilatticeInf (P × P))

instance (P : Type) [Finite P] : Finite (Sq P) := inferInstanceAs (Finite (P × P))

def prodSys (A : Over (Sp R)) {P : Type} [SemilatticeInf P] (S : Sys A.left P) : Sys (A ⊗ A).left (Sq P) where
  u ab := MainStatements.Hodge.Sh.prodAff A A (S.u (Prod.fst ab)) (S.u (Prod.snd ab))
  map_inf ab cd := by
    change MainStatements.Hodge.Sh.prodW A A (S.u (ab.1 ⊓ cd.1)).1 (S.u (ab.2 ⊓ cd.2)).1 =
      MainStatements.Hodge.Sh.prodW A A (S.u ab.1).1 (S.u ab.2).1 ⊓ MainStatements.Hodge.Sh.prodW A A (S.u cd.1).1 (S.u cd.2).1
    simp only [MainStatements.Hodge.Sh.prodW, S.map_inf, Scheme.Hom.preimage_inf]
    ac_rfl
  cover := by
    change ⨆ ab : P × P, MainStatements.Hodge.Sh.prodW A A (S.u ab.1).1 (S.u ab.2).1 = ⊤
    simp only [MainStatements.Hodge.Sh.prodW]
    rw [← iSup_inf_iSup (f := fun a ↦ (fst A A).left ⁻¹ᵁ (S.u a).1) (g := fun b ↦ (snd A A).left ⁻¹ᵁ (S.u b).1)]
    rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, S.cover]
    simp

end MainStatements.Hodge.Pf.AXO
