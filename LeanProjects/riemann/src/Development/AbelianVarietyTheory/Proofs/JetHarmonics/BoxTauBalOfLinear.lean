import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxTauLin

theorem isMonHom_of_coord {S : Scheme.{0}} {A' A : Over S} [GrpObj A'] [GrpObj A] {n : ℕ} (p : IsPowGrp A' A n)
    (f : A ⟶ A) [IsMonHom f] (f' : A' ⟶ A') (h : ∀ i, f' ≫ p.pr i = p.pr i ≫ f) : IsMonHom f' := by
  have e : f' = powMap p f := pow_ext p fun i => by rw [h, powMap_pr]
  rw [e]
  exact powMap_isMonHom p f

theorem boxTauBal_of_linear : GlobalFnsSt →
    ∀ (R : Type) [CommRing R] [IsDomain R] (D' D : DegPre R) (n : ℕ) (pD : IsPowDeg D' D n)
    (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A) (a a' : D.X → D.X), IsMonHom f → IsMonHom g →
    (∀ i, f' ≫ pD.pw.pr i = pD.pw.pr i ≫ f) → (∀ i, g' ≫ pD.pw.pr i = pD.pw.pr i ≫ g) →
    RosatiAdj D.P.A D.P.L f g → (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (a' y) = D.c y ≫ g) →
    D.TauBal f g a a' →
    D'.TauBal f' g' (fun y => pD.xe.symm fun i => a (pD.xe y i))
      (fun y => pD.xe.symm fun i => a' (pD.xe y i)) := by
  intro hG R _ _ D' D n pD f g f' g' a a' hf hg ef eg hr ca ca' hT
  exact GlobalTheory.TauBalBox.tauBal_pow hG R n D D' pD f g f' g' hf hg (isMonHom_of_coord pD.pw f f' ef)
    (isMonHom_of_coord pD.pw g g' eg) ef eg hr a a' _ _
    (fun x i => by rw [AddEquiv.apply_symm_apply]) (fun x i => by rw [AddEquiv.apply_symm_apply]) ca ca' hT

end GlobalTheory.BoxTauLin
