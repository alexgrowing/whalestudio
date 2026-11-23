import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def outer (W : G.Weil) (M : Vol G) {t : T} {i j : ℕ} (d : PureT G (routeSmall t i j)) (F : Fn G (.grid i (j + 1)))
    (g₁ : GA D (G.V (.grid (i + 1) j))) : Fn G (.grid i j) := fun u =>
  W.kerA (.right i j) d.2 u g₁ * ∫ g in M.fd (.grid i (j + 1)), W.kerA (.down t i j) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))

theorem liftT_routeSmall (W : G.Weil) (M : Vol G) {t : T} {i j : ℕ} (τ : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    liftT W M (routeSmall t i j) τ F g₁ = τ.sum fun d c => c * ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := by
  simp only [liftT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

end GlobalTheory.SmallRoute
end
