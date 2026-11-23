import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

def upSec {S : Scheme.{0}} (G : Over S) {L : LB G.left} {k : ℕ} (σ : H0 L k) :
    LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S))) :=
  GlobalTheory.VVRank.pullTo σ (snd (Over.mk (𝟙 S)) G).left (fun _ => Category.comp_id _)

theorem sval_upSec {S : Scheme.{0}} (G : Over S) {L : LB G.left} {k : ℕ} (σ : H0 L k) {Z : Scheme.{0}}
    (r : Z ⟶ (Over.mk (𝟙 S) ⊗ G).left) (z : Z) {J : (Z ⟶ G.left) → L.ι} (hJ : Good L z J) :
    sval (upSec G σ) r z J = sval σ (r ≫ (snd (Over.mk (𝟙 S)) G).left) z J :=
  GlobalTheory.VVRank.sval_pullTo σ _ _ r z hJ

end GlobalTheory.TorRef
