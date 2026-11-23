import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationVectorBundleAbelianPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSmoothOfRelativeDimensionOfGeneri

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

variable {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
  {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ}

theorem isFrame_chart (h : IsGrpPullback H G x ψ) (j : PUnit → (hodge G g).ι) :
    IsFrame fun i => (omegaBase h).app (LB.wchart (hodge G g) (fun _ => x) j)
      (pullbackSections x (omega G) (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit) ((j PUnit.unit).e i)) :=
  (GlobalTheory.BadPt.Fibre.frame_pb x (j PUnit.unit).isFrame _).map_iso (omegaBase h)

def gen (h : IsGrpPullback H G x ψ) {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) : LB.Gen ((hodge G g).pull x) where
  s j := (isFrame_chart h j).detUnit ha le_rfl le_top

end GlobalTheory.HodgeFrameGen
