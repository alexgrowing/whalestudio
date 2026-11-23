import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerPin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ShortIn
import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.LiftDataTimeEqWeightTime

noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Rec

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree Formalism.IndefR.Obj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Q : Par D}

def ofGeo {M : ℕ} (S : SlopeGeometry.SharpGeo Q M) : SharpGeo Q M :=
  { S with }

variable (P : SlopeBoundParameters) (S : SlopeGeometry.SharpGeo Q (SlopeGeometry.Msh D P)) (i : Fin D.R.m)

variable (D) in

def gapG : ℝ := P.η / P.m / (4 * (SlopeGeometry.Tn D P : ℝ))

variable (D) in

def boundG : ℝ := (SlopeGeometry.pack0 D P i 0 (fun _ : Unit => 0)).B0

def GeoPin (B : SlopeGeometry.MbarIn P S i) : Prop :=
  TowerPin (S.Xo i) S.c (SlopeGeometry.wtZ' D i (SlopeGeometry.upR D P i)) ⌊boundG D P i⌋₊ B.top B.dg

structure GeoRows : Prop where
  h0 : D.R.m ^ 4 ≤ D.R.f
  indef : (i : ℕ) + 1 < D.R.m
  primes : (2 * discr D.host.E * S.l.M').natAbs.primeFactors.card ≤ 4 * D.R.f * D.R.r ^ 2
  rd : P.rd = D.host.rdE
  lval : P.Lc = dlogL D 1
  gaps : Top.WeightHyp (SlopeGeometry.pp D i) (SlopeGeometry.upR D P i) (gapG D P)
  reg : ∀ τ, StrictAnti (SlopeGeometry.u1R D P i τ)

def GeoSmallIn (Λ cc : ℝ) : Prop :=
  ∀ Z : SlopeGeometry.Cmp P S i, SlopeGeometry.delC P S i Z ≠ 0 ∧
    ShortIn (SlopeGeometry.latW P S i (SlopeGeometry.u1R D P i) Z) (SlopeGeometry.ipW P S i (SlopeGeometry.u1R D P i) Z) Λ ∧
    MultIn (S.U i) (S.gen i) (S.e i) Z (SlopeGeometry.wtZ' D i (SlopeGeometry.u1R D P i)) (SlopeGeometry.wtZ' D i (SlopeGeometry.upR D P i))
      ⌊boundG D P i⌋₊ cc

def mbarOfGeo (B : SlopeGeometry.MbarIn P S i) : MbarIn (ofGeo S) i (SlopeGeometry.upR D P i) := ⟨B.top, B.dg, B.dg_lim, B.conv⟩

end GlobalTheory.CompanionTheory.Ar.Rec
