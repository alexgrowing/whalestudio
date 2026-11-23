import Formalism.LocalToGlobal.HermitianColumns.ColsHerm

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)
  (g' : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w))
  (hd' : ∀ u w h, (g' u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)

abbrev setGat : D7 := { D with gat := g', gat_d := hd' }

open Formalism.L2.Herm

structure FullTiedNoG (D : D7) extends AllTied D where
  levelZeroCompatibility : Lev0Tied D base.toHermCols atT
  ad : AdTied D base.toHermCols atT
  cof : CofTied D base.toHermCols atT
  piG : PiGConst D base.toHermCols atT levelZeroCompatibility
  stabMap : StabMapTied D base.toHermCols atT
  fvI : FvStepTied D base.toHermCols atT
  relDet : RelativeDeterminantCompatible D base
  std : StdTied D
  vpos : PositiveVolumeCompatible D
  baseL : BaseTied D base.toHermCols atT

def FullTiedNoG.ofFull {D : D7} (X : FullTied D) : FullTiedNoG D := { X with }

def FullTiedNoG.toFull {D : D7} (X : FullTiedNoG D) (g : GTied D X.base) : FullTied D := { X with g := g }

theorem FullTiedNoG.toFull_base {D : D7} (X : FullTiedNoG D) (g : GTied D X.base) : (X.toFull g).base = X.base := rfl

theorem FullTiedNoG.toFull_g {D : D7} (X : FullTiedNoG D) (g : GTied D X.base) : (X.toFull g).g = g := rfl

def colsSet (H : HermCols D) : HermCols (setGat D g' hd') := { H with }

def hermSet (H : HermTied D) : HermTied (setGat D g' hd') := { H with }

theorem hermitian_setting_level_zero (H : HermTied D) : (hermSet D g' hd' H).lev0 = H.lev0 := rfl

set_option maxHeartbeats 4000000 in

def atTSet {u : D.what₂.Word}
    {e : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}}
    {eF : ∀ v : (D.mem u).A.vT, (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (e v).1.asIdeal)} (A : AtT D u e eF) :
    AtT (setGat D g' hd') u e eF := { A with }

set_option maxHeartbeats 4000000 in
def allSet (H : AllTied D) : AllTied (setGat D g' hd') where
  base := hermSet D g' hd' H.base
  atT := fun u => atTSet D g' hd' (H.atT u)
  vol := H.vol

set_option maxHeartbeats 4000000 in
theorem adSet (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (h : AdTied D H aT) :
    AdTied (setGat D g' hd') (colsSet D g' hd' H) (fun u => atTSet D g' hd' (aT u)) :=
  { h with }

set_option maxHeartbeats 4000000 in

def fullSet (H : FullTiedNoG D) : FullTiedNoG (setGat D g' hd') where
  toAllTied := allSet D g' hd' H.toAllTied
  levelZeroCompatibility := H.levelZeroCompatibility
  ad := adSet D g' hd' _ _ H.ad
  cof := H.cof
  piG := H.piG
  stabMap := H.stabMap
  fvI := H.fvI
  relDet := H.relDet
  std := H.std
  vpos := H.vpos
  baseL := H.baseL

theorem full_setting_level_zero (H : FullTiedNoG D) : (fullSet D g' hd' H).base.lev0 = H.base.lev0 := rfl

end Formalism.L2.G
