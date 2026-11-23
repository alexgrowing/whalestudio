import Formalism.LocalToGlobal.Columns.ValuationPosIffMemSeen
import Formalism.LocalToGlobal.Columns.CoordLatticeSelfDualEqStd

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

structure AtTOwed (hS : SpStd d.toColBase) (hH : HostHyp d) where
  disc : ∀ u, AtTDisc (d.colRec a) u
  moves : ∀ u, AtTMoves (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)
  xp : ∀ u, AtTXp (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)

def hermAtT (hS : SpStd d.toColBase) (hH : HostHyp d) (O : AtTOwed a hS hH) (u : d.what₂.Word) :
    CH.AtT (d.colRec a) u (tieEV d.sp.cm d.hX d.hPr u) (fun v => tieFv d.sp.cm d.hX d.hPr u v) :=
  atTOf (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) (fun v => tieFv d.sp.cm d.hX d.hPr u v)
    (fun v x => tieFv_mk d.sp.cm d.hX d.hPr u v x) (th_seen a hH u) (O.disc u) (O.moves u) (O.xp u)

section Asm

variable (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)
  (O : AtTOwed a hS hH)

theorem cofTied : CH.CofTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := by
  intro u
  show (d.piT d.u₀ : d.host.E) / (d.piT u : d.host.E) * (d.piT u : d.host.E) = (d.piT d.u₀ : d.host.E)
  exact div_mul_cancel₀ _ (basePi_of_ok d.hX d.hPr u).coe_ne_zero

theorem baseTied : CH.BaseTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := by
  intro u pb hpb
  have hpb' : algebraMap (𝓞 d.X.E) d.X.E pb = star (algebraMap (𝓞 d.X.E) d.X.E (d.Pr.piT u)) := by
    rw [att_star_eq]
    exact hpb
  refine ⟨?_, fun i h1 hm => ?_⟩
  · rw [coordLattice_selfDual_zero hS]
    exact levPack_base d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) _ _ _ _ (hK u 0) (hCrd0 hS u) pb hpb'
  · rw [coordLattice_selfDual_eq_std hS i hm]
    exact levPack_base d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) _ _ _ _ (hK u i) (hCrd hS u i hm) pb hpb'

structure HermOwed where
  levelZeroCompatibility : CH.Lev0Tied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)
  ad : CH.AdTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)
  piG : CH.PiGConst (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) levelZeroCompatibility
  stabMap : CH.StabMapTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)
  fvI : CH.FvStepTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)

def colsHerm (W : HermOwed a hS hH hP hK S hI O) : CH.ColsHerm (d.colRec a) where
  base := hermCols a hS hP hK S hI
  atT := hermAtT a hS hH O
  levelZeroCompatibility := W.levelZeroCompatibility
  ad := W.ad
  cof := cofTied a hS hH hP hK S hI O
  piG := W.piG
  stabMap := W.stabMap
  fvI := W.fvI
  std := stdTied a hS
  baseL := baseTied a hS hH hP hK S hI O

end Asm

end Formalism.L2.Col
