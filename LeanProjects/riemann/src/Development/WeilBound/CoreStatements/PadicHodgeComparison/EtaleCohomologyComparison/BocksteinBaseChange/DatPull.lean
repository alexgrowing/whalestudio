import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimAlg
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsPhi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge GlobalTheory.LogCris

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

namespace Model

abbrev L (M : Model l K) (k : Bool) (n : ℕ) : (B.bs l k n).Fun := B.Lc (B.schFn M.p) (okToOC l K) k n

abbrev Hc (M : Model l K) (k : Bool) (n j : ℕ) : Type 1 := B.Hc (B.schFn M.p) (okToOC l K) k n j

abbrev HS (M : Model l K) (k : Bool) (j : ℕ) : Sys.{1} (Acris l) := B.HcSys (B.schFn M.p) (okToOC l K) k j

def galH (M : Model l K) (k : Bool) (j : ℕ) (σ : Gal(PadicAlgCl l/K)) : Sys.Hom (M.HS k j) (M.HS k j) (ACris.galCris σ) where
  f n := B.galHc _ _ σ (galOC_okToOC σ) k n j
  comm n x := SH.red_gal _ _ σ _ k n j x

def phiH (M : Model l K) (j : ℕ) : Sys.Hom (M.HS true j) (M.HS true j) (ACris.phi ℂ_[l] l) where
  f n := B.phiHc _ _ n j
  comm n x := SH.red_phi _ _ n j x

def pullH {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (k : Bool) (j : ℕ) :
    Sys.Hom (N.HS k j) (M.HS k j) (RingHom.id _) where
  f n := B.pullHc _ (B.schMap u hu) k n j
  comm n x := SH.red_pull _ _ k n j x

def HA (M : Model l K) (k : Bool) : GAlg (Acris l) K.fixingSubgroup :=
  limAlg (M.HS k) (σ := fun g => ACris.galCris (IntermediateField.fixingSubgroupEquiv K g))
    (fun j g => M.galH k j (IntermediateField.fixingSubgroupEquiv K g)) (fun n => CH.oneH (B.OcA (B.schFn M.p) (okToOC l K) k n))
    (fun n _ _ x y => (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) k n)).cup rfl x y)

end Model

def dat (Amp : ∀ M : Model l K, E.LineData M.X → Prop) : Dat (per l K) where
  Ch M := {D : E.LineData M.X // Amp M D}
  Mo _ _ _ _ := PUnit
  A {M} _ := M.MA
  phiA {M} _ j := (M.phiS j).lim.toAddMonoidHom
  pullA {_ _ u hu _ _} _ j := (Model.pullS u hu j).lim
  c1A {M} D y := E.IsFirstChernClassOfLineBundle M.p (okToOC l K) D.1 (show (M.MS 2).lim from y).1
  H {M} _ := M.HA false
  fil {M} _ j r x := ∀ n, (show (M.HS false j).lim from x).1 n ∈ B.HcFil (B.schFn M.p) (okToOC l K) false n r j
  c1H {M} D x := B.IsFirstChernFamily M.p D.1 (okToOC l K) false (show (M.HS false 2).lim from x).1
  pullH {_ _ u hu _ _} _ j := (Model.pullH u hu false j).lim.toAddMonoidHom
  H' {M} _ := (M.HA true).toGMod
  phi' {M} _ j := (M.phiH j).lim.toAddMonoidHom

def datPull (Amp : ∀ M : Model l K, E.LineData M.X → Prop) {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p}
    {a : (dat Amp).Ch M} {b : (dat Amp).Ch N} (_ : (dat Amp).Mo u hu a b) (j : ℕ) : ((dat Amp).H' b).N j →+ ((dat Amp).H' a).N j :=
  (Model.pullH u hu true j).lim.toAddMonoidHom

end CrystallineSemistableComparison
