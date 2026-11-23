import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemberChainFormsLevelPrimeEqMember
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DetIntOfLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Formalism.LocalToGlobal.GroupLattices.Joint0

noncomputable section

section
namespace GlobalTheory.Port

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.KAat Formalism.L2.Ker
open GlobalTheory.TwU (StepCharts ChainCharts AdData AdPins AdTie latCo)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Site

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Tw : TwForms D} {μ : D.what₂.Tup}

def SiteD.inTw (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) :
    CmpJIn Tw u μ w hg (Z.lv Fl ht) := Formalism.MainNotions.G.KAat.inTw fun j hj => Z.st Fl ht Gt j hj

def ValAll (Tw : TwForms D) (St : ChainCharts D u μ) : Prop :=
  ∀ i hi, ValuationCompatibleChart (Tw.fm u μ) (St i hi).eY (fun _ => True) (St i hi).chOf (St i hi).K

set_option maxHeartbeats 2000000 in

def foOf (Hh : Formalism.L2.Herm.SymmetricHermitianColumns D) (St : ChainCharts D u μ) (hv : ValAll Tw St) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    FormsIn (Tw.fm u μ) (j + 1) hj where
  T := (St (j + 1) hj).T
  bad := (St (j + 1) hj).bad
  eY := (St (j + 1) hj).eY
  okW := fun _ => True
  Ch := (St (j + 1) hj).Ch
  chOf := (St (j + 1) hj).chOf
  lat := (St (j + 1) hj).lat
  K := (St (j + 1) hj).K
  val := hv (j + 1) hj
  tw := fun _ => DetTw.ofChiD (detTieOf Hh _) (cTw D (j + 1))

end Site

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure JIn (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) where
  Gd : GroupCompatibilityAll D hT ex.cmp
  Hh : Formalism.L2.Herm.SymmetricHermitianColumns D
  rel : Formalism.L2.Herm.SymmetricRelativeDeterminant D Hh
  St : ChainCharts D u μ
  A : AdData t u μ St
  a : 𝓞 D.host.E
  pins : AdPins A Hh.dt
  tie : AdTie A Hh.dt a
  val : ValAll ex.tw St
  fin : ∀ i hi, Finite (St i hi).Ch
  ord : ∀ i hi β, ∃ n : ℕ, 0 < n ∧ ∀ κ, ((St i hi).K β).lev.chi κ ^ n = 1
  base : ∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)
  joint0 : Joint0 Gd.herm.lev0 u (Gd.forms u)
  e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0
  jointCmpEmbeddingY : (D.mem u).C.Y 0 ≃ (D.chTw u μ).Y 0
  e0Tw : ∀ φ c y, D.e0Tw u μ φ (e0 c) (jointCmpEmbeddingY y) = φ c y
  lev0 : ∀ β : (St 0 (Nat.zero_le _)).Ch, ((St 0 _).K β).lev.Lb = (Gd.forms u).cls0.lev.Lb ∧
    ((St 0 _).K β).lev.Uloc = (Gd.forms u).cls0.lev.Uloc ∧ ((St 0 _).K β).lev.U = (Gd.forms u).cls0.lev.U ∧
    ∀ (κ : ((St 0 _).K β).lev.U) (κ' : (Gd.forms u).cls0.lev.U), κ.1 = κ'.1 → ((St 0 _).K β).lev.chi κ = (Gd.forms u).cls0.lev.chi κ'
  ch0 : Subsingleton (St 0 (Nat.zero_le _)).Ch
  y0 : ∀ c, ∃ κ : (Gd.forms u).cls0.lev.U, ((St 0 (Nat.zero_le _)).y (e0 c)).1 = ((Gd.forms u).cls0.y c).1 * κ.1 ∧
    (Gd.forms u).cls0.lev.chi κ = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ q ∈ Dx.Qp μ, ((q : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) →
      bc (prV (E := D.host.E) v) κ.1 = 1
  fr0 : ∀ y, (St 0 (Nat.zero_le _)).eY (jointCmpEmbeddingY y) = (Gd.forms u).val0.eY y
  rat : ∀ j, j < D.R.m → (ex.tw.fm u μ).KRat j
  kin : ∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y
  chiD : ∀ z : D.Dt, ∃ r : D.what₂.LL, D.what₂.embLL r = ((D.chiD z : ℂˣ) : ℂ)

end GlobalTheory.Port
end

end
