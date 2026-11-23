import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepsOnto

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.SpectralTiesReal
open scoped TensorProduct

namespace GlobalTheory.Core.Rk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Link (D : D7) (u : D.what₂.Word) (W : Tower D) where

  P : W.Lv

  eT : (D.mem u).P.Mt →ₗ[ℂ] W.CXP P
  eT_onto : Function.Surjective eT

  jE : W.CP P 0 →ₗ⋆[ℂ] D.s.HH
  jE_onto : Function.Surjective jE

  Θ : Desc D u
  Θ_eq : ∀ F, ∃ T₀ : W.CP P 0, W.IsDn (eT F) T₀ ∧ Θ F = jE T₀

namespace Link

variable {D : D7} {u : D.what₂.Word} {W : Tower D} (L : Link D u W)

theorem ontoAll (h : W.Onto L.P) : OntoAll D u L.Θ := by
  intro y
  obtain ⟨T₀, rfl⟩ := L.jE_onto y
  obtain ⟨T, hT, h1, h2⟩ := h T₀.1 T₀.2
  obtain ⟨F, hF⟩ := L.eT_onto ⟨T, hT⟩
  obtain ⟨T₁, ⟨h3, h4⟩, h5⟩ := L.Θ_eq F
  refine ⟨F, ?_⟩
  rw [h5]
  congr 1
  apply Subtype.ext
  have e : (⟨(L.eT F).1, h3⟩ : W.CX) = ⟨T, h1⟩ := Subtype.ext (show (L.eT F).1 = T by rw [hF])
  rw [h4, h2, e]

open Classical in

def TopPin {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) : Prop :=
  ∃ J : SmT W.MX →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ), Function.Injective J ∧
    (∀ v, J v ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramP D) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.sgT u)) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ (v : W.MX.Vec) (w : W.MX.sm τ), (w : W.MX.H τ) = W.MX.rep τ g (v τ) →
      ∀ y y' : Formalism.L2.Forms.FrP D,
        Formalism.L2.Forms.IsTr (Function.update (fun _ => 1) τ
          (g.reindex (finCongr (Formalism.L2.Forms.rankP D)) (finCongr (Formalism.L2.Forms.rankP D)))) y' y →
        J (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = J (PiTensorProduct.tprod ℂ v) y') ∧
    ∀ (F : (D.mem u).P.Mt) (c : (D.fm u).clsP) (v : SmT W.MX) (h : GA D D.sp.X'), h ∈ GfC D.sp.X' →
      (∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom D.sp.X' h)).1 i j =
        (Tf.clsP.y c).1.1 (finCongr (Formalism.L2.Forms.rankP D) i) (finCongr (Formalism.L2.Forms.rankP D) j)) →
      (L.eT F).1 v h = (Nat.card ((D.fm u).stabilizer₂ c) : ℂ) *
        (D.mem u).P.period (Tf.valP.eW.symm (Pi.single c (J v))) F

def RowPinAt (S : STies D) (hF : FinX S.Y) (v₀ : (W.MY 0).Vec) (t : GA D (Yc D 0)) : Prop :=
  (∀ τ, ‖(v₀ τ : (W.MY 0).H τ)‖ = 1) ∧ S.X.B.I = RationalEmbedding.inst D ∧
    ∃ ι : GA D (Yc D 0) ≃* S.X.B.I.GA, HEq ι (RationalEmbedding.iota D).toMulEquiv ∧ ∀ T : W.CP L.P 0,
      (((show Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX S.X from (S.hI hF).eHH (L.jE T)) : Formalism.L2.SG.RowDict.L2X S.X) : S.X.B.I.GA → ℂ)
        =ᵐ[Formalism.L2.SG.RowDict.muX S.X] fun x => star (T.1 (PiTensorProduct.tprod ℂ v₀) (ι.symm x * t))

def RowPin (S : STies D) (hF : FinX S.Y) : Prop := ∃ v₀ t, L.RowPinAt S hF v₀ t

def RowPinE (S : STies D) (hF : FinX S.Y) : Prop := (∀ x : S.X.B.I.E, HEq (S.X.ιE x) x) ∧ L.RowPin S hF

end Link

structure STrue0 (D : D7) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) extends STies D where
  tr : ∀ u, Formalism.L2.SG.ColDict.Transport X u (F₀ u)
  into : ∀ u, Formalism.L2.SG.ColDict.ColDictInto X (tr u) Y.hK
  bij : ∀ u, Formalism.L2.SG.ColDict.ColDictBij X (tr u) Y.hK
  lev : ∀ u, Formalism.L2.SG.ColDict.LevelMatch X (tr u) Y.hK
  colPin : ∀ (hF : FinX Y) (u : D.what₂.Word) (x : D.s.Cu u),
    Formalism.L2.SG.ColDict.colDict X (tr u) Y.hK (into u) (bij u) ((hI hF).eCu u x) = D.s_Cu u x
  inst : X.B.I = RationalEmbedding.inst D
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D

  pin : ∀ x : X.B.I.E, HEq (X.ιE x) x

structure STrue (D : D7) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) extends STies D where

  hF : FinX Y
  tr : ∀ u, Formalism.L2.SG.ColDict.Transport X u (F₀ u)
  into : ∀ u, Formalism.L2.SG.ColDict.ColDictInto X (tr u) Y.hK
  bij : ∀ u, Formalism.L2.SG.ColDict.ColDictBij X (tr u) Y.hK
  lev : ∀ u, Formalism.L2.SG.ColDict.LevelMatch X (tr u) Y.hK
  colPin : ∀ (u : D.what₂.Word) (x : D.s.Cu u),
    Formalism.L2.SG.ColDict.colDict X (tr u) Y.hK (into u) (bij u) ((hI hF).eCu u x) = D.s_Cu u x
  inst : X.B.I = RationalEmbedding.inst D
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D

  pin : ∀ x : X.B.I.E, HEq (X.ιE x) x

section Bare

variable {D : D7} {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u}

def STrue.bare (S : STrue D F₀) : STrue0 D F₀ where
  toSTies := S.toSTies
  tr := S.tr
  into := S.into
  bij := S.bij
  lev := S.lev
  colPin := fun _ => S.colPin
  inst := S.inst
  locTied := S.locTied
  pin := S.pin

def STrue0.withFin (S : STrue0 D F₀) (hF : FinX S.Y) : STrue D F₀ where
  toSTies := S.toSTies
  hF := hF
  tr := S.tr
  into := S.into
  bij := S.bij
  lev := S.lev
  colPin := S.colPin hF
  inst := S.inst
  locTied := S.locTied
  pin := S.pin

def STrue.equivBare : STrue D F₀ ≃ {S : STrue0 D F₀ // FinX S.Y} where
  toFun S := ⟨S.bare, S.hF⟩
  invFun S := S.1.withFin S.2
  left_inv _ := rfl
  right_inv _ := rfl

end Bare

section Built

open GlobalTheory.Mem GlobalTheory.Mem.Col2

structure World {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) where
  ok : I.Ok
  pins : TC.Pins B X
  C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)
  std : I.StdC l Z C
  S : STrue (I.rec7 l Z) fun u => (C.forms u).to0

def TrueD (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), D = I.rec7 l Z ∧ Nonempty (World I l Z)

theorem TrueD.elim {Q : D7 → Prop}
    (h : ∀ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), World I l Z → Q (I.rec7 l Z))
    {D : D7} (hD : TrueD D) : Q D := by
  obtain ⟨B, X, I, l, Z, rfl, ⟨w⟩⟩ := hD
  exact h B X I l Z w

theorem TrueD.sTies {D : D7} (hD : TrueD D) :
    ∃ S : STies D, FinX S.Y ∧ Formalism.L2.SG.Pf.LocCP.LocTied D :=
  TrueD.elim (Q := fun D => ∃ S : STies D, FinX S.Y ∧ Formalism.L2.SG.Pf.LocCP.LocTied D)
    (fun _ _ _ _ _ w => ⟨w.S.toSTies, w.S.hF, w.S.locTied⟩) hD

structure World0 {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) where
  ok : I.Ok
  pins : TC.Pins B X
  C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)
  std : I.StdC l Z C
  S : STrue0 (I.rec7 l Z) fun u => (C.forms u).to0

def IsTrueColumnDatum (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), D = I.rec7 l Z ∧ Nonempty (World0 I l Z)

section Maps

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

def World.bare (w : World I l Z) : World0 I l Z := ⟨w.ok, w.pins, w.C, w.std, w.S.bare⟩

def World0.withFin (w : World0 I l Z) (hF : FinX w.S.Y) : World I l Z := ⟨w.ok, w.pins, w.C, w.std, w.S.withFin hF⟩

end Maps

theorem TrueD.bare {D : D7} (hD : TrueD D) : IsTrueColumnDatum D :=
  let ⟨B, X, I, l, Z, e, ⟨w⟩⟩ := hD; ⟨B, X, I, l, Z, e, ⟨w.bare⟩⟩

theorem trueD_iff {D : D7} (h : ∀ T : STies D, FinX T.Y) : TrueD D ↔ IsTrueColumnDatum D := by
  refine ⟨TrueD.bare, ?_⟩
  rintro ⟨B, X, I, l, Z, rfl, ⟨w⟩⟩
  exact ⟨B, X, I, l, Z, rfl, ⟨w.withFin (h w.S.toSTies)⟩⟩

end Built

variable (D : D7) (u : D.what₂.Word)

def MITower : Prop := ∃ (W : Tower D) (L : Link D u W), W.Is ∧ MIMap D u L.Θ

def MIKerTower : Prop := ∃ (W : Tower D) (L : Link D u W), W.Is ∧ MIKer D u L.Θ

def OntoTower : Prop := ∀ W : Tower D, W.Is → ∀ P : W.Lv, W.Onto P

theorem MITower.ker (h : MITower D u) : MIKerTower D u :=
  let ⟨W, L, h1, h2⟩ := h; ⟨W, L, h1, MIMap.miKer D u h2⟩

theorem kerIncl_of_tower (h : MIKerTower D u) (h' : OntoTower D) : KerIncl D u :=
  let ⟨W, L, h1, h2⟩ := h
  kerIncl_of D u h2 (OntoAll.ontoP D u (L.ontoAll (h' W h1 L.P)))

def MIPinned {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (w : World I l Z) (u : (I.rec7 l Z).what₂.Word) : Prop :=
  ∃ (W : Tower (I.rec7 l Z)) (L : Link (I.rec7 l Z) u W), W.Is ∧ L.TopPin (w.C.forms u) ∧ L.RowPinE w.S.toSTies w.S.hF ∧
    MIMap (I.rec7 l Z) u L.Θ

def MIPinned0 {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (w : World0 I l Z) (u : (I.rec7 l Z).what₂.Word) : Prop :=
  ∃ (W : Tower (I.rec7 l Z)) (L : Link (I.rec7 l Z) u W), W.Is ∧ L.TopPin (w.C.forms u) ∧
    (∀ hF : FinX w.S.Y, L.RowPinE w.S.toSTies hF) ∧ MIMap (I.rec7 l Z) u L.Θ

theorem miPinned_withFin_iff {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (w : World0 I l Z) (hF : FinX w.S.Y) (u : (I.rec7 l Z).what₂.Word) :
    MIPinned (w.withFin hF) u ↔ MIPinned0 w u :=
  ⟨fun ⟨W, L, h1, h2, h3, h4⟩ => ⟨W, L, h1, h2, fun _ => h3, h4⟩, fun ⟨W, L, h1, h2, h3, h4⟩ => ⟨W, L, h1, h2, h3 hF, h4⟩⟩

def thetaRec (V : D.what₂.EE →ₗ[ℂ] D.what₂.EE) : Desc D u :=
  D.sEE.toLinearMap ∘ₛₗ (V ∘ₗ D.iota0 ∘ₗ (D.eMt u).toLinearMap)

def RowsAll : Prop := Function.Surjective D.sEE

end GlobalTheory.Core.Rk

end
