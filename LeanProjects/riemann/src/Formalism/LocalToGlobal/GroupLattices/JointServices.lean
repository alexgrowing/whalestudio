import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.Divisibility.JetBounds.Statement

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.DIV Formalism.L2.Indef

noncomputable section

namespace Formalism.L2.G.ServJoint

structure ColBr (D : D7) : Type 1 where

  Gp : Type
  [grp : Group Gp]
  [fin : Fintype Gp]

  Pl0 : Type

  T : Type

  m : ℕ

  A : FamIn D.what₂.LL Gp Pl0 T m

  P0 : Subgroup Gp
  ψ0 : P0 →* D.what₂.LLˣ

  Ps : Subgroup Gp
  ψs : Ps →* D.what₂.LLˣ

  Zs : DefSub A.fam.amb

  S0 : IndefData (A.side P0 ψ0 Zs)
  S1 : IndefData (A.side Ps ψs Zs)

  X0 : BaseLevelRowSide D

  Dc : DefCols (A.side Ps ψs Zs)

  I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 X0 Dc

attribute [instance] ColBr.grp ColBr.fin

structure ColBr.Tied {D : D7} (B : ColBr D) : Prop where

  ok : ∃ s : ℕ, B.A.fam.Ok s

  mu : ∀ w : D.what₂.places.Pl, D.what₂.muAt w = B.I.tup (B.S1.μ (D.plEq w))

  sharp : RowSideTie D B.A (RowSide.sharp D) B.Ps B.ψs B.Zs B.S1 B.I.tup B.I.eRR B.I.jA

  dcPt : ∀ (u : D.what₂.Word) (t : B.T) (x : Fin (B.Dc.a (B.I.wU u)) → D.what₂.LL)
    (F : Fin ((B.A.side B.Ps B.ψs B.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (B.Dc.Pt (B.I.wU u) t x F) =
      D.what₂.perCol u (B.I.tup t) (D.jN u (B.I.eNu u x)) (B.I.jA t ((rV0 D B.A B.Ps B.ψs t).mulVec F))

structure OTie (D : D7) : Prop where
  ded : IsDedekindDomain D.what₂.O
  int : ∃ ι : D.what₂.O →+* 𝓞 D.what₂.LL, Function.Injective ι ∧ ∀ a, ((ι a : 𝓞 D.what₂.LL) : D.what₂.LL) = D.what₂.OtoLL a
  aint : Rows.AIntegral D.what₂
  form : ∀ μ, DV.Used D μ → OForm (D.what₂.Mtilde μ)

def CutUp (D : D7) (μ : D.what₂.Tup) : Prop :=
  ∀ x : D.what₂.Amb μ, (∃ c : D.what₂.Amb μ → 𝓞 D.what₂.LL, x = ∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.embLL (c v : D.what₂.LL) • v) →
    x ∈ D.what₂.V0 μ →
    ∃ (s : Finset (D.what₂.Amb μ)) (c : D.what₂.Amb μ → 𝓞 D.what₂.LL),
      (s : Set (D.what₂.Amb μ)) ⊆ (D.what₂.Mtilde μ).carrier ∩ (D.what₂.V0 μ : Set (D.what₂.Amb μ)) ∧
      x = ∑ y ∈ s, D.what₂.embLL (c y : D.what₂.LL) • y

def NPc {D : D7} {L : SizeData₂ D} (B : ColBr D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) : Submodule (𝓞 D.what₂.LL) (Fin (B.Dc.a (B.I.wU u)) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL) {x | InNP X Y K c u w (D.nuIn u (B.I.eNu u x))}

def sgServ {D : D7} {L : SizeData₂ D} (X : Inst D L) (K : Consts) (Xe : ErrX D) (ce : ErrC) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) : ℝ :=
  ur D w (totS X K Xe ce 1 u w - vDG D u w)

def OffTG (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : Prop :=
  D.what₂.places.resChar w ≠ (D.mem u).A.T ∧ D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ)

def SvPl (D : D7) (u : D.what₂.Word) : Set (HeightOneSpectrum (𝓞 D.what₂.LL)) := {z | OffTG D u (D.plEq.symm z)}

def PerToVal2 : Prop :=
  ∀ (D : D7) (B : ColBr D), B.Tied → ∀ (u : D.what₂.Word) (t : B.T), CutUp D (B.I.tup t) →
    ∀ (z : HeightOneSpectrum (𝓞 D.what₂.LL)) (s : ℝ) (N : Set (Fin (B.Dc.a (B.I.wU u)) → D.what₂.LL)),
    (∀ x ∈ N, ∀ F ∈ (D.what₂.Mtilde (B.I.tup t)).carrier, F ∈ D.what₂.V0 (B.I.tup t) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (B.I.tup t) (D.jN u (B.I.eNu u x)) F ∧
        (y = 0 ∨ s ≤ (vAdd z y : ℝ))) →
    LocalValuationBoundAt B.Dc (B.I.wU u) t (Submodule.span (𝓞 D.what₂.LL) N) z s

def CutUpOfOTie : Prop := ∀ (D : D7), OTie D → ∀ μ, DV.Used D μ → CutUp D μ

def JointAt : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (Dx : DivX D) (T : TwForms D)
    (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (B : ColBr D),
    B.Tied → (∀ μ, DV.Used D μ → CutUp D μ) → PairInt D Dx T → Ties9 D L X Y c → ErrDefs D L Xe lev K ce →
    Conclusion1 D L X Y K c Dx T lev Xe ce 1 →
    ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl), OffTG D u w →
      LocalValuationBoundAt B.Dc (B.I.wU u) (B.S1.μ (D.plEq w)) (NPc B X Y K c u w) (D.plEq w) (sgServ X K Xe ce u w)

def MemNPcServed : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (B : ColBr D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
    ∀ x, x ∈ NPc B X Y K c u w ↔ InNP X Y K c u w (D.nuIn u (B.I.eNu u x))

def NuLeAt : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (B : ColBr D),
    c.NuServedDef X Y K →
    (∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T → LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)) →
    (∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
      VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ → GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) →
    ∀ (u : D.what₂.Word) (Nu : Submodule (𝓞 D.what₂.LL) (Fin (B.Dc.a (B.I.wU u)) → D.what₂.LL)),
      (∀ x ∈ Nu, B.I.eNu u x ∈ L.NuLat u) →
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ (D.mem u).A.T → Nu ≤ NPc B X Y K c u w

def SgLeAt : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC),
    ErrDefs D L Xe lev K ce →
    (∀ (w : D.what₂.places.Pl), ∀ j ∈ SizeData₂.lifts D, L.gainD j w ≤ gainS X K (D.what₂.places.resChar w) j) →
    ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl), ur D w (L.sg u w) ≤ sgServ X K Xe ce u w

def SecondLevelHypothesisAt : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (Dx : DivX D) (T : TwForms D)
    (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (B : ColBr D),
    B.Tied → (∀ μ, DV.Used D μ → CutUp D μ) → PairInt D Dx T → Ties9 D L X Y c → ErrDefs D L Xe lev K ce →
    c.NuServedDef X Y K →
    (∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T → LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)) →
    (∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
      VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ → GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) →
    (∀ (w : D.what₂.places.Pl), ∀ j ∈ SizeData₂.lifts D, L.gainD j w ≤ gainS X K (D.what₂.places.resChar w) j) →
    Conclusion1 D L X Y K c Dx T lev Xe ce 1 →
    ∀ (u : D.what₂.Word) (Nu : Submodule (𝓞 D.what₂.LL) (Fin (B.Dc.a (B.I.wU u)) → D.what₂.LL))
      (sg : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
      (∀ x ∈ Nu, B.I.eNu u x ∈ L.NuLat u) →
      (∀ w : D.what₂.places.Pl, OffTG D u w → sg (D.plEq w) ≤ ur D w (L.sg u w)) →
      ∀ z ∈ SvPl D u, Nu ≤ NPc B X Y K c u (D.plEq.symm z) ∧
        LocalValuationBoundAt B.Dc (B.I.wU u) (B.S1.μ z) (NPc B X Y K c u (D.plEq.symm z)) z (sg z)

def SecondLevelValuationAt : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (B : ColBr D), B.Tied → (∀ μ, DV.Used D μ → CutUp D μ) → Formalism.MainNotions.LocalQuadraticParts.UnroundedValuationBound D L →
    ∀ (u : D.what₂.Word) (Nu : Submodule (𝓞 D.what₂.LL) (Fin (B.Dc.a (B.I.wU u)) → D.what₂.LL))
      (sg : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
      (∀ x ∈ Nu, B.I.eNu u x ∈ L.NuLat u) → (∀ w : D.what₂.places.Pl, sg (D.plEq w) ≤ ur D w (L.sg u w)) →
      ∀ z, ∀ φ ∈ Nu, ∀ F ∈ (B.A.side B.Ps B.ψs B.Zs).Mt (B.S1.μ z),
        B.Dc.Pt (B.I.wU u) (B.S1.μ z) φ F = 0 ∨ sg z ≤ (Formalism.DivisionValues.vw z (B.Dc.Pt (B.I.wU u) (B.S1.μ z) φ F) : ℝ)

def SecondLevelValuationAtRestricted : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (B : ColBr D), B.Tied → (∀ μ, DV.Used D μ → CutUp D μ) → Formalism.MainNotions.LocalQuadraticParts.adm2 D L →
    ∀ (u : D.what₂.Word) (Nu : Submodule (𝓞 D.what₂.LL) (Fin (B.Dc.a (B.I.wU u)) → D.what₂.LL)),
      (∀ x ∈ Nu, B.I.eNu u x ∈ L.NuLat u) →
      ∀ z, ∀ φ ∈ Nu, ∀ F ∈ (B.A.side B.Ps B.ψs B.Zs).Mt (B.S1.μ z),
        B.Dc.Pt (B.I.wU u) (B.S1.μ z) φ F = 0 ∨
          ((⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ : ℤ) : ℝ) ≤
            (Formalism.DivisionValues.vw z (B.Dc.Pt (B.I.wU u) (B.S1.μ z) φ F) : ℝ)

def UnitAt : Prop :=
  ∀ (D : D7) (w : D.what₂.places.Pl) (y : ℝ),
    ur D w y = (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) * y

def SecondLevelHypothesisFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ServF Fm →
  (∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), PairInt (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw) →
  (∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) (p : ℕ), Cand (Fm.D x i) (Fm.L x i) Fm.GK p →
    p ≠ ((Fm.D x i).mem u).A.T → GIdx (Fm.D x i).host ((Fm.D x i).mem u).A.T p) →
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x) (B : ColBr (Fm.D x i)), B.Tied → (∀ μ, DV.Used (Fm.D x i) μ → CutUp (Fm.D x i) μ) →
    ∀ (u : (Fm.D x i).what₂.Word) (Nu : Submodule (𝓞 (Fm.D x i).what₂.LL) (Fin (B.Dc.a (B.I.wU u)) → (Fm.D x i).what₂.LL))
      (sg : HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → ℝ),
      (∀ y ∈ Nu, B.I.eNu u y ∈ (Fm.L x i).NuLat u) →
      (∀ w : (Fm.D x i).what₂.places.Pl, OffTG (Fm.D x i) u w → sg ((Fm.D x i).plEq w) ≤ ur (Fm.D x i) w ((Fm.L x i).sg u w)) →
      ∀ z ∈ SvPl (Fm.D x i) u,
        Nu ≤ NPc B (Fm.Gx x i) (Fm.Gy x i) Fm.GK (Fm.ex x hx i).cmp u ((Fm.D x i).plEq.symm z) ∧
        LocalValuationBoundAt B.Dc (B.I.wU u) (B.S1.μ z) (NPc B (Fm.Gx x i) (Fm.Gy x i) Fm.GK (Fm.ex x hx i).cmp u ((Fm.D x i).plEq.symm z)) z (sg z)

end Formalism.L2.G.ServJoint

end
