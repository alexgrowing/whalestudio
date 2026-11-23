import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.RowEx
open Formalism.L2.Host (HChar)
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.LiteralAutomorphy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NEa (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (A : AtP) : NExt hL := fun K B f T w Z Wt p0 t nch n xd c =>
  N K B f T w Z Wt p0 t nch n xd c × PLift (A K B f T)

@[reducible] def prmA (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (A : AtP) : Prm hL :=
  prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) A) SExt.none (geoCl anyGeometry)

abbrev GKey (P : Pre) : Type :=
  HeightOneSpectrum (𝓞 P.host.F) × HeightOneSpectrum (𝓞 P.host.E) × (Fin P.R.m → HChar P.host.E)

def gkeyOf {X : Stages} {T : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) : GKey X.B.toPre :=
  (G.pl.v0, G.pl.w G.pl.v0, fun a => G.ch.chiH (a.1 + 1))

def GKeyFin : Prop := ∀ (P : Pre) (c : ℝ), ∃ 𝒦 : Set (GKey P), 𝒦.Finite ∧
  ∀ (X : Stages) (T : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T) (sc : GlobalTheory.ChiGrid.Consts) (G : GridData L sc), X.B.toPre = P → sc.cGap = c →
    ∃ κ ∈ 𝒦, HEq (gkeyOf G) κ

def WeilEx : Prop := BigR fun R sc => ∀ G : GridData R.toLevCh sc, ∃ W : G.Weil, W.Over R ∧ Nonempty (GridChoice W Set.univ)

def NFSq : Prop := ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
  GlobalTheory.SqTop.Rec large₂ → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh D T) (μ₀ : T), L.Is μ₀ → ∀ G : GridData L ⟨1, CF, large₂.sc.b⟩,
    InNF fun _ σ => GlobalTheory.BigTop.Fun.SqIn G μ₀ σ

def TrSq : Prop := OnAgree fun {_ _ _ _ _ _ _} G G' _ _ _ _ μ₀ μ₀' _ => ∀ (M : IntermediateField ℚ ℂ) (σ : M →+* ℂ),
  GlobalTheory.BigTop.Fun.SqIn G μ₀ σ → GlobalTheory.BigTop.Fun.SqIn G' μ₀' σ

def Full {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {sc : GlobalTheory.ChiGrid.Consts}
    (G : GridData R.toLevCh sc) : Prop :=
  ∃ W M ρ ξ cv rm S rp n e c, (⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ : Choice R).Is ∧
    (⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ : Choice R).FieldOK ∧ GlobalTheory.BigTop.Fun.SqIn G A.μ0 D.what₂.embLL

def GridAt (s : Scale) (CF : ℝ) (X : Stages) (f : Fr X.B.toPre) (Ξ : Set (HChar X.B.host.E)) : Prop :=
  ∀ large₂ : SizeData₂ X.toD7, large₂.sc = s → GlobalTheory.SqTop.Rec large₂ → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type)
    (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL]
    (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F → R.C = Fr.at X f → TwistPlacesOffPrimeQZero R.toLevCh →
    (∀ t, ∃ ξ ∈ Ξ, HEq (R.toLevCh.xiH t) ξ) → ∀ G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩,
      ∃ G : GridData R.toLevCh ⟨1, CF, s.b⟩, gkeyOf G = gkeyOf G₀ ∧ Full R G

def ExGrid : Prop := ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ s : Scale, s.eps = ε → x₀ ≤ s.x →
  ∀ (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)), Ξ.Finite → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ (X : Stages) (f' : Fr X.B.toPre) (Ξ' : Set (HChar X.B.host.E)), X.B.toPre = P → HEq f' f → HEq Ξ' Ξ →
      (∀ z ∈ S, z ∈ Set.range X.toD7.what₂.embLL) → GridAt s CF X f' Ξ'

def GridA (CF : ℝ) : AtP := fun K B f T => ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
  (N : NStage B C W) (G : GJStage B C), GridAt K.s CF ⟨B, C, W, V, S, N, G⟩ f (T.set f)

end GlobalTheory.Mem.LiteralAutomorphy

end
