import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.Mem GlobalTheory.Mem.Top

namespace GlobalTheory.RowEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

abbrev RP := ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL], RealDat D A Ks → GlobalTheory.ChiGrid.Consts → Prop

def BigR (Q : RP) : Prop :=
  ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      Q R ⟨1, CF, large₂.sc.b⟩

def TwistPlacesOffPrimeQZero {D : D7} {T : Type} (L : LevCh D T) : Prop := ∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

def GridEx : Prop := BigR fun R sc => TwistPlacesOffPrimeQZero R.toLevCh →
  ∃ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R ∧ Nonempty (GridChoice W Set.univ)

def ConstEx : Prop := BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ B : Frames G,
  ∃ (rm : RealMatch W) (c : Fin D.R.m → Fin D.R.m → T → ℂ), rm.Over R ∧ ∀ i j t, IsSquareConst W B rm t i j (c i j t)

def LinB : Prop := BigR fun R sc => ∀ ch : Choice R, ch.sc = sc → ch.IsBase → ∀ a u, ConvK ch a u

def BaseEx : Prop := BigR fun R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ S₀ : GridChoice W Set.univ,
  ∃ M ρ ξ cv rm, ∃ S : SumChoice W Set.univ, ∃ rp n e c, S.toGridChoice = S₀ ∧
    (⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ : Choice R).IsBase

def IsEx : Prop := BigR fun R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ S₀ : GridChoice W Set.univ,
  ∃ M ρ ξ cv rm, ∃ S : SumChoice W Set.univ, ∃ rp n e c, S.toGridChoice = S₀ ∧
    (⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ : Choice R).Is

def InNF (Q : ∀ M : IntermediateField ℚ ℂ, (M →+* ℂ) → Prop) : Prop :=
  ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ Q M (algebraMap M ℂ)

section Clauses

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {K : Type} [Field K]
  (σ : K →+* ℂ) (S : GridChoice W Set.univ)

def RootCl : Prop := RootsIn σ 8 ∧ (∀ t, ∀ w ∈ locPl G t, RootsIn σ (Ideal.absNorm w.asIdeal ^ depthAt G w)) ∧
  ∀ w, (w ∈ S.PA ∨ ∃ t, w ∈ locPl G t) → ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ Set.range σ

def PhaseCl : Prop := ∀ t Φ, ∀ β ∈ S.supp t Φ, PhasesIn σ S t Φ β

def JetCl : Prop := ∀ t Φ, ∀ β ∈ S.supp t Φ, JetsIn σ S t Φ β

variable (W) in

def BotCl : Prop := ∀ i j : Fin D.R.m, ∃ (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X ∧ SumsIn W σ X

structure AllIn (μ₀ : T) : Prop where

  chars : CharsIn G σ

  root : RootCl σ S

  phase : PhaseCl σ S

  jet : JetCl σ S

  ratios : ∀ i j, LRatiosIn G σ μ₀ i j

  bot : BotCl W σ

variable {σ S} in

theorem AllIn.numbersIn {μ₀ : T} (h : AllIn σ S μ₀) : NumbersIn σ S μ₀ :=
  ⟨h.chars, h.root.1, h.root.2.1, h.phase, h.root.2.2, h.jet, h.ratios, fun i j _ => h.bot i j⟩

end Clauses

def NFChars : Prop := Big fun ch => InNF fun _ σ => CharsIn ch.G σ

def NFRoot : Prop := Big fun ch => InNF fun _ σ => RootCl σ ch.S.toGridChoice

def NFPhase : Prop := Big fun ch => InNF fun _ σ => PhaseCl σ ch.S.toGridChoice

def NFJet : Prop := Big fun ch => InNF fun _ σ => JetCl σ ch.S.toGridChoice

def NFRatio : Prop := Big fun {_} _ _ _ _ _ A _ _ _ _ _ ch => InNF fun _ σ => ∀ i j, LRatiosIn ch.G σ A.μ0 i j

def NFBot : Prop := Big fun ch => InNF fun _ σ => BotCl ch.W σ

def NFAll : Prop := Big fun {_} _ _ _ _ _ A _ _ _ _ _ ch => InNF fun _ σ => AllIn σ ch.S.toGridChoice A.μ0

section Agree

variable {X X' : Stages} {T T' : Type} {L : LevCh X.toD7 T} {L' : LevCh X'.toD7 T'}

structure LAgree (L : LevCh X.toD7 T) (L' : LevCh X'.toD7 T') (μ₀ : T) (μ₀' : T') (ι : T' → T) : Prop where

  pre : X'.B.toPre = X.B.toPre

  is : L.Is μ₀

  is' : L'.Is μ₀'

  C : ∃ (f : Fr X.B.toPre) (f' : Fr X'.B.toPre), HEq f' f ∧ L.C = Fr.at X f ∧ L'.C = Fr.at X' f'

  base : ι μ₀' = μ₀

  xi : ∀ t, HEq (L'.xiH t) (L.xiH (ι t))

  Q : ∀ t, HEq (L'.Q t) (L.Q (ι t))

  β : L.βX = 1 ∧ L'.βX = 1

variable {sc : GlobalTheory.ChiGrid.Consts}

structure GAgree (G : GridData L sc) (G' : GridData L' sc) : Prop where

  v0 : HEq G'.pl.v0 G.pl.v0

  w : HEq G'.pl.w G.pl.w

  chiH : HEq G'.ch.chiH G.ch.chiH

  chi : HEq G'.ch.chi G.ch.chi

  grid : ∀ i j, HEq (G'.V (.grid (i + 1) j)) (G.V (.grid (i + 1) j)) ∧ HEq (G'.Λ (.grid (i + 1) j)) (G.Λ (.grid (i + 1) j))

  top : ∀ j, HEq (G'.V (.top j)) (G.V (.top j)) ∧ HEq (G'.Λ (.top j)) (G.Λ (.top j))

  rowDec : ∀ j h h', HEq (G'.rowDec j h').ι (G.rowDec j h).ι ∧ HEq (G'.rowDec j h').a (G.rowDec j h).a

  topDec : HEq G'.sp.topDec.ι G.sp.topDec.ι ∧ HEq G'.sp.topDec.a G.sp.topDec.a

variable {G : GridData L sc} {G' : GridData L' sc}

def mapPair (ι : T' → T) : Pair T' → Pair T
  | .chi i j => .chi i j
  | .mu t i j => .mu (ι t) i j
  | .core i => .core i
  | .top t j => .top (ι t) j

structure WAgree (W : G.Weil) (W' : G'.Weil) (ι : T' → T) : Prop where

  ψ : HEq W'.ψ W.ψ

  θ : HEq W'.θ W.θ

  cart : ∀ Y, DefNode X'.toD7.R.m Y → HEq (W'.cart Y) (W.cart Y)

  om : ∀ p, DefPair X'.toD7.R.m p → HEq (W'.om p) (W.om (mapPair ι p))

variable {W : G.Weil} {W' : G'.Weil}

structure SAgree (S : GridChoice W Set.univ) (S' : GridChoice W' Set.univ) (ι : T' → T) : Prop where

  β : ∀ i j, HEq (S'.B.β (i + 1) j) (S.B.β (i + 1) j)

  βp : ∀ j, HEq (S'.βp j) (S.βp j)

  fr : ∀ Y, DefNode X'.toD7.R.m Y → HEq (S'.N.fr Y) (S.N.fr Y) ∧ HEq (S'.N.u Y).1 (S.N.u Y).1

  δ : S'.Z.δ = S.Z.δ

  vac : ∀ p, DefPair X'.toD7.R.m p → HEq (S'.Z.vac p) (S.Z.vac (mapPair ι p)) ∧ S'.Z.c0 p = S.Z.c0 (mapPair ι p)

  PA : HEq S'.PA S.PA

structure Agree (S : GridChoice W Set.univ) (S' : GridChoice W' Set.univ) (μ₀ : T) (μ₀' : T') (ι : T' → T) : Prop where

  l : LAgree L L' μ₀ μ₀' ι

  g : GAgree G G'

  w : WAgree W W' ι

  s : SAgree S S' ι

def FlipAgree (S : GridChoice W Set.univ) (S' : GridChoice W' Set.univ) (ι : T' → T) (Φ : G.Datum) (Φ' : G'.Datum) : Prop :=
  ∀ t w w', HEq w' w → w' ∈ locPl G' t → HEq (locGrid G' t w') (locGrid G (ι t) w) ∧
    HEq (givenLevel G' t w') (givenLevel G (ι t) w) ∧ HEq (Tflip W' S'.B t Φ' w') (Tflip W S.B (ι t) Φ w)

end Agree

abbrev AP := ∀ {X X' : Stages} {T T' : Type} {L : LevCh X.toD7 T} {L' : LevCh X'.toD7 T'} {sc : GlobalTheory.ChiGrid.Consts}
  {G : GridData L sc} {G' : GridData L' sc} {W : G.Weil} {W' : G'.Weil},
  GridChoice W Set.univ → GridChoice W' Set.univ → T → T' → (T' → T) → Prop

def OnAgree (Q : AP) : Prop := ∀ (X X' : Stages) (T T' : Type) (L : LevCh X.toD7 T) (L' : LevCh X'.toD7 T') (sc : GlobalTheory.ChiGrid.Consts)
  (G : GridData L sc) (G' : GridData L' sc) (W : G.Weil) (W' : G'.Weil) (S : GridChoice W Set.univ) (S' : GridChoice W' Set.univ)
  (μ₀ : T) (μ₀' : T') (ι : T' → T), Agree S S' μ₀ μ₀' ι → Q S S' μ₀ μ₀' ι

def TrFlip : Prop := OnAgree fun S S' _ _ ι => ∀ Φ', ∃ Φ, FlipAgree S S' ι Φ Φ'

def TrEasy : Prop := OnAgree fun {_ _ _ _ _ _ _} G G' _ _ S S' μ₀ μ₀' _ => ∀ (M : IntermediateField ℚ ℂ) (σ : M →+* ℂ),
  (CharsIn G σ → CharsIn G' σ) ∧ (RootCl σ S → RootCl σ S') ∧ ((∀ i j, LRatiosIn G σ μ₀ i j) → ∀ i j, LRatiosIn G' σ μ₀' i j)

def TrPhase : Prop := OnAgree fun S S' _ _ _ => ∀ (M : IntermediateField ℚ ℂ) (σ : M →+* ℂ), PhaseCl σ S → PhaseCl σ S'

def TrJet : Prop := OnAgree fun S S' _ _ _ => ∀ (M : IntermediateField ℚ ℂ) (σ : M →+* ℂ), JetCl σ S → JetCl σ S'

def TrBot : Prop := OnAgree fun {_ _ _ _ _ _ _ _ _} W W' _ _ _ _ _ => ∀ (M : IntermediateField ℚ ℂ) (σ : M →+* ℂ),
  BotCl W σ → BotCl W' σ

def CarryG : Prop := ∀ (X X' : Stages) (T T' : Type) (L : LevCh X.toD7 T) (L' : LevCh X'.toD7 T') (μ₀ : T) (μ₀' : T') (ι : T' → T),
  LAgree L L' μ₀ μ₀' ι → ∀ (sc : GlobalTheory.ChiGrid.Consts) (G : GridData L sc), ∃ G' : GridData L' sc, GAgree G G'

def CarryW : Prop := ∀ (X X' : Stages) (T T' : Type) (L : LevCh X.toD7 T) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 : Type)
  (A : FamIn X'.toD7.what₂.LL Γ Pl0 T' X'.toD7.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks X'.toD7.what₂.LL]
  (R : RealDat X'.toD7 A Ks) (μ₀ : T) (ι : T' → T), LAgree L R.toLevCh μ₀ A.μ0 ι → R.IsChain → R.IsModels →
  ∀ (sc : GlobalTheory.ChiGrid.Consts) (G : GridData L sc) (G' : GridData R.toLevCh sc), GAgree G G' → ∀ W : G.Weil,
    ∃ W' : G'.Weil, W'.Over R ∧ WAgree W W' ι

def CarryS : Prop := ∀ (X X' : Stages) (T T' : Type) (L : LevCh X.toD7 T) (L' : LevCh X'.toD7 T') (μ₀ : T) (μ₀' : T') (ι : T' → T),
  LAgree L L' μ₀ μ₀' ι → ∀ (sc : GlobalTheory.ChiGrid.Consts) (G : GridData L sc) (G' : GridData L' sc), GAgree G G' →
  ∀ (W : G.Weil) (W' : G'.Weil), WAgree W W' ι → ∀ S : GridChoice W Set.univ, ∃ S' : GridChoice W' Set.univ, SAgree S S' ι

abbrev Key (P : Pre) : Type := Set (HChar P.host.E × Finset (HeightOneSpectrum (𝓞 P.host.E)))

def keyOf {X : Stages} {T : Type} (L : LevCh X.toD7 T) : Key X.B.toPre := Set.range fun t => (L.xiH t, L.Q t)

def KeyFin : Prop := ∀ (P : Pre) (Ξ : Set (HChar P.host.E)), Ξ.Finite → ∃ 𝒦 : Set (Key P), 𝒦.Finite ∧
  ∀ (X : Stages) (T : Type) (L : LevCh X.toD7 T) (μ₀ : T), X.B.toPre = P → L.Is μ₀ → (∀ t, ∃ ξ ∈ Ξ, HEq (L.xiH t) ξ) →
    ∃ κ ∈ 𝒦, HEq (keyOf L) κ

def FieldFor (s : Scale) (CF : ℝ) (P : Pre) (f : Fr P) (c : ∀ (X : Stages) (T : Type), LevCh X.toD7 T → Prop) : Prop :=
  ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (X : Stages) (f' : Fr X.B.toPre), X.B.toPre = P → HEq f' f →
    ∀ large₂ : SizeData₂ X.toD7, large₂.sc = s → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type)
      (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL]
      (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F → R.C = Fr.at X f' → TwistPlacesOffPrimeQZero R.toLevCh → c X T R.toLevCh →
      (∀ z ∈ S, z ∈ Set.range X.toD7.what₂.embLL) → ∃ ch : Choice R, ch.Is ∧ ch.AtScale CF s.b ∧ ch.FieldOK

def ExKey : Prop := ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ s : Scale, s.eps = ε → x₀ ≤ s.x →
  ∀ (P : Pre) (f : Fr P) (κ : Key P), FieldFor s CF P f fun _ _ L => HEq (keyOf L) κ

def ExField : Prop := ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ s : Scale, s.eps = ε → x₀ ≤ s.x →
  ∀ (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)), Ξ.Finite → FieldFor s CF P f fun _ _ L => ∀ t, ∃ ξ ∈ Ξ, HEq (L.xiH t) ξ

end GlobalTheory.RowEx

end
