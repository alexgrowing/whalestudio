import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HaarOrderData
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.WeilBound.CoreStatements.TorusUniformisation.RepresentationHypotheses.HostNumDef

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.RT

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def edgeOf : Arrow T → GlobalTheory.SplitFlip.Edge
  | .right i j => .ex i j
  | .down _ i j => .theta i j
  | _ => .ex 0 0

def GridArrow (t : T) (m : ℕ) : Arrow T → Prop
  | .right i j => i < m ∧ j ≤ m
  | .down t' i j => t' = t ∧ i ≤ m ∧ j < m
  | _ => False

def IsGridPath (t : T) (m : ℕ) {X Y : Node} (p : Path T X Y) : Prop := ∀ a ∈ p.arrows, GridArrow t m a

def edges {X Y : Node} (p : Path T X Y) : List GlobalTheory.SplitFlip.Edge := p.arrows.map edgeOf

noncomputable def famOf {S : Arrow T → Type} (x : ∀ a, S a) {X : Node} : ∀ {Y : Node} (p : Path T X Y), p.Fam S
  | _, .nil => ()
  | _, .snoc a p => (famOf x p, x a)

noncomputable def famProd (x : ∀ a : Arrow T, WO (G.pS a.pair) (G.pT a.pair)) {X : Node} :
    ∀ {Y : Node} {p : Path T X Y}, PureT G p → ℂ
  | _, .nil, _ => 1
  | _, .snoc a _, d => famProd x d.1 * d.2 (x a)

variable (G) in

abbrev PolAll : Type := ∀ b : GlobalTheory.SplitFlip.Edge,
  PolF D (G.V (.grid b.src.1 b.src.2)).rank (G.V (.grid b.tgt.1 b.tgt.2)).rank

def polOn (P : PolAll G) : ∀ a : Arrow T, PolF D (G.pT a.pair).rank (G.pS a.pair).rank
  | .right i j => P (.ex i j)
  | .down _ i j => P (.theta i j)
  | .coreUp _ => 0
  | .coreDown _ => 0
  | .col _ _ => 0

def totOn (W : G.Weil) {X Y : Node} (p : Path T X Y) (r : PolAll G →₀ ℂ) (τ : TotT G p) : TotT G p :=
  tensT W (r.mapDomain fun P => famOf (polOn P) p) τ

def vacA {W : G.Weil} (ρ : RealMatch W) : ∀ a : Arrow T, Sch G a
  | .right i j => ρ.vX i j
  | .down _ i j => ρ.vT i j
  | .coreUp _ => 0
  | .coreDown _ => 0
  | .col _ _ => 0

def locArgs (B : Frames G) (t : T) (w : Pl D.host.E) (x : ∀ a : Arrow T, WO (G.pS a.pair) (G.pT a.pair)) :
    (locGrid G t w).Args
  | .theta i j => if h : i ≤ D.R.m ∧ j < D.R.m then B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨h.1, h.2⟩ ⟨h.1, h.2.le⟩
      (Matrix.map (x (.down t i j)) fun a => cpt w (toEAf D a)) else 0
  | .ex i j => if h : i < D.R.m ∧ j ≤ D.R.m then B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨h.1.le, h.2⟩ ⟨h.1, h.2⟩
      (Matrix.map (x (.right i j)) fun a => cpt w (toEAf D a)) else 0

def HasTens {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (e : AE D) {X Y : Node} (p : Path T X Y) (τ : TotT G p)
    (S : ∀ w, (locGrid G t w).Args → ℂ) : Prop :=
  ∃ φ : PureT G p → PureT G p,
    (∀ d ∈ τ.support, Path.Fam.All (S := fun a => Sch G a × Sch G a) (fun a q => IsLocVec W a.pair e (vacA ρ a) q.1 q.2)
      (Path.Fam.zip (S'' := fun a => Sch G a × Sch G a) (fun _ u v => (u, v)) (φ d) d)) ∧
    ∀ x : ∀ a : Arrow T, WO (G.pS a.pair) (G.pT a.pair), (∀ a, IsHalf e (x a)) →
      (τ.sum fun d c => c * famProd x (φ d)) = ∏ w ∈ locPl G t, S w (locArgs B t w x)

def LocTens (t : T) (γ : List GlobalTheory.SplitFlip.Edge) (S : ∀ w, (locGrid G t w).Args → ℂ) : Prop :=
  ∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) γ (S w)

def flipS (W : G.Weil) (t : T) (i j : ℕ) (S : ∀ w, (locGrid G t w).Args → ℂ) : ∀ w, (locGrid G t w).Args → ℂ := fun w =>
  (locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (S w)

def RealFlip {W : G.Weil} (ρ : RealMatch W) (i j : ℕ) (r r' : PolAll G →₀ ℂ) : Prop :=
  ∃ a : PolAll G → ((Unit × PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid (i + 1) (j + 1))).rank) ×
      PolF D (G.V (.grid (i + 1) (j + 1))).rank (G.V (.grid (i + 1) j)).rank →₀ ℂ),
    (∀ P, (toTens (a P), P (.theta i j) ⊗ₜ[ℂ] P (.ex i j)) ∈ ρ.rel i j) ∧
    r' = r.sum fun P c => c • (a P).mapDomain fun d =>
      Function.update (Function.update P (.ex i (j + 1)) d.1.2) (.theta (i + 1) j) d.2

def valSpan (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Submodule ℂ (GA D V → ℂ) :=
  Submodule.span ℂ {φ | ∃ F ∈ MultT θ M ∅ 1, ∃ v : SmT M, φ = F v}

def IsVal (W : G.Weil) (i j : ℕ) (F : Fn G (.grid i j)) : Prop :=
  ∃ M : DSModel (G.V (.grid i j)) fun τ => dualPar (parV D sc.cGap i j τ), F ∈ valSpan W.θ M

def IsFockVec (W : G.Weil) (a : Arrow T) (f : Sch G a) : Prop :=
  ∃ f₀ P, IsThetaFunO W.ψ (G.pS a.pair) (G.pT a.pair) f₀ ∧
    (∀ τ, IsFockVacAt (heisO W.ψ (G.pS a.pair) (G.pT a.pair)) W.θ τ
      (cplxO (G.cartS W.cart a.pair τ) (G.onT W.cart a.pair τ)) f₀) ∧ f = W.fock a.pair f₀ P

def ValLifts (W : G.Weil) : Prop :=
  ∀ M : Vol G, (∀ i j, i < D.R.m → j ≤ D.R.m → (M.ν (.grid i j)).IsHaarMeasure →
      IsFundamentalDomain (GQ (G.V (.grid i j))) (M.fd (.grid i j)) (M.ν (.grid i j)) →
      ∀ f F, IsFockVec W (.right i j) f → IsVal W i j F →
        LiftConv W M (.right i j) f F ∧ IsVal W (i + 1) j (liftA W M (.right i j) f F)) ∧
    ∀ t i j, i ≤ D.R.m → j < D.R.m → (M.ν (.grid i (j + 1))).IsHaarMeasure →
      IsFundamentalDomain (GQ (G.V (.grid i (j + 1)))) (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) →
      ∀ f F, IsFockVec W (.down t i j) f → IsVal W i (j + 1) F →
        LiftConv W M (.down t i j) f F ∧ IsVal W i j (liftA W M (.down t i j) f F)

section Square

variable (W : G.Weil) (B : Frames G) (ρ : RealMatch W)

def SqRel (t : T) (i j : Fin D.R.m) (c : ℂ) (a : PolT G (routeBig t i j) →₀ ℂ) (b : PolT G (routeSmall t i j) →₀ ℂ) : Prop :=
  ∀ M : Vol G, M.Is t → ∀ τ τ' n Φ, (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ GlobalTheory.SplitFlip.IsNatDatum (unifAt w) (n w) (Φ w)) →
    HasFlip B t ρ i j n Φ τ τ' → ∀ z g g₁, SquareConv W M (tensT W a τ) (tensT W b τ') z g g₁ →
      zdeg z * ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ =
        c * ∫ u in M.fd _, translates z (kerSmall W (tensT W b τ') g g₁) u ∂M.ν _

def SqFactor (i j : Fin D.R.m) (lam : T → ℂ) : Prop :=
  (∀ t, lam t ≠ 0) ∧ ∃ (Pi : ModuleCat.{0} ℂ)
    (p : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ] Pi)
    (p' : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j) →ₗ[ℂ] Pi),
    Nontrivial Pi ∧ Function.Surjective p ∧ Function.Surjective p' ∧
      ∀ t c a b, SqRel W B ρ t i j c a b ↔ lam t • p (toTens a) = c • p' (toTens b)

end Square

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri) in

def FactorZ {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (lam : T → ℂ) : Prop :=
  (∀ t, lam t ≠ 0) ∧ ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi) (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi)
    (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))),
    Nontrivial Pi ∧ Function.Surjective p ∧ Function.Surjective p' ∧ (∀ t, Function.Injective (J t)) ∧
    (∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) ∧ (∀ t P, X.I ψ θ t P = lam t • J t (p P)) ∧
    (∀ t P' z h, IntegrableOn (translates z (X.ker' ψ θ t P' h)) X.fd' X.m' →
      ∫ g in X.fd', translates z (X.ker' ψ θ t P' h) g ∂X.m' = zdeg z * J t (p' P') h) ∧
    ∀ t P' h, ∃ z, zdeg z ≠ 0 ∧ IntegrableOn (translates z (X.ker' ψ θ t P' h)) X.fd' X.m'

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri) in

def IsStage (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) : Prop :=
  p ≤ (D.R.m - (j + 1)) / 2 ∧ q ≤ (D.R.m - j) / 2 ∧
    A.rank + 2 * ((D.R.m - (j + 1)) / 2) = rankV D (i + 1) (j + 1) + 2 * p ∧
    A'.rank + 2 * ((D.R.m - j) / 2) = rankV D i j + 2 * q ∧
    GlobalTheory.ConstRatio.NegIdx A p ∧ GlobalTheory.ConstRatio.NegIdx A' q ∧ GlobalTheory.ConstRatio.NegIdx WW (p + q) ∧
    X.Is W.ψ W.θ (fun t => L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))
      (fun _ => G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (fun t => SqNum.nuH G t i j) (locPl G)

def onCorner (φ : GA D D.sp.X' → ℂ) : Fn G (.grid 0 D.R.m) :=
  fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m L)) g)

structure Std (W : G.Weil) (μ₀ : T) : Prop where

  lev : L.Is μ₀

  size : GlobalTheory.IndefiniteRowSideFullHecke.HaarEquallySpacedConditions.SizeOK D

  host : PositivityTheory.HostN.HostNum D

  cc : D.host.ccK = ⊤

  rk : 2 * D.R.m + 1 < D.R.r

  split : ∀ p ∈ D.host.levelPrimes, D.host.cls p = .splitK

  pdeE : (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧
    (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E

namespace Std

variable {W : G.Weil} {μ₀ : T}

end Std

abbrev PropG : Type 1 := ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}, G.Weil → T → Prop

def AllG (Q : PropG) : Prop :=
  ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (W : G.Weil) (μ₀ : T), Std W μ₀ → Q W μ₀

def ValSt : Prop := AllG fun W _ => ValLifts W

def TripleG : Prop := AllG fun {D} _ _ _ _ W _ => ∀ t (i j : Fin D.R.m), SquareTriple W t i j

def SqFacSt : Prop := AllG fun {_} _ _ _ G W _ => ∀ (B : Frames G) (ρ : RealMatch W) i j, ∃ lam, SqFactor W B ρ i j lam

def OneFlip : Prop := AllG fun {D} _ _ _ G W _ => ∀ (B : Frames G) (ρ : RealMatch W) t (i j : Fin D.R.m) (c : ℂ),
  IsSquareConst W B ρ t i j c → ∀ (p₁ : Path _ (.grid 0 D.R.m) (.grid i (j + 1))) (p₂ : Path _ (.grid (i + 1) j) (.grid D.R.m 0)),
    IsGridPath t D.R.m p₁ → IsGridPath t D.R.m p₂ → ∀ e, IsIdemSum e (locPl G t) → ∀ M : Vol G, M.Is t →
    ∀ S, LocTens t (edges ((p₁.comp (routeSmall t i j)).comp p₂)) S → ∀ r r', RealFlip ρ i j r r' → ∀ τ τ',
      HasTens B ρ t e ((p₁.comp (routeSmall t i j)).comp p₂) τ S →
      HasTens B ρ t e ((p₁.comp (routeBig t i j)).comp p₂) τ' (flipS W t i j S) → ∀ F, IsVal W 0 D.R.m F →
        liftT W M _ (totOn W _ r' τ') F = c • liftT W M _ (totOn W _ r τ) F

def FlipG : Prop := AllG fun {D} T _ _ G W _ => ∀ (B : Frames G) (ρ : RealMatch W) (c : Fin D.R.m → Fin D.R.m → T → ℂ),
  (∀ i j t, IsSquareConst W B ρ t i j (c i j t)) → ∀ r, ∃ r', ∀ t Φ e, IsIdemSum e (locPl G t) → ∀ M : Vol G, M.Is t → ∀ τ τ',
    HasTens B ρ t e (givenPath t D.R.m) τ (fun w => (givenStage t w B Φ).tensor) →
    HasTens B ρ t e (oppPath t D.R.m) τ' (Tflip W B t Φ) → ∀ F, IsVal W 0 D.R.m F →
      liftT W M _ (totOn W _ r' τ') F = (∏ i, ∏ j, c i j t) • liftT W M _ (totOn W _ r τ) F

variable (G) in

def SqField {K : Type} [Field K] (σ : K →+* ℂ) : Prop :=
  CharsIn G σ ∧ RootsIn σ 8 ∧ ∀ t, ∀ w ∈ locPl G t, RootsIn σ (Ideal.absNorm w.asIdeal ^ depthAt G w) ∧
    ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ Set.range σ

section Tower

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

def FacZSt : Prop := AllG fun {D} T _ _ _ W _ => ∀ (i j : Fin D.R.m) p q (A A' WW : HSp D) (X : Tri T A A' WW),
  IsStage W i j p q X → ∃ lam, FactorZ X W.ψ W.θ lam

def StepSmall : Prop := AllG fun {D} T _ _ G W _ => ∀ (K : Type) [Field K] (σ : K →+* ℂ), SqField G σ →
  ∀ (i j : Fin D.R.m) p q (A A' WW : HSp D) (X : Tri T A A' WW) lam (e : ℕ) (Λ : T → ℂ → ℂ), IsStage W i j p (q + 1) X →
    FactorZ X W.ψ W.θ lam → A.rank = A'.rank + 2 * e → (∀ t, GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G t i j) (Λ t)) →
    ∃ (B B' W₁ : HSp D) (Y : Tri T B B' W₁) (lam₁ : T → ℂ), IsStage W i j p q Y ∧ FactorZ Y W.ψ W.θ lam₁ ∧
      ∀ t, ∃ y : Kˣ, lam t * Λ t ((e + 1 : ℕ) : ℂ) = σ y * lam₁ t

def StepBig : Prop := AllG fun {D} T _ _ G W _ => ∀ (K : Type) [Field K] (σ : K →+* ℂ), SqField G σ →
  ∀ (i j : Fin D.R.m) p (A A' WW : HSp D) (X : Tri T A A' WW) lam (e : ℕ) (Λ : T → ℂ → ℂ), IsStage W i j (p + 1) 0 X →
    FactorZ X W.ψ W.θ lam → A.rank = A'.rank + 2 * e → (∀ t, GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G t i j) (Λ t)) →
    ∃ (B B' W₁ : HSp D) (Y : Tri T B B' W₁) (lam₁ : T → ℂ), IsStage W i j p 0 Y ∧ FactorZ Y W.ψ W.θ lam₁ ∧
      ∀ t, ∃ y : Kˣ, lam t = σ y * Λ t (e : ℂ) * lam₁ t

def StageCmp : Prop := AllG fun {D} T _ _ G W _ => ∀ (K : Type) [Field K] (σ : K →+* ℂ), SqField G σ →
  ∀ (i j : Fin D.R.m) p q (A A' WW : HSp D) (X : Tri T A A' WW) (B B' W₁ : HSp D) (Y : Tri T B B' W₁) lam lam',
    IsStage W i j p q X → IsStage W i j p q Y → FactorZ X W.ψ W.θ lam → FactorZ Y W.ψ W.θ lam' →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ t, ∃ y : Kˣ, lam' t = κ * σ y * lam t

def StageRat : Prop := AllG fun {D} T _ _ G W μ₀ => ∀ (K : Type) [Field K] (σ : K →+* ℂ), SqField G σ →
  ∀ i j : Fin D.R.m, LRatiosIn G σ μ₀ i j → BottomIn W σ i j → ∀ p q (A A' WW : HSp D) (X : Tri T A A' WW) lam,
    IsStage W i j p q X → FactorZ X W.ψ W.θ lam → GlobalTheory.ConstRatio.RatIn σ μ₀ lam

def TopLink : Prop := AllG fun {D} T _ _ G W _ => ∀ (K : Type) [Field K] (σ : K →+* ℂ), SqField G σ →
  ∀ (B : Frames G) (ρ : RealMatch W) (i j : Fin D.R.m) lam, SqFactor W B ρ i j lam →
    ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (lam' : T → ℂ), IsStage W i j ((D.R.m - (j + 1)) / 2) ((D.R.m - j) / 2) X ∧
      FactorZ X W.ψ W.θ lam' ∧ ∀ t, ∃ y : Kˣ, lam t = σ y * lam' t

end Tower

end GlobalTheory.CompanionTheory.Ar.RT

end
