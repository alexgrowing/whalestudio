import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.StdFrames
open scoped TensorProduct

namespace GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

def edgeOf : Arrow T → GlobalTheory.SplitFlip.Edge
  | .right i j => .ex i j
  | .down _ i j => .theta i j
  | _ => .ex 0 0

def IsGridArrow (m : ℕ) (t : T) (a : Arrow T) : Prop :=
  (∃ i j, i < m ∧ j ≤ m ∧ a = .right i j) ∨ ∃ i j, i ≤ m ∧ j < m ∧ a = .down t i j

variable {X Y : Node}

def OnGrid (m : ℕ) (t : T) (p : Path T X Y) : Prop := ∀ a ∈ p.arrows, IsGridArrow m t a

def edges (p : Path T X Y) : List GlobalTheory.SplitFlip.Edge := p.arrows.map edgeOf

section Grid

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def vacOf {W : G.Weil} (ρ : RealMatch W) : ∀ a : Arrow T, Sch G a
  | .right i j => ρ.vX i j
  | .down _ i j => ρ.vT i j
  | _ => 0

def locArg (B : Frames G) (t : T) (w : Pl D.host.E) : ∀ a : Arrow T, WO (G.pS a.pair) (G.pT a.pair) →
    Matrix (Fin ((locGrid G t w).rank (edgeOf a).tgt)) (Fin ((locGrid G t w).rank (edgeOf a).src)) (Kw w)
  | .right i j, x => if h : i < D.R.m ∧ j ≤ D.R.m then
      B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨h.1.le, h.2⟩ ⟨h.1, h.2⟩ (x.map fun c => cpt w (toEAf D c)) else 0
  | .down _ i j, x => if h : i ≤ D.R.m ∧ j < D.R.m then
      B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨h.1, h.2⟩ ⟨h.1, h.2.le⟩ (x.map fun c => cpt w (toEAf D c)) else 0
  | .coreUp _, _ => 0
  | .coreDown _, _ => 0
  | .col _ _, _ => 0

abbrev ArgT (G : GridData L sc) (p : Path T X Y) : Type := p.Fam fun a => WO (G.pS a.pair) (G.pT a.pair)

def castArg {t : T} {w : Pl D.host.E} {e₁ e₂ : GlobalTheory.SplitFlip.Edge} (h : e₁ = e₂)
    (y : Matrix (Fin ((locGrid G t w).rank e₁.tgt)) (Fin ((locGrid G t w).rank e₁.src)) (Kw w)) :
    Matrix (Fin ((locGrid G t w).rank e₂.tgt)) (Fin ((locGrid G t w).rank e₂.src)) (Kw w) := h ▸ y

def argAt (B : Frames G) (t : T) (w : Pl D.host.E) (a : Arrow T) (x : WO (G.pS a.pair) (G.pT a.pair)) (e : GlobalTheory.SplitFlip.Edge)
    (d : Matrix (Fin ((locGrid G t w).rank e.tgt)) (Fin ((locGrid G t w).rank e.src)) (Kw w)) :
    Matrix (Fin ((locGrid G t w).rank e.tgt)) (Fin ((locGrid G t w).rank e.src)) (Kw w) :=
  if h : edgeOf a = e then castArg h (locArg B t w a x) else d

noncomputable def pathArgs (B : Frames G) (t : T) (w : Pl D.host.E) : ∀ {Y : Node} (p : Path T X Y), ArgT G p → (locGrid G t w).Args
  | _, .nil, _ => 0
  | _, .snoc a p, x => fun e => argAt B t w a x.2 e (pathArgs B t w p x.1 e)

noncomputable def famProd : ∀ {Y : Node} (p : Path T X Y), PureT G p → ArgT G p → ℂ
  | _, .nil, _, _ => 1
  | _, .snoc _ p, d, x => famProd p d.1 x.1 * d.2 x.2

noncomputable def HalfAll (e : AE D) : ∀ {Y : Node} (p : Path T X Y), ArgT G p → Prop
  | _, .nil, _ => True
  | _, .snoc _ p, x => HalfAll e p x.1 ∧ IsHalf e x.2

noncomputable def VecAll {W : G.Weil} (ρ : RealMatch W) (e : AE D) : ∀ {Y : Node} (p : Path T X Y), PureT G p → PureT G p → Prop
  | _, .nil, _, _ => True
  | _, .snoc a p, φ, f => VecAll ρ e p φ.1 f.1 ∧ IsLocVec W a.pair e (vacOf ρ a) φ.2 f.2

def RepFin {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (p : Path T X Y) (τ : TotT G p)
    (Tl : ∀ w, (locGrid G t w).Args → ℂ) : Prop :=
  ∃ e, IsIdemSum e (locPl G t) ∧ ∃ φ : PureT G p → PureT G p, (∀ d ∈ τ.support, VecAll ρ e p (φ d) d) ∧
    ∀ x : ArgT G p, HalfAll e p x → (τ.sum fun d c => c * famProd p (φ d) x) = ∏ w ∈ locPl G t, Tl w (pathArgs B t w p x)

variable (G) in

abbrev PolE : Type := ∀ e : GlobalTheory.SplitFlip.Edge, PolF D (G.V (.grid e.src.1 e.src.2)).rank (G.V (.grid e.tgt.1 e.tgt.2)).rank

def polOf (P : PolE G) : ∀ a : Arrow T, PolF D (G.pT a.pair).rank (G.pS a.pair).rank
  | .right i j => P (.ex i j)
  | .down _ i j => P (.theta i j)
  | .coreUp _ => 0
  | .coreDown _ => 0
  | .col _ _ => 0

noncomputable def restrictPol (P : PolE G) : ∀ {Y : Node} (p : Path T X Y), PolT G p
  | _, .nil => ()
  | _, .snoc a p => (restrictPol P p, polOf P a)

def tensE (W : G.Weil) (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ : TotT G p) : TotT G p :=
  tensT W (Q.mapDomain fun P => restrictPol P p) τ

def toOpp (P : PolE G) : GlobalTheory.RowClaim.PolRow G × GlobalTheory.RowClaim.PolDown G :=
  (fun i => P (.ex i D.R.m), fun j => P (.theta D.R.m j))

end Grid

end GlobalTheory.FlipRun

namespace GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.ChiGrid GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem range_snd_rel (ρ : RealMatch W) (i j : ℕ) :
    LinearMap.range ((LinearMap.snd ℂ _ _).comp (ρ.rel i j).subtype) = ⊤ := by
  refine LinearMap.range_eq_top.2 fun b => ?_
  obtain ⟨a, h⟩ := ρ.onto_small i j b
  exact ⟨⟨(a, b), h⟩, rfl⟩

def matchLin (ρ : RealMatch W) (i j : ℕ) : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j) →ₗ[ℂ]
    PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) :=
  (LinearMap.fst ℂ _ _).comp ((ρ.rel i j).subtype.comp
    (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose)

theorem matchLin_mem (ρ : RealMatch W) (i j : ℕ) (b : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)) :
    (matchLin ρ i j b, b) ∈ ρ.rel i j := by
  have h := LinearMap.congr_fun (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose_spec b
  set g := (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose
  have e : ((g b : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j))) = (matchLin ρ i j b, b) :=
    Prod.ext rfl h
  exact e ▸ (g b).2

def flipPol (ρ : RealMatch W) (i j : ℕ) (P : PolE G) : PolE G →₀ ℂ :=
  (toTens_surjective (matchLin ρ i j (P (.theta i j) ⊗ₜ P (.ex i j)))).choose.sum fun q c =>
    Finsupp.single (Function.update (Function.update P (.ex i (j + 1)) q.1.2) (.theta (i + 1) j) q.2) c

def flipPolE (ρ : RealMatch W) (i j : ℕ) (Q : PolE G →₀ ℂ) : PolE G →₀ ℂ := Q.sum fun P c => c • flipPol ρ i j P

def flipsPolE (ρ : RealMatch W) (l : List (ℕ × ℕ)) (Q : PolE G →₀ ℂ) : PolE G →₀ ℂ :=
  l.foldl (fun Q x => flipPolE ρ x.1 x.2 Q) Q

def IsCuspListed (θ : InfFam D) (X : Node) (F : Fn G X) : Prop :=
  IsAutFunSm θ (G.V X) F ∧ IsCuspFun (G.V X) F ∧ G.IsListed θ X F

def CuspStep (W : G.Weil) (M : Vol G) (ρ : RealMatch W) (t : T) : Prop :=
  ∀ a : Arrow T, IsGridArrow D.R.m t a → ∀ e, IsIdemSum e (locPl G t) → ∀ φ f, IsLocVec W a.pair e (vacOf ρ a) φ f →
    ∀ (Q : PolF D (G.pT a.pair).rank (G.pS a.pair).rank) (F : Fn G a.src), IsCuspListed W.θ a.src F →
      LiftConv W M a (W.fock a.pair f Q) F ∧ IsCuspListed W.θ a.tgt (liftA W M a (W.fock a.pair f Q) F)

end GlobalTheory.FlipRun
