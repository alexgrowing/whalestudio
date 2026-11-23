import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus)

namespace GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

def xiVals (L : LevCh D T) (t : T) : Subgroup ℂˣ := Subgroup.closure {z | ∃ w x, z = (L.xiH t).loc w x}

section Grid

variable {L : LevCh D T} {sc : Consts} (G : GridData L sc)

abbrev PolRow : Type := ∀ i : Fin D.R.m, PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank

abbrev PolDown : Type := ∀ j : Fin D.R.m, PolF D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank

abbrev PolCol : Type := ∀ j : Fin D.R.m, PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank

abbrev SchRow : Type := ∀ i : Fin D.R.m, Sch G (.right i D.R.m)

abbrev SchDown (t : T) : Type := ∀ j : Fin D.R.m, Sch G (.down t D.R.m j)

noncomputable def colPath (t : T) : ∀ n, Path T (.top 0) (.top n)
  | 0 => .nil
  | n + 1 => .snoc (.col t n) (colPath t n)

noncomputable def colFam {S : Arrow T → Type} (t : T) : ∀ n, (∀ j : Fin n, S (.col t j)) → (colPath t n).Fam S
  | 0, _ => ()
  | n + 1, f => (colFam t n fun j => f j.castSucc, f (Fin.last n))

variable {G} (W : G.Weil) (t : T)

def oppPure (P : PolRow G × PolDown G) (d : SchRow G × SchDown G t) : PureT G (oppPath t D.R.m) :=
  Path.Fam.append (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (d.1 i) (P.1 i))
    (downFam t D.R.m D.R.m fun j => W.fock (.mu t D.R.m j) (d.2 j) (P.2 j))

def oppTens (τi : PolRow G × PolDown G →₀ ℂ) (τf : SchRow G × SchDown G t →₀ ℂ) : TotT G (oppPath t D.R.m) :=
  τi.sum fun P c => τf.sum fun d c' => Finsupp.single (oppPure W t P d) (c * c')

variable {W}

def oppArgs (B : Frames G) (w : Pl D.host.E)
    (x : ∀ i : Fin D.R.m, Mx D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank)
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) : (locGrid G t w).Args
  | .ex i j => if h : i < D.R.m ∧ j = D.R.m then
      (B.coord t w (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨h.1.le, le_rfl⟩ ⟨h.1, le_rfl⟩
        ((x ⟨i, h.1⟩).map fun a => cpt w (toEAf D a))).submatrix (Fin.cast (by rw [h.2])) (Fin.cast (by rw [h.2])) else 0
  | .theta i j => if h : j < D.R.m ∧ i = D.R.m then
      (B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, h.1⟩ ⟨le_rfl, h.1.le⟩
        ((y ⟨j, h.1⟩).map fun a => cpt w (toEAf D a))).submatrix (Fin.cast (by rw [h.2])) (Fin.cast (by rw [h.2])) else 0

def IsFlipFin (B : Frames G) (ρ : RealMatch W) (Φ : G.Datum) (τ : SchRow G × SchDown G t →₀ ℂ) : Prop :=
  ∃ e, IsIdemSum e (locPl G t) ∧ ∃ φ : SchRow G × SchDown G t → SchRow G × SchDown G t,
    (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧
      ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) ((φ d).2 j) (d.2 j)) ∧
    ∀ x y, (∀ i, IsHalf e (x i)) → (∀ j, IsHalf e (y j)) →
      (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) =
        ∏ w ∈ locPl G t, Tflip W B t Φ w (oppArgs t B w x y)

variable {U : Set T} (S : GridChoice W U)

def movedVec {p : Pair T} (d : FinDatum G t p) : WO (G.pS p) (G.pT p) → ℂ :=
  W.om p (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1) (S.Z.vec d)

def defPer (M : Vol G) (P : PolCol G × PolRow G) (d : PureDat G t) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) : ℂ :=
  ∫ h in M.fd (.grid D.R.m D.R.m),
    liftP W M (colPath t D.R.m) (colFam t D.R.m fun j => W.fock (.top t j) (movedVec t S (d.1 j)) (P.1 j)) φ (stabilizerEmbedding G.sp.topDec h) *
      liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (movedVec t S (d.2 i)) (P.2 i)) F h
    ∂M.ν (.grid D.R.m D.R.m)

def IsTermVol (Φ : G.Datum) (β : CosFam G t) (M : Vol G) : Prop :=
  (∀ j (h : j < D.R.m), M.IsAt (.top j) (S.levTop t Φ β j h)) ∧ ∀ i (h : i ≤ D.R.m), M.IsAt (.grid i D.R.m) (S.levRow t i h)

def defTot (M : Vol G) (τi : PolCol G × PolRow G →₀ ℂ) (τ : PureDat G t →₀ ℂ) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) : ℂ :=
  τi.sum fun P c => τ.sum fun d c' => c * c' * defPer t S M P d φ F

end Grid

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def formTop (t : T) (y : (R.HX t).H) : Fn ch.G (.grid 0 D.R.m) := fun g =>
  ch.cv.formX t y (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) g)

def colFn (a : Fin ch.n) : Fn ch.G (.top 0) := pairVec (coefPlus ch.G ch.W.θ) ch.ξ (ch.col a)

def ProjAt : Prop := ∀ t (x : A.fam.amb.FR t), x ∈ (A.fam.R t).goodF A.fam.X →
  R.e0 (ch.cv.lift t (R.jX t x)) = ch.cv.lift t (R.jX t x)

def FlipAt : Prop :=
  ∃ (τi : PolRow ch.G × PolDown ch.G →₀ ℂ) (z : T → ℂˣ), ∀ t, z t ∈ xiVals R.toLevCh t ∧ ∀ Φ,
    ∃ τ, IsFlipFin t ch.S.B ch.rm Φ τ ∧ ∀ M : Vol ch.G, M.Is t → ∀ y,
      TotConv ch.W M (oppPath t D.R.m) (oppTens ch.W t τi τ) (formTop ch t y) ∧
      thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) =
        ((z t : ℂ) * cTot ch t)⁻¹ • liftT ch.W M (oppPath t D.R.m) (oppTens ch.W t τi τ) (formTop ch t y)

def UnfoldAt : Prop :=
  ∀ τi : PolRow ch.G × PolDown ch.G →₀ ℂ, ∃ (σ : PolCol ch.G × PolRow ch.G →₀ ℂ) (z : T → ℂˣ), ∀ t, z t ∈ xiVals R.toLevCh t ∧
    ∀ a τ, IsFlipFin t ch.S.B ch.rm (ch.Phi a) τ → ∀ M : Vol ch.G, M.Is t →
      ∀ (Mβ : CosFam ch.G t → Vol ch.G) (τβ : CosFam ch.G t → PureDat ch.G t →₀ ℂ),
        (∀ β ∈ ch.S.supp t (ch.Phi a), IsTermVol t ch.S.toGridChoice (ch.Phi a) β (Mβ β) ∧ ch.S.IsExpansion t (ch.Phi a) β (τβ β)) →
        ∀ y, Bplus ch.W ch.M (colFn ch a) (liftT ch.W M (oppPath t D.R.m) (oppTens ch.W t τi τ) (formTop ch t y)) =
          (z t : ℂ)⁻¹ * ch.S.sAA * ∑ᶠ β ∈ ch.S.supp t (ch.Phi a), (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
            defTot t ch.S.toGridChoice (Mβ β) σ (τβ β) (colFn ch a) (formTop ch t y)

def JetsAt : Prop :=
  (∀ t Φ β, ∃ M, IsTermVol t ch.S.toGridChoice Φ β M) ∧
  ∀ σ : PolCol ch.G × PolRow ch.G →₀ ℂ, ∃ κ : ℂ, ∀ t a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M τ,
    IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y,
      defTot t ch.S.toGridChoice M σ τ (colFn ch a) (formTop ch t y) =
        κ * ch.S.classSum (ch.Phi a) β τ (psiC (ch.Psi a)) (ch.S.formC t y)

def StepProj : Prop := Big fun ch => ProjAt ch

def StepFlip : Prop := Big fun ch => FlipAt ch

def StepUnfold : Prop := Big fun ch => UnfoldAt ch

def StepJets : Prop := Big fun ch => JetsAt ch

end GlobalTheory.RowClaim

end
