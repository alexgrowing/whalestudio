import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
import Formalism.LocalToGlobal.BaseRankEqOfRealisation

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Inhab

open GlobalTheory.SymBridge

section Frames

variable {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]

def stdFr (k : Type) [Field k] (e : Y ≃ Fin N) : GlobalTheory.LocMod.Frame k N Y where
  β := (1 : Matrix (Fin N) (Fin N) k).submatrix id e
  γ := (1 : Matrix (Fin N) (Fin N) k).submatrix e id
  βγ := by rw [Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_id_id]
  γβ := by
    have h := Matrix.submatrix_mul_equiv (1 : Matrix (Fin N) (Fin N) k) (1 : Matrix (Fin N) (Fin N) k) e (Equiv.refl _) e
    rw [Matrix.one_mul, Matrix.submatrix_one_equiv] at h
    exact h

def negFr (F : GlobalTheory.LocMod.Frame k N Y) : GlobalTheory.LocMod.Frame k N Y where
  β := -F.β
  γ := -F.γ
  βγ := by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, F.βγ]
  γβ := by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, F.γβ]

theorem isStdFr_stdFr {pos : Y → ℕ} {e : Y ≃ Fin N} (h : IsOrd pos e) : IsStdFr pos (stdFr k e) := ⟨e, h, rfl⟩

theorem isStdFr_unique {pos : Y → ℕ} {F F' : GlobalTheory.LocMod.Frame k N Y} (h : IsStdFr pos F) (h' : IsStdFr pos F') : F.β = F'.β := by
  obtain ⟨e, he, hF⟩ := h
  obtain ⟨e', he', hF'⟩ := h'
  have : e = e' := Equiv.ext fun a => Fin.ext ((he a).trans (he' a).symm)
  rw [hF, hF', this]

theorem not_isStdFr_neg [Nonempty Y] (h2 : (2 : k) ≠ 0) {pos : Y → ℕ} {F : GlobalTheory.LocMod.Frame k N Y} (h : IsStdFr pos F) :
    ¬ IsStdFr pos (negFr F) := fun h' => by
  have hβ : -F.β = F.β := isStdFr_unique h' h
  obtain ⟨e, -, hF⟩ := h
  obtain ⟨a⟩ := ‹Nonempty Y›
  have h1 : -F.β (e a) a = F.β (e a) a := congrFun (congrFun hβ (e a)) a
  have h0 : F.β (e a) a = 1 := by rw [hF]; exact Matrix.one_apply_eq (e a)
  rw [h0] at h1
  exact h2 (by linear_combination -h1)

def blockOrd (κ τ l j : ℕ) : (Fin κ ⊕ Fin l) ⊕ Fin j × Fin τ ≃ Fin (κ + l + j * τ) :=
  (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv

theorem isOrd_xPos (κ τ j : ℕ) : IsOrd (xPos (κ := κ) (τ := τ) (j := j)) (blockOrd κ τ j j) := by
  rintro ((i | i) | ⟨a, b⟩) <;> simp [blockOrd, xPos, finProdFinEquiv]
  ring

theorem isOrd_zPos (κ τ l j : ℕ) : IsOrd (zPos (κ := κ) (τ := τ) (l := l) (j := j)) (blockOrd κ τ l j) := by
  rintro ((i | i) | ⟨a, b⟩) <;> simp [blockOrd, zPos, finProdFinEquiv]
  ring

theorem exists_isStdFr (k : Type) [Field k] (κ τ l j : ℕ) :
    (∃ F : GlobalTheory.LocMod.Frame k (κ + j + j * τ) (XIx (Fin κ) (Fin τ) j), IsStdFr xPos F) ∧
      ∃ F : GlobalTheory.LocMod.Frame k (κ + l + j * τ) (Ix (Fin κ ⊕ Fin l) (Fin τ) j), IsStdFr zPos F :=
  ⟨⟨_, isStdFr_stdFr (isOrd_xPos κ τ j)⟩, ⟨_, isStdFr_stdFr (isOrd_zPos κ τ l j)⟩⟩

theorem isStdFr_stdFr_and_not_isStdFr_negFr : IsStdFr (xPos (κ := 1) (τ := 1) (j := 1)) (stdFr ℚ (blockOrd 1 1 1 1)) ∧
    ¬ IsStdFr (xPos (κ := 1) (τ := 1) (j := 1)) (negFr (stdFr ℚ (blockOrd 1 1 1 1))) :=
  ⟨isStdFr_stdFr (isOrd_xPos 1 1 1), not_isStdFr_neg two_ne_zero (isStdFr_stdFr (isOrd_xPos 1 1 1))⟩

end Frames

section True

open GlobalTheory.Mem

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

end True

section Built

open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

def packOf {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {x : TwIn ex} {Rc : Formalism.L2.RecT ex}
    {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} (y : RealIn x Rc S) : RealPack ex where
  R := Rc
  S := S
  P := divisionPairOfAdelicFormsFaceColumnsData x
  Dcf := x.F.Dc
  Spf := x.F.Sp
  Zscf := x.F.Zsc
  Ks := x.core.Q.c.F
  Q := realTOf y

def tupP {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (s : W.P.T) : D.what₂.Tup := W.P.I.tup s

theorem packOf_tup {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {x : TwIn ex} {Rc : Formalism.L2.RecT ex}
    {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} (y : RealIn x Rc S) (s : x.T) :
    Formalism.IndefR.RecTie.Used0 D (tupP (packOf y) s) ∧ x.Y.tupT (tupP (packOf y) s) = s :=
  ⟨Formalism.IndefR.LevelRealisationRankEquality.tupAllUsed_of_real (realTOf y) s, x.Y.tupT_tup s⟩

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) {Rc : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} (y : RealIn a.x Rc S)

end Built

end GlobalTheory.Fam.Inhab

end
