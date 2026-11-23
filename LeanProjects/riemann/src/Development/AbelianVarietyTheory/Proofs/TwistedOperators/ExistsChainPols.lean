import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def colPure (W : G.Weil) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j))
    (q : ∀ j : Fin D.R.m, PolF D (G.pT (.mu t 0 j)).rank (G.pS (.mu t 0 j)).rank) : PureT G (downPath t 0 D.R.m) :=
  downFam t 0 D.R.m fun j => W.fock (.mu t 0 j) (f j) (q j)

def givenFin (W : G.Weil) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j)) (Φ : G.Datum) : PureT G (givenPath t D.R.m) :=
  Path.Fam.append (downFam t 0 D.R.m f) (rowFam 0 D.R.m fun i => W.cosVec i (Φ i))

def gPol (ρ : G.RealVec) (q : ∀ j : ℕ, PolF D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank) : PolE G
  | .ex i 0 => if h : i < D.R.m then ρ ⟨i, h⟩ else 0
  | .ex _ (_ + 1) => 0
  | .theta 0 j => q j
  | .theta (_ + 1) _ => 0

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def ChainVecs (ch : Choice R) (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) : Prop :=
  ∀ j : Fin D.R.m, ((j : ℕ) + 1 < D.R.m → HEq (f j) (R.vY t j)) ∧ ((j : ℕ) + 1 = D.R.m → HEq (f j) (R.vX t))

def ChainPols (ch : Choice R) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank) : Prop :=
  ∀ j : ℕ, (j + 1 < D.R.m → HEq (q j) (ch.cv.polY j)) ∧ (j + 1 = D.R.m → HEq (q j) ch.cv.polX)

theorem exists_heq_fun (Y Y' : LSp D) (S S' : HSp D) (Λ Λ') (hY : Y = ⟨S, Λ⟩) (hY' : Y' = ⟨S', Λ'⟩) (f : WO S S' → ℂ) :
    ∃ f' : WO Y.sp Y'.sp → ℂ, HEq f' f := by
  subst hY hY'; exact ⟨f, HEq.rfl⟩

theorem exists_heq_pol {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : PolF D a b) : ∃ P' : PolF D a' b', HEq P' P := by
  subst ha hb; exact ⟨P, HEq.rfl⟩

theorem rank_col_lt (L : LevCh D T) {j : ℕ} (h : j < D.R.m) : (columnBlock L j).sp.rank = (Yc D j).rank := by
  rw [colY_lt L h]

theorem rank_col_m (L : LevCh D T) : (columnBlock L D.R.m).sp.rank = D.sp.X'.rank := by
  rw [colY_m L]

theorem exists_chainVecs (ch : Choice R) (t : T) : ∃ f, ChainVecs ch t f := by
  have H : ∀ j : Fin D.R.m, ∃ f : Sch ch.G (.down t 0 j),
      ((j : ℕ) + 1 < D.R.m → HEq f (R.vY t j)) ∧ ((j : ℕ) + 1 = D.R.m → HEq f (R.vX t)) := fun ⟨j, hj⟩ => by
    by_cases h : j + 1 < D.R.m
    · obtain ⟨f, e⟩ := exists_heq_fun (columnBlock R.toLevCh j) (columnBlock R.toLevCh (j + 1)) _ _ _ _ (colY_lt _ (by omega))
        (colY_lt _ h) (R.vY t j)
      exact ⟨f, fun _ => e, fun h' => by simp at h'; omega⟩
    · have e1 : j = D.R.m - 1 := by omega
      subst e1
      have e2 : columnBlock R.toLevCh (D.R.m - 1 + 1) = ⟨D.sp.X', R.ΛX⟩ := by
        rw [Nat.sub_add_cancel (by omega)]; exact colY_m _
      obtain ⟨f, e⟩ := exists_heq_fun (columnBlock R.toLevCh (D.R.m - 1)) (columnBlock R.toLevCh (D.R.m - 1 + 1)) _ _ _ _
        (colY_lt _ (by omega)) e2 (R.vX t)
      exact ⟨f, fun h' => absurd h' h, fun _ => e⟩
  choose f hf using H
  exact ⟨f, hf⟩

theorem exists_chainPols (ch : Choice R) : ∃ q, ChainPols ch q := by
  have H : ∀ j : ℕ, ∃ q : PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank,
      (j + 1 < D.R.m → HEq q (ch.cv.polY j)) ∧ (j + 1 = D.R.m → HEq q ch.cv.polX) := fun j => by
    by_cases h : j + 1 < D.R.m
    · obtain ⟨q, e⟩ := exists_heq_pol (rank_col_lt R.toLevCh h) (rank_col_lt R.toLevCh (by omega)) (ch.cv.polY j)
      exact ⟨q, fun _ => e, fun h' => by omega⟩
    · by_cases h' : j + 1 = D.R.m
      · have e1 : j = D.R.m - 1 := by omega
        subst e1
        have e2 : (columnBlock R.toLevCh (D.R.m - 1 + 1)).sp.rank = D.sp.X'.rank := by
          rw [Nat.sub_add_cancel (by omega)]; exact rank_col_m _
        obtain ⟨q, e⟩ := exists_heq_pol e2 (rank_col_lt R.toLevCh (by omega)) ch.cv.polX
        exact ⟨q, fun h'' => absurd h'' h, fun _ => e⟩
      · exact ⟨0, fun h'' => absurd h'' h, fun h'' => absurd h'' h'⟩
  choose q hq using H
  exact ⟨q, hq⟩

end GlobalTheory.FlipStart

end
