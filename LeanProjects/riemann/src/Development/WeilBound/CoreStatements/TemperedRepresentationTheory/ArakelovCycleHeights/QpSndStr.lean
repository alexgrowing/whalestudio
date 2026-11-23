import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.ArMixIff
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.ExtLBAmb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.ArithmeticHeightTower

def twB (m : ℕ) (n : Fin (m + 1) → ℕ) (c : Fin m) (t : ℤ) : LB (MP ℤ m n) :=
  tw ((O1 ℤ (n c.succ)).pull (pr ℤ m n c.succ)) ((O1 ℤ (n 0)).pull (pr ℤ m n 0)) t

def IsTwB {m : ℕ} {n : Fin (m + 1) → ℕ} (M : HermLB (mpStr ℤ m n)) : Prop :=
  ∃ (c : Fin m) (t : ℤ), Nonempty (LBIso M.B (twB m n c t))

abbrev QP (n' m : ℕ) (n : Fin (m + 1) → ℕ) : Scheme.{0} := pullback (toSpecBase ℤ n') (mpStr ℤ m n)

abbrev qpStr (n' m : ℕ) (n : Fin (m + 1) → ℕ) : QP n' m n ⟶ Sp ℤ := pullback.fst _ _ ≫ toSpecBase ℤ n'

abbrev qpSnd (n' m : ℕ) (n : Fin (m + 1) → ℕ) : QP n' m n ⟶ MP ℤ m n := pullback.snd _ _

theorem qpSnd_str (n' m : ℕ) (n : Fin (m + 1) → ℕ) : qpSnd n' m n ≫ mpStr ℤ m n = qpStr n' m n :=
  pullback.condition.symm

def HeightsZ : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)), IsTwB M → ∃ h, M.IsArithHeight h

def HeightsQ : Prop := ∀ (n' m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)), IsTwB M →
  ∃ h, (M.pull (qpSnd n' m n) (qpSnd_str n' m n)).IsArithHeight h

def FormZ : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n)
  [IsClosedImmersion i] (D : ℕ), IsArithVar (i ≫ mpStr ℤ m n) D → ∀ (ι : Type) [Fintype ι] (M : ι → HermLB (mpStr ℤ m n)),
    (∀ j, IsTwB (M j)) → ∃ Φ, IsArFun (fun j => (M j).restr i) D Φ

def MixZ : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
  (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ), IsArithVar (i ≫ mpStr ℤ m n) D →
    ∀ (ι : Type) [Fintype ι] (M₀ : HermLB (mpStr ℤ m n)) (M : ι → HermLB (mpStr ℤ m n)), IsTwB M₀ → (∀ j, IsTwB (M j)) →
      GlobalTheory.Published.Amb.MixOn (i ≫ mpStr ℤ m n) D ι (M₀.restr i) (fun j => (M j).restr i)

def ProjQ : Prop := ∀ (n' m : ℕ) (n : Fin (m + 1) → ℕ) (Y : Scheme.{0}) [IsIntegral Y] (j : Y ⟶ QP n' m n)
  [IsClosedImmersion j] (e : ℕ), IsArithVar (j ≫ qpStr n' m n) e →
    topologicalKrullDim (closure ({qpSnd n' m n (j (genericPoint Y))} : Set (MP ℤ m n))) = (e + 1 : ℕ) →
    (qpSnd n' m n).residueDegree (j (genericPoint Y)) ≠ 0 → ∀ (M : HermLB (mpStr ℤ m n)), IsTwB M →
    ∀ (h : MP ℤ m n → ℝ) (h' : QP n' m n → ℝ), M.IsArithHeight h →
      (M.pull (qpSnd n' m n) (qpSnd_str n' m n)).IsArithHeight h' →
        h' (j (genericPoint Y)) = ((qpSnd n' m n).residueDegree (j (genericPoint Y)) : ℝ) *
          h (qpSnd n' m n (j (genericPoint Y)))

def CyclesZ : Prop := HeightsZ ∧ HeightsQ ∧ FormZ ∧ MixZ ∧ ProjQ

end GlobalTheory.ArithmeticHeightTower
