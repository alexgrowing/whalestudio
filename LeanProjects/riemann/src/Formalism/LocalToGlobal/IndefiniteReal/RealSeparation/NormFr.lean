import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def nfScal (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) (j : ℕ) : ℕ → D.host.E
  | 0 => s j
  | i + 1 => κ j i * nfScal κ s j i

def vecY (j : ℕ) (x : Fin (D.sp.Y j).rank → D.host.E) : (D.sp.Y j).V := (D.sp.Y j).frame.equivFun.symm x

def adaptedVector (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (j i : ℕ) :
    Fin (D.sp.Y j).rank → D.host.E :=
  if i < (D.R.m - 1 - j) / 2 then e j i
  else if (D.R.m - 1 - j) % 2 = 1 ∧ i = (D.R.m - 1 - j) / 2 then z j
  else ev j (D.R.m - 1 - j - 1 - i)

def IsAdaptedVectorSystem (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) : Prop :=
  ∀ j < D.R.m,
    (∀ i < (D.R.m - 1 - j) / 2, ∀ l < (D.R.m - 1 - j) / 2,
      (D.sp.Y j).hT (vecY j (e j i)) (vecY j (ev j l)) = (if i = l then 1 else 0) ∧
      (D.sp.Y j).hT (vecY j (e j i)) (vecY j (e j l)) = 0 ∧ (D.sp.Y j).hT (vecY j (ev j i)) (vecY j (ev j l)) = 0) ∧
    ((D.R.m - 1 - j) % 2 = 1 →
      (D.sp.Y j).hT (vecY j (z j)) (vecY j (z j)) = -(D.sp.T : D.host.E) ∧
      ∀ i < (D.R.m - 1 - j) / 2,
        (D.sp.Y j).hT (vecY j (z j)) (vecY j (e j i)) = 0 ∧ (D.sp.Y j).hT (vecY j (z j)) (vecY j (ev j i)) = 0) ∧
    ∀ x : (D.sp.X j).V, ∀ i' < D.R.m - 1 - j,
      (D.sp.Y j).hT (D.sp.iXY j x) (vecY j (adaptedVector e ev z j i')) = 0

def xInY (j : ℕ) (l : Fin (D.sp.X j).rank) (r : Fin (D.sp.Y j).rank) : D.host.E :=
  (D.sp.Y j).frame.repr (D.sp.iXY j ((D.sp.X j).frame l)) r

def xMat (j : ℕ) : Matrix (Fin (D.sp.Y j).rank) (Fin (D.sp.X j).rank) (EAf D) :=
  fun r l => eToEAf D (xInY j l r)

def XSpanAt (j : ℕ) (β : Matrix (Fin (D.sp.Y j).rank) (Fin (D.sp.Y j).rank) (EAf D)) (ei : AE D) (col : Fin (D.sp.Y j).rank) :
    Prop :=
  ∃ y : Fin (D.sp.X j).rank → EAf D, ∀ r : Fin (D.sp.Y j).rank,
    toEAf D ei * β r col = toEAf D ei * Matrix.mulVec (xMat (D := D) j) y r

def ColAt (j : ℕ) (β : Matrix (Fin (D.sp.Y j).rank) (Fin (D.sp.Y j).rank) (EAf D)) (ei : AE D) (col : Fin (D.sp.Y j).rank)
    (v : Fin (D.sp.Y j).rank → D.host.E) : Prop :=
  ∀ r : Fin (D.sp.Y j).rank, toEAf D ei * β r col = toEAf D ei * eToEAf D (v r)

open Classical in

def NormalFrames (βY : ∀ j : ℕ, GL (Fin (D.sp.Y j).rank) (EAf D)) (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E)
    (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E)
    (S Pg : Finset (Pl D.host.E)) : Prop :=
  IsAdaptedVectorSystem e ev z ∧ (∀ j i, κ j i ≠ 0) ∧ (∀ j, s j ≠ 0) ∧
  (∀ PP ∈ Pg, ∀ j < D.R.m, ∀ i < D.R.m - 1 - j, PP.valuation D.host.E (nfScal κ s j i) = 1) ∧
  ∀ PP ∈ S, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → ∀ j < D.R.m,
    (∀ i < D.R.m - 1 - j, ∀ col : Fin (D.sp.Y j).rank, col.val = D.R.k + i →
      ColAt j (βY j).val ei col fun r =>
        (if PP ∈ Pg then ((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) else 1) *
          (nfScal κ s j i * adaptedVector e ev z j i r)) ∧
    (∀ col : Fin (D.sp.Y j).rank, (col.val < D.R.k ∨ D.R.k + (D.R.m - 1 - j) ≤ col.val) →
      XSpanAt j (βY j).val ei col)

end Formalism.IndefR.Mi

end
