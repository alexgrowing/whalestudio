import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SuccMulSuccSubOneDivSucc
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CardFilterValLt
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetOfColSpanEq
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bridge
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.YVMapRowAct
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.TgtBidet
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.GeXZero

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

abbrev BX : Type := Σ v : X.Pl, Fin (X.G.P.n' v)

abbrev NJ (j : ℕ) : ℕ := NN X.G.P.m X.t j

def emX (j : ℕ) (b : BX X) (v : Fin (NJ X j) × Fin (NJ X j)) :
    (Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :=
  idxI X j ⟨b.1, (b.2, v)⟩

def xmX (j : ℕ) (b : BX X) (s : ℕ × Fin (NJ X j)) : X.FrI j := ⟨b.1, (b.2, s.1, s.2)⟩

def mF (j : ℕ) (b : BX X) (A : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    Matrix (Fin (NJ X j)) (Fin (NJ X j)) X.G.Kf :=
  (A.map fun x => X.G.P.ι b.1 ((X.G.P.σ b.1 ^ b.2.val) x)).submatrix (finCongr (rank_eq X j).symm) (finCongr (rank_eq X j).symm)

def nuM : (j : ℕ) → BX X → Fin (NJ X j) → ℕ
  | 0, b, t => nuOf (lamAt (X.G.P.lam0 b.1) b.2) (Fin.cast (rankJ X 0).symm t)
  | j + 1, b, t => nuOf (lamAt ((X.Fl.Pj (j + 1)).lam0 b.1) b.2) (Fin.cast (rankJ X (j + 1)).symm t)

def sX (j : ℕ) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) : X.G.Kf :=
  ∏ b : BX X, (mF X j b (g b.1)).det ^ (-(eJ X j b.1 b.2))

def muX (j n : ℕ) (b : BX X) : Fin n → ℕ := fun t => (X.nuv b.1 (j + 1) b.2 (t.val + 1)).toNat

def cX (j : ℕ) (b : BX X) : ℕ := (X.nuv b.1 (j + 1) b.2 1).toNat

def eX (j : ℕ) (b : BX X) : ℕ := (X.nuv b.1 (j + 1) b.2 (NJ X j)).toNat

def nuS (j : ℕ) (b : BX X) : Fin (NJ X j) → ℕ :=
  if IsOddPos b.2 then fun t => cX X j b - muX X j (NJ X j) b t.rev else fun t => muX X j (NJ X j) b t - eX X j b

def nuT (j : ℕ) (b : BX X) : Fin (NJ X (j + 1)) → ℕ :=
  if IsOddPos b.2 then fun t => cX X j b - muX X j (NJ X (j + 1)) b t.rev else muX X j (NJ X (j + 1)) b

def HgX (R : Type) [CommRing R] (j : ℕ) (b : BX X) : GenR R (NJ X j) :=
  if IsOddPos b.2 then hvO (gX R (NJ X j)) (gY R (NJ X j)) (cX X j b) (fun k => colH (muX X j (NJ X j) b) k.val)
  else (Matrix.of fun a i : Fin (NJ X j) => gX R (NJ X j) a i.val).det ^ (eX X j b) *
    hvE (gX R (NJ X j)) (gY R (NJ X j)) (cX X j b) (fun k => colH (nuS X j b) k.val) (fun k => colH_le _ k.val)

def szT (j : ℕ) (b : BX X) (k : Fin (cX X j b)) : ℕ :=
  if IsOddPos b.2 then NJ X (j + 1) - colH (muX X j (NJ X (j + 1)) b) k.val else colH (muX X j (NJ X (j + 1)) b) k.val

theorem szT_le (j : ℕ) (b : BX X) (k : Fin (cX X j b)) : szT X j b k ≤ NJ X (j + 1) := by
  unfold szT
  split_ifs
  · exact Nat.sub_le _ _
  · exact colH_le _ _

end Formalism.L2.PairingIndexBounds.Ent
