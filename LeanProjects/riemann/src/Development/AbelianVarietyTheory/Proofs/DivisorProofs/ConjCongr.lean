import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal
open scoped Formalism.Per

namespace GlobalTheory.ConjPeriod

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

def uj (T : LocTied l P AI) (j : ℕ) : Per.Acris l →+* P.R.BdR :=
  (P.ιB : P.R.B →+* P.R.BdR).comp
    (T.eB.symm.toRingHom.comp ((algebraMap (Per.Acris l) (Per.Bcris l)).comp (GlobalTheory.MemLoc.phiA l ^ j)))

def Compat (T : LocTied l P AI) (K : FinExt l) (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) : Prop :=
  ∀ w : W0 K, uj T j (aC l (wA l (fK K) w)) =
    algebraMap (Om l) P.R.BdR (s (oK K (thetaW (fK K) K w)))

def conj (T : LocTied l P AI) (K : FinExt l) (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s) :
    BK K →+* P.R.BdR :=
  liftB (uj T j) ((algebraMap (Om l) P.R.BdR).comp (s : ↥K.1 →+* Om l)) h

theorem conj_inK (T : LocTied l P AI) (K : FinExt l) (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s)
    (c : ↥K.1) : conj T K j s h (inK K c) = algebraMap (Om l) P.R.BdR (s c) :=
  liftB_inK (uj T j) ((algebraMap (Om l) P.R.BdR).comp (s : ↥K.1 →+* Om l)) h c

theorem conj_inC (T : LocTied l P AI) (K : FinExt l) (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s)
    (a : Per.Acris l) : conj T K j s h (toB K (inC K a)) = uj T j a :=
  liftB_inC (uj T j) ((algebraMap (Om l) P.R.BdR).comp (s : ↥K.1 →+* Om l)) h a

end GlobalTheory.ConjPeriod

end
