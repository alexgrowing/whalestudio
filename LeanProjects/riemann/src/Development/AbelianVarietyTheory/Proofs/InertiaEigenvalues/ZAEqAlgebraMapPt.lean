import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffTaylor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntRingHomExtOfIsHausdorff
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.JumpDR

theorem zA_eq_algebraMap_pt (l : ℕ) [Fact l.Prime] (z : ℤ_[l]) :
    Per.zA l z = algebraMap ℤ_[l] (Ainf l) z := by
  haveI : IsAdicComplete (Ideal.span {(l : WittVector l (PreTilt (OC l) l))}) (WittVector l (PreTilt (OC l) l)) :=
    WittVector.isAdicCompleteIdealSpanP
  have h := padicInt_ringHom_ext_of_isHausdorff l (WittVector l (PreTilt (OC l) l)) (Per.zA l) (algebraMap ℤ_[l] (Ainf l))
  exact RingHom.congr_fun h z

section Rings

variable {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)

def cB : Per.Bcris l →+* Pl.R.BdR :=
  (Pl.ιB : Pl.R.B →+* Pl.R.BdR).comp (Td.eB.symm : Per.Bcris l →+* Pl.R.B)

theorem cB_algebraMap (z : ℤ_[l]) :
    cB Td (algebraMap ℤ_[l] (Per.Bcris l) z) = algebraMap ℚ_[l] Pl.R.BdR (z : ℚ_[l]) := by
  have h : Td.eB.symm (Per.zB l z) = algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l]) := by
    rw [← Td.zB z, RingEquiv.symm_apply_apply]
  have hz : Per.zB l z = algebraMap ℤ_[l] (Per.Bcris l) z :=
    (GlobalTheory.RingIface.zB_eq_aB_zA l z).trans (congrArg (Per.aB l) (zA_eq_algebraMap_pt l z))
  rw [← hz]
  change Pl.ιB (Td.eB.symm (Per.zB l z)) = _
  rw [h, AlgHom.commutes]

def cD : Per.BdRp l →+* Pl.R.BdR :=
  (Td.eD.symm : Per.BdR l →+* Pl.R.BdR).comp (algebraMap (Per.BdRp l) (Per.BdR l))

theorem cD_algebraMap (z : ℤ_[l]) :
    cD Td (algebraMap ℤ_[l] (Per.BdRp l) z) = algebraMap ℚ_[l] Pl.R.BdR (z : ℚ_[l]) := by
  have h : Td.eD.symm (Per.zD l z) = algebraMap ℚ_[l] Pl.R.BdR (z : ℚ_[l]) := by
    rw [← Td.zD z, RingEquiv.symm_apply_apply]
  have hz : Per.zD l z = algebraMap (Per.BdRp l) (Per.BdR l) (algebraMap ℤ_[l] (Per.BdRp l) z) :=
    (GlobalTheory.RingIface.zD_eq_alg l z).trans (congrArg (fun x => algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l x))
      (zA_eq_algebraMap_pt l z))
  rw [hz] at h
  exact h

end Rings

section Hat

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

variable (O) in

def kLift (c : ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K))) : ZMod a → Ahat O K l e :=
  fun τ => AhatEq.equivAhat O K l e (PowerSeries.C (c τ))

def hsum (P : PhiMod O K l e a ι) {n : ℕ} (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → Vec K a ι) :
    ZMod a → ι → AhatE O K l e :=
  fun τ i => ∑ k, algebraMap (Ahat O K l e) (AhatE O K l e) (s k τ) * P.hatTot (m k) τ i

variable (O K l e) in

def InEhat (j : ℤ) (w : ZMod a → ι → AhatE O K l e) : Prop :=
  ∃ N : ℕ, 0 ≤ j + N ∧ ∀ τ i, ∃ x : Ahat O K l e,
    algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e ^ (j + N).toNat * x) =
      algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e ^ N) * w τ i

end Hat

end GlobalTheory.BKGal.JumpDR
