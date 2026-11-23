import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity

noncomputable section
namespace GlobalTheory.HermitianPreEigenvalues
variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

def mulR (a : S → O) (N : ℕ) (r : RS a) : (Fin N → RS a) →ₗ[O] (Fin N → RS a) :=
  (LinearMap.lsmul (RS a) (Fin N → RS a) r).restrictScalars O

def preEig (a : S → O) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) :
    Submodule O (Fin N → RS a) :=
  (Fil.restrictScalars O).comap (mulR a N (lin a τ))

def filKer (a : S → O) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) :
    Submodule O (Fin N → RS a) :=
  Fil.restrictScalars O ⊓ LinearMap.ker (mulR a N (cofac a τ))

end GlobalTheory.HermitianPreEigenvalues
