import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesEqUnionThreeParts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharMemF0Primes
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.SatForced

theorem resChar_eq_of_overOne (D : D7) {v v' : D.what₂.places.Pl} (h : GlobalTheory.TwistChoice.OverOne D v v') :
    D.what₂.places.resChar v = D.what₂.places.resChar v' := by
  have hp := D.what₂.places.resChar_prime v
  have h1 := GlobalTheory.TwistChoice.val_resChar_pos D v
  have h2 := (h ((D.what₂.places.resChar v : ℕ) : 𝓞 ↥D.LL0)).1 (by simpa using h1)
  exact GlobalTheory.TwistChoice.eq_resChar_of_pos D v' hp (by simpa using h2)

theorem mem_W1F_of_overOne : ∀ (K : Ctx) (D : D7) (v v' : D.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D v v' →
    v ∈ placesWithNonzeroContentOrConj D (F0K K.s D) → v' ∈ placesWithNonzeroContentOrConj D (F0K K.s D) := by
  intro K D v v' h hv
  obtain ⟨j, y, hy, hne⟩ := hv
  have key : D.what₂.places.resChar (D.plEq.symm y) = D.what₂.places.resChar v := by
    rcases hy with e | e
    · rw [e, Equiv.symm_apply_apply]
    · rw [e]; exact GlobalTheory.Mem.NonzeroPlacesOverPrimes.resChar_symm_conjPl D v
  refine ⟨j, D.plEq v', Or.inl rfl, ?_⟩
  have e2 : F0K K.s D (D.plEq v') j = F0K K.s D y j := by
    unfold F0K
    rw [key, Equiv.symm_apply_apply, resChar_eq_of_overOne D h]
  rw [e2]; exact hne

end GlobalTheory.Mem.SatForced
