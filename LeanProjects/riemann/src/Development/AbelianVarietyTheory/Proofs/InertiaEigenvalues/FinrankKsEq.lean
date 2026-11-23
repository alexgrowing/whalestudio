import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem finrank_Ks_eq : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (s : ℕ), 0 < s → finrank ℚ_[l] ↥(Loc.Ks K s) = finrank ℚ_[l] ↥(Loc.K0 K) * (l ^ (s - 1) * (l - 1)) := by
  intro l _ K s hs
  rw [GlobalTheory.Cyc.finrank_Ks K s hs, mul_comm (l - 1)]

end GlobalTheory.HubLoc
