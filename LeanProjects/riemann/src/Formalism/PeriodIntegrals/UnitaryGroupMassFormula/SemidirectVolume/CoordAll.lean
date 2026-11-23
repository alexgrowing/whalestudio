import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModHomeo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary

noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField

theorem heisenberg_coordinates_holds : HeisenbergCoordinates := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T _ hP
  have hσσ := sigma_invol hCM
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  obtain ⟨h1, -, -, -⟩ := Lc.tensor_adele_topology_holds F E
  refine ⟨coordHomeo hσσ hJ hP h2, fun n₀ n => phi_mul hσσ hJ hP h2 n₀ n, fun h hh n n' hn => ?_⟩
  obtain ⟨e1, e2⟩ := phi_conj hσσ hJ hP h2 hh n n' hn
  exact ⟨fun a => congrFun e1 a, Subtype.ext e2⟩

end PI.VolSemiDirect.W.Md
