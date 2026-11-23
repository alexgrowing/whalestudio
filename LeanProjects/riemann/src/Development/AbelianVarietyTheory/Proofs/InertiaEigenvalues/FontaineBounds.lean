import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.FontaineAdm

theorem fontaine_bounds : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm8 D := by
  intro D l _ K LL T
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.dcris_finite_le_of_tied (D.locT l) K LL T.V T.ρ
  refine ⟨⟨h1, h2⟩, fun τ => ?_⟩
  obtain ⟨hd, -⟩ := GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ
  exact ⟨(hd τ).1, (hd τ).2.1⟩

end GlobalTheory.Per.FontaineAdm
