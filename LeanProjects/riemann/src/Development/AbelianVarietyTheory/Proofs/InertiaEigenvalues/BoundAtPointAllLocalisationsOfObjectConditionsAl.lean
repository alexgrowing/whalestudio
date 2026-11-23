import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesAStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerLengthBoundAtPointStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateFinitenessAllOfLocalTateDualityStatement
import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LocalisationBoundAtPoint

theorem boundAtPoint_all_localisations_of_objectConditions : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.IntegralityFromMetric D := by
  intro hGAR hBK hLTD hLEC D h51 i r ρ π dc lenRow e' cB hR hA hl0 hl1
  have a51 := h51 i hl0 hl1 r ρ π dc lenRow e' cB hR hA
  obtain ⟨G1, G2, G3, G4, G5, G5x, G6, BK, TB, ROW, LIFT, Cont, SS, Decomp, Eps, Comparison₂, Shape, Font, H2, CFT⟩ := hA
  have TB78 : EmbeddingTypes.admTB i r π dc cB := fun w hw _ C hC => TB w hw C hC
  exact GlobalTheory.T.globalLatticeIndexTheorem_of_lengthBoundAtPlaces hGAR hLTD hLEC D i r ρ π dc lenRow e' cB G1 G2 G3 G4 G5 G5x G6 BK
    (GlobalTheory.T.blochKatoAnnihilator_all_of_tateDuality_eulerChar hBK hLTD hLEC D i) Cont Decomp Font (GlobalTheory.T.tateFinitenessAll_of_localTateDuality hLTD D i) Comparison₂ a51
    (GlobalTheory.T.unramifiedTrivialH1f_of_decl D i dc) ROW LIFT TB78 hl0 hl1

end GlobalTheory.LocalisationBoundAtPoint
