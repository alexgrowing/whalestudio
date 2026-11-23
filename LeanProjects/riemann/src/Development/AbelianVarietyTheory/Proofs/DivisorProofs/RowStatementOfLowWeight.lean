import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToRatHyp0
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesBaseTwistedUniversalRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPrimeMemExceptionalSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDataRealizationStatement
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem rowAt_of : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → LowAt → TwAdm → RowAt := by
  intro hP hA hR hS hL hT
  refine rowAt_of_ratStep ?_ (GlobalTheory.T.thetaSeries_base_twisted_universal_rational hA hR hS)
  exact AtTw.imp (AtTw.and hL hT) fun Fm x hx i p hp hM w _ j h =>
    GlobalTheory.T.exists_rational_data_realization hP Fm x hx i p hp hM _ j (ratHyp0_at_point Fm x hx i p hp hM _ h.2.2.2 h.1 j)

end GlobalTheory.BigOn.Exp
