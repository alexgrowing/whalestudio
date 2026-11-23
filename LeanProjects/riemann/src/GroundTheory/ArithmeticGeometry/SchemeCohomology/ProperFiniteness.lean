import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FinitenessStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

theorem finiteH_of_isProper {X : Scheme.{u}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (F : X.Modules) (hF : IsCoherent F) : FiniteH.{u} A F :=
  finiteH_of_supportedIn X ⊤ F hF (by
    rw [Closeds.coe_top]
    exact Scheme.Modules.SupportedIn.univ F)

theorem finite_H_of_isProper {X : Scheme.{u}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (F : X.Modules) (hF : IsCoherent F) (p : ℕ) :
    Module.Finite A (Sheaf.H.{u} (modulesAb F) p) :=
  finiteH_of_isProper F hF p

end

end GroundTheory.Arith.SchemeCoh
