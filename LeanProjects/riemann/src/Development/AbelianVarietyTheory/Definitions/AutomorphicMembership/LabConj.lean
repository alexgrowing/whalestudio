import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

def LabConj (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) : Prop :=
  ∀ k v (w : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w → ∃ (c : D.nd.Om ≃+* D.nd.Om) (γ : G D.host.E D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
    (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ (∀ x, γ (c x) = c (D.ntypes.tg k v x)) ∧
    ∀ a : D.naut.LP w, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      D.naut.items₂ k w a = GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ (T.e w a)

end GlobalTheory.HeightCounting

end
