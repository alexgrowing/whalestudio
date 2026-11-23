import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedAwayStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameAnyAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameOfFrobeniusDenseStatement

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem tameSum_of_inputs : ∀ D : D7, WildOne D →
    (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k →
      ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) →
    GalAway D → FrobDense D → PointPar D → TameSum D := by
  intro D hW hχ hG hF hP i Sig hx hfull hc ρ hρ k hk
  obtain ⟨x, hx⟩ := hx
  obtain ⟨π, rfl⟩ := hc
  obtain ⟨h1, h2⟩ := hP i x π hx
  refine ⟨GlobalTheory.T.tame_fixed_away D hW hG hF i π ρ h1 h2 hfull hρ k hk, fun w hw ht => ?_⟩
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · subst hv
    exact GlobalTheory.T.tame_any_at_place D hG hF i π ρ h1 h2 hfull hρ k hk v
  · exact GlobalTheory.T.tame_of_frobenius_dense D hW hχ hG hF i π ρ h1 h2 hfull hρ k hk v w hv ht

end GlobalTheory.TypeLeaf
