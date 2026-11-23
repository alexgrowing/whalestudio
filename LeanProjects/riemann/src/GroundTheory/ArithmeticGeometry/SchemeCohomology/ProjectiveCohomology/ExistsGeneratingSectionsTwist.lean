import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.SerreP
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Immersion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ} {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (i : X ⟶ projectiveSpace A n) [IsClosedImmersion i]
  [i.IsOver (Spec (.of A))]

omit [IsNoetherianRing A] [X.Over (Spec (.of A))] [i.IsOver (Spec (.of A))] in

theorem exists_generatingSections_twist (F : X.Modules) (hF : IsCoherent F) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ σ : (twist i F q).GeneratingSections, σ.IsFiniteType := by
  have := hF.1
  obtain ⟨q₀, hq₀⟩ := ProjSpace.exists_generatingSections_twist _ (isCoherent_pushforward i hF)
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨σ, hσ⟩ := hq₀ q hq
  exact exists_generatingSections_of_pushforward i (twist i F q)
    (exists_generatingSections_of_iso (pushforwardTwistIso i F q) ⟨σ, hσ⟩)

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

attribute [local instance] algebraOfOver

include i in

theorem finite_H (F : X.Modules) (hF : IsCoherent F) (p : ℕ) :
    Module.Finite A (Sheaf.H.{w'} (modulesAb F) p) := by
  have := hF.1
  have := ProjSpace.finite_H.{w'} _ (isCoherent_pushforward i hF) p
  exact Module.Finite.equiv (HLinearEquivPushforward.{w'} i F p).symm

theorem exists_subsingleton_H_twist (F : X.Modules) (hF : IsCoherent F) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ p : ℕ, 0 < p →
      Subsingleton (Sheaf.H.{w'} (modulesAb (twist i F q)) p) := by
  have := hF.1
  obtain ⟨q₀, hq₀⟩ := ProjSpace.exists_subsingleton_H_twist.{w'} _ (isCoherent_pushforward i hF)
  refine ⟨q₀, fun q hq p hp => ?_⟩
  have h₁ := hq₀ q hq p hp
  have e₁ := HLinearEquivPushforward.{w'} i (twist i F q) p
  have e₂ : Sheaf.H.{w'} (modulesAb (ProjSpace.twist ((Scheme.Modules.pushforward i).obj F) q)) p ≃+
      Sheaf.H.{w'} (modulesAb ((Scheme.Modules.pushforward i).obj (twist i F q))) p :=
    ((H.moduleFunctor.{w'} A p).mapIso (pushforwardTwistIso i F q)).toLinearEquiv.toAddEquiv
  exact e₁.toEquiv.subsingleton_congr.2 (e₂.toEquiv.subsingleton_congr.1 h₁)

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh
