import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ComplexMetric

lemma continuous_point_of (h₁ : ProjPointContinuous.Statement.{u}) {A : Type u} [CommRing A]
    {N : ℕ} (X : ProjScheme A N) (ρ : A →+* ℂ) : Continuous (X.point (ρ := ρ)) := by
  rw [X.ι.isClosedEmbedding.isInducing.continuous_iff]
  have e : (X.ι.base ∘ X.point (ρ := ρ)) = projPoint ρ ∘ Subtype.val := funext X.ι_point
  rw [e]
  exact (h₁ A N ρ).comp continuous_subtype_val

theorem RegularContinuous.proof (h₁ : ProjPointContinuous.Statement.{u})
    (h₂ : FractionContinuous.Statement.{u}) (h₃ : GermFraction.Statement.{u})
    (h₄ : LocalLift.Statement.{u}) : RegularContinuous.Statement.{u} := by
  intro A _ N X ρ U f
  have hpt := continuous_point_of h₁ X ρ
  rw [continuous_iff_continuousAt]
  rintro ⟨y₀, hy₀⟩
  obtain ⟨V, g, W, hpW, hWU, hWV, hlift⟩ := h₄ A N X U f (X.point y₀) hy₀
  obtain ⟨W', hqW', hW'V, d, a, b, ha, hb, hbW', hval⟩ :=
    h₃ A N V g (X.ι.base (X.point y₀)) (hWV hpW)
  let O : Set {x : X.complexPoints ρ // X.point x ∈ U} :=
    {y | X.point y.1 ∈ W ∧ X.ι.base (X.point y.1) ∈ W'}
  have hc1 : Continuous fun y : {x : X.complexPoints ρ // X.point x ∈ U} => X.point y.1 :=
    hpt.comp continuous_subtype_val
  have hO : IsOpen O :=
    (W.isOpen.preimage hc1).inter (W'.isOpen.preimage (X.ι.continuous.comp hc1))
  have hy₀O : (⟨y₀, hy₀⟩ : {x : X.complexPoints ρ // X.point x ∈ U}) ∈ O := ⟨hpW, hqW'⟩
  have key : ∀ y ∈ O, X.evalAtPoint y.1 (germR y.2 f) =
      evalAt ρ y.1.1.rep a / evalAt ρ y.1.1.rep b := by
    rintro ⟨y, hy⟩ ⟨h1, h2⟩
    have e := hlift (X.point y) h1
    rw [ProjScheme.evalAtPoint, e]
    exact (X.evalStalk_stalkMap (X.isOver_point y) _).trans (hval ρ y.1.rep _ h2 (X.isOver_point y))
  have hne : ∀ y ∈ O, evalAt ρ y.1.1.rep b ≠ 0 := fun y hy h0 =>
    hbW' _ hy.2 ((X.isOver_point y.1 d b hb).2 h0)
  have hg : Continuous fun y : {x : X.complexPoints ρ // X.point x ∈ U} => y.1.1 :=
    continuous_subtype_val.comp continuous_subtype_val
  have hc : ContinuousAt (fun y : {x : X.complexPoints ρ // X.point x ∈ U} =>
      evalAt ρ y.1.1.rep a / evalAt ρ y.1.1.rep b) ⟨y₀, hy₀⟩ := by
    refine ContinuousWithinAt.continuousAt (s := O) ?_ (hO.mem_nhds hy₀O)
    have hF := (h₂ A N ρ d a b ha hb).continuousWithinAt (hne _ hy₀O)
    exact ContinuousWithinAt.comp (f := fun y : {x : X.complexPoints ρ // X.point x ∈ U} => y.1.1)
      hF hg.continuousWithinAt fun y hy => hne y hy
  exact hc.congr (Filter.eventuallyEq_of_mem (hO.mem_nhds hy₀O) fun y hy => (key y hy).symm)

end ComplexMetric

end

end GroundTheory.Heights₂.Heights
