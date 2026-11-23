import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ComplexMetric.GermFraction.proof : ComplexMetric.GermFraction.Statement.{u} := by
  intro A _ N V g q hq
  obtain ⟨W, hqW, i, d, r, s, hs, hw⟩ := g.2 ⟨q, hq⟩
  refine ⟨W, hqW, i.le, d, r.1, s.1, r.2, s.2, fun y hy => hs ⟨y, hy⟩, ?_⟩
  intro ρ w y hy h
  have e1 : (Proj.stalkIso (ProjSpace.grading A N) y).hom.hom
      ((projectiveSpace A N).presheaf.germ V y (i.le hy) g) = g.1 ⟨y, i.le hy⟩ :=
    Proj.stalkIso'_germ _ V y (i.le hy) g
  rw [evalStalkProj, RingHom.comp_apply, e1]
  have e2 : g.1 ⟨y, i.le hy⟩ = _ := hw ⟨y, hy⟩
  rw [e2, evalAtPrime_mk]

end GroundTheory.Heights₂.Heights
