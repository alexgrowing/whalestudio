import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DixmierMalliavinLie

open GlobalTheory.Orb
open scoped Topology ContDiff Manifold

noncomputable section

namespace GlobalTheory.MatLie

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {d : ℕ}

def transChart (φ : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin d))) (a : G) :
    OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin d)) :=
  (Homeomorph.mulLeft a⁻¹).toOpenPartialHomeomorph.trans φ

variable (φ : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin d)))

@[simp] theorem transChart_apply (a x : G) : transChart φ a x = φ (a⁻¹ * x) := rfl

@[simp] theorem transChart_symm_apply (a : G) (y : EuclideanSpace ℝ (Fin d)) :
    (transChart φ a).symm y = a * φ.symm y := by
  simp [transChart, Homeomorph.mulLeft_symm]

@[simp] theorem transChart_source (a : G) : (transChart φ a).source = {x | a⁻¹ * x ∈ φ.source} := by
  ext x; simp [transChart]

@[simp] theorem transChart_target (a : G) : (transChart φ a).target = φ.target := by
  ext y; simp [transChart]

def chartedSpace (h1 : (1 : G) ∈ φ.source) : ChartedSpace (EuclideanSpace ℝ (Fin d)) G where
  atlas := Set.range (transChart φ)
  chartAt := transChart φ
  mem_chart_source a := by simp [h1]
  chart_mem_atlas a := ⟨a, rfl⟩

end GlobalTheory.MatLie
