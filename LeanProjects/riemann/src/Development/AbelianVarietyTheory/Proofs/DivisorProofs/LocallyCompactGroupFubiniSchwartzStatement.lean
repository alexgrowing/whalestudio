import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyCompactGroupFubiniSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_compact_group_fubini_schwartz : ∀ {G V Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
  [AddCommGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [LocallyCompactSpace Z] [SecondCountableTopology Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]
  (νV : Measure V) (νZ : Measure Z), νV.IsAddHaarMeasure → νZ.IsAddHaarMeasure →
  ∀ (Φ : G ≃ₜ V × Z) (β : V → V → Z), Continuous (Function.uncurry β) →
  (∀ u v, Φ (u * v) = ((Φ u).1 + (Φ v).1, (Φ u).2 + (Φ v).2 + β (Φ u).1 (Φ v).1)) →
  ∀ (f : G → G) (A : V ≃ₜ V) (C : Z ≃ₜ Z) (a c : ENNReal), a ≠ ⊤ → c ≠ ⊤ → νV.map A = a • νV → νZ.map C = c • νZ →
  (∀ u, Φ (f u) = (A (Φ u).1, C (Φ u).2)) →
  ∀ μ : Measure G, μ.IsHaarMeasure → ∀ S : Set G, μ (f ⁻¹' S) = a * c * μ S := by
  first | exact @GlobalTheory.heisenberg_preimage_haar | exact GlobalTheory.heisenberg_preimage_haar | (intros; apply GlobalTheory.heisenberg_preimage_haar <;> assumption)
