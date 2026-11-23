import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectHaarMeasureProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_haar_measure_product : ∀ (Q L A C : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [T2Space L] [MeasurableSpace L] [BorelSpace L]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C] [LocallyCompactSpace C]
    [SecondCountableTopology C] [T2Space C] [MeasurableSpace C] [BorelSpace C]
    (Φ : L × (A × C) ≃ₜ Q),
    (∀ q' : Q, ∃ (l' : L) (f : L → A) (g : L × A → C), Continuous f ∧ Continuous g ∧
      ∀ l a c, Φ (l, (a, c)) * q' = Φ (l * l', (a + f l, c + g (l, a)))) →
    ∀ (α : Q →* Q) (sA : A →+ A) (sC : C →+ C) (kA kC : ℝ≥0), Continuous α → Continuous sA → Continuous sC →
    (∀ l a c, α (Φ (l, (a, c))) = Φ (l, (sA a, sC c))) →
    (∀ ν : Measure A, ν.IsAddHaarMeasure → ν.map sA = kA • ν) →
    (∀ ν : Measure C, ν.IsAddHaarMeasure → ν.map sC = kC • ν) →
    ∀ μ : Measure Q, μ.IsHaarMeasure → μ.map α = (kA * kC) • μ := by
  first | exact @GlobalTheory.ModulusCoord.map_haar_eq_smul_of_coords | exact GlobalTheory.ModulusCoord.map_haar_eq_smul_of_coords | (intros; apply GlobalTheory.ModulusCoord.map_haar_eq_smul_of_coords <;> assumption)
