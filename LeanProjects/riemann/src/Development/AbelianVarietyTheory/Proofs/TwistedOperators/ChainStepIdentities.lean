import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableSetPreSingleton
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainStepIdentities

theorem volAdd_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (r : ℕ) :
    volAdd ν r = ∏ i ∈ Finset.Icc 1 r, (zetaAt (resCard k) i)⁻¹ := by
  have := hν.1
  have h := GlobalTheory.IndexVolume.volumeOfGL ν hν.2 (Fin r)
  have hS : (Units.val '' (KO k (Fin r) : Set (GL (Fin r) k)) : Set (Matrix (Fin r) (Fin r) k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.groupSet (⊤ : Subgroup (GL (Fin r) 𝒪[k])) := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, trivial, rfl⟩
    · rintro ⟨g, -, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, rfl⟩
  have e : volAdd ν r = GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.volGroup ν (⊤ : Subgroup (GL (Fin r) 𝒪[k])) := by
    unfold volAdd GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.volGroup
    rw [hS]
    rfl
  rw [e, h, Fintype.card_fin, Formalism.MainNotions.ZetaProductPairs.qE]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [zetaAt, GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.resCard, resCard, _root_.zpow_neg, _root_.zpow_natCast]

end GlobalTheory.ChainStepIdentities
