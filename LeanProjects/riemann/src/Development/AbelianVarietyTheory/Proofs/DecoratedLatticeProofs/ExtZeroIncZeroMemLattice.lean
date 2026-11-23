import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZeroAt

variable {D : D7}

theorem mulVec_idAt {m n : ℕ} (M : Mx D m n) {P : Pl D → Prop} {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D P) :
    ∀ i, (M *ᵥ y) i ∈ idAt D P := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem wittProjectionZero_mem_latticeCompletion_of_splits {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {P : Pl D → Prop}
    (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, P v → MonoAt d L L₀ v) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : d.p0 *ᵥ y ∈ latV S₀ L₀ P := by
  refine (GlobalTheory.FinPlLoc.part_lat P S₀ L₀ _ hL₀).2 ⟨mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hm v hv _).1 (GlobalTheory.FinPlLoc.smul_latV v he hy)).2.2

theorem wittCoreInclusion_mem_latticeCompletionAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {P : Pl D → Prop}
    (hL : Submodule.IsLattice D.host.E L) (hm : ∀ v, P v → MonoAt d L L₀ v) {u : Fin T₀.rank → AE D}
    (hu : u ∈ latV T₀ L₀ P) : d.j0 *ᵥ u ∈ latV T L P := by
  refine (GlobalTheory.FinPlLoc.part_lat P T L _ hL).2 ⟨mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hu), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact GlobalTheory.FinPl.VacFlat.wittCoreInclusion_mem_latticeCompletionAtPlace d (hm v hv) (GlobalTheory.FinPlLoc.smul_latV v he hu)

end GlobalTheory.FinPl.ExtZeroAt
