import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableSetPreSingleton
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.BlockVolume

variable {k : Type} [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν]

def rowSplit (A D : Type) [Fintype A] [Fintype D] :
    ((A ⊕ D) → k) ≃ᵐ ((A → k) × (D → k)) :=
  MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ D => k)

theorem rowSplit_mp (A D : Type) [Fintype A] [Fintype D] :
    MeasurePreserving (rowSplit (k := k) A D) (Measure.pi fun _ : A ⊕ D => ν)
      ((Measure.pi fun _ : A => ν).prod (Measure.pi fun _ : D => ν)) :=
  measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ D => ν)

def colSplit (R A D : Type) [Fintype R] [Fintype A] [Fintype D] :
    (R → (A ⊕ D) → k) ≃ᵐ ((R → A → k) × (R → D → k)) :=
  (MeasurableEquiv.piCongrRight fun _ : R => rowSplit (k := k) A D).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (A → k) (D → k) R)

theorem colSplit_mp (R A D : Type) [Fintype R] [Fintype A] [Fintype D] :
    MeasurePreserving (colSplit (k := k) R A D)
      (Measure.pi fun _ : R => Measure.pi fun _ : A ⊕ D => ν)
      ((Measure.pi fun _ : R => Measure.pi fun _ : A => ν).prod
        (Measure.pi fun _ : R => Measure.pi fun _ : D => ν)) := by
  have h1 := measurePreserving_pi (fun _ : R => Measure.pi fun _ : A ⊕ D => ν)
    (fun _ : R => (Measure.pi fun _ : A => ν).prod (Measure.pi fun _ : D => ν))
    (fun _ => rowSplit_mp ν A D)
  have h2 := measurePreserving_arrowProdEquivProdArrow (A → k) (D → k) R
    (fun _ => Measure.pi fun _ : A => ν) (fun _ => Measure.pi fun _ : D => ν)
  exact h2.comp h1

def blockSplit (A D : Type) [Fintype A] [Fintype D] :
    ((A ⊕ D) → (A ⊕ D) → k) ≃ᵐ (((A → A → k) × (A → D → k)) × ((D → A → k) × (D → D → k))) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ D => (A ⊕ D) → k)).trans
    (MeasurableEquiv.prodCongr (colSplit A A D) (colSplit D A D))

def blockEquiv (A D : Type) [Fintype A] [Fintype D] :
    Matrix (A ⊕ D) (A ⊕ D) k ≃ᵐ ((Matrix A A k × Matrix A D k) × (Matrix D A k × Matrix D D k)) :=
  blockSplit (k := k) A D

theorem blockSplit_mp (A D : Type) [Fintype A] [Fintype D] :
    MeasurePreserving (blockEquiv (k := k) A D) (volM ν (A ⊕ D) (A ⊕ D))
      (((volM ν A A).prod (volM ν A D)).prod ((volM ν D A).prod (volM ν D D))) := by
  have h1 := measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ D => Measure.pi fun _ : A ⊕ D => ν)
  have h2 := (colSplit_mp ν A A D).prod (colSplit_mp ν D A D)
  exact h2.comp h1

end GlobalTheory.BlockVolume

theorem GlobalTheory.blockVolume_prod : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (A D : Type) [Fintype A] [Fintype D] (S₁₁ : Set (Matrix A A k)) (S₁₂ : Set (Matrix A D k))
    (S₂₁ : Set (Matrix D A k)) (S₂₂ : Set (Matrix D D k)),
    volM ν (A ⊕ D) (A ⊕ D)
        {x | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧ x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      volM ν A A S₁₁ * volM ν A D S₁₂ * volM ν D A S₂₁ * volM ν D D S₂₂ := by
  intro k _ _ _ _ _ _ ν _ A D _ _ S₁₁ S₁₂ S₂₁ S₂₂
  haveI := GlobalTheory.IndexVolume.secondCountable k
  haveI : SigmaFinite ν := inferInstance
  haveI hσ : ∀ (m n : Type) [Fintype m] [Fintype n], SigmaFinite (volM ν m n) := fun m n _ _ => by
    exact (inferInstance : SigmaFinite (Measure.pi fun _ : m => Measure.pi fun _ : n => ν :
      Measure (m → n → k)))
  haveI := hσ A A; haveI := hσ A D; haveI := hσ D A; haveI := hσ D D
  have hmp := GlobalTheory.BlockVolume.blockSplit_mp ν A D
  have hset : {x : Matrix (A ⊕ D) (A ⊕ D) k | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧
      x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      GlobalTheory.BlockVolume.blockEquiv (k := k) A D ⁻¹' ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂)) := by
    ext x
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [hset]
  have h := hmp.measure_preimage_equiv ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂))
  refine h.trans ?_
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  ring
