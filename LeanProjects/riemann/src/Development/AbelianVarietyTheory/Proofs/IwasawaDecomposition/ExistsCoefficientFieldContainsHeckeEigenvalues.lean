import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameCfgRefl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteColumnConfigurationsWitnessesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAlgebraicSetHeckeFieldsSplitStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.HFld

theorem heckeFields_of (hF : ∀ (P : Pre) (f : Top.Fr P) (F F₀ : IntermediateField ℚ ℂ) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)),
  ∃ (n : ℕ) (Wt : Fin n → Σ B0 : Base, Σ px0 : PreX B0.toPre, Col2.ColIn B0 px0),
    (∀ i, (Wt i).1.fields.Ok ∧ (Wt i).2.2.Ok) ∧
    ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → B.toPre = P → HEq I.C f → B.KsC = F →
      B.fixedCoefficientFieldInComplex = F₀ → HEq (Set.range I.xi) Ξ → ∃ i, GlobalTheory.Mem.HFld.SameCfg B px I (Wt i).1 (Wt i).2.1 (Wt i).2.2) (hT : ∀ (B0 : Base) (px0 : PreX B0.toPre) (I0 : Col2.ColIn B0 px0), B0.fields.Ok → I0.Ok →
  ∃ s : Finset ℂ, (∀ z ∈ s, IsAlgebraic ℚ z) ∧
    ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → GlobalTheory.Mem.HFld.SameCfg B px I B0 px0 I0 →
      (∀ z ∈ s, z ∈ B.LLC) → ∀ a : I.ι,
        Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
          ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅) :
    ∃ So : ∀ P : Pre, Top.Fr P → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Set (Formalism.L2.Host.HChar P.host.E) → Finset ℂ,
  (∀ P f F F₀ Ξ, ∀ z ∈ So P f F F₀ Ξ, IsAlgebraic ℚ z) ∧
  ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok →
    (∀ z ∈ So B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi), z ∈ B.LLC) → ∀ a : I.ι,
      Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
        ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ := by
  classical
  choose n Wt hWok hWcov using hF
  choose s hsalg hs using hT
  refine ⟨fun P f F F₀ Ξ => Finset.univ.biUnion fun i : Fin (n P f F F₀ Ξ) =>
    s (Wt P f F F₀ Ξ i).1 (Wt P f F F₀ Ξ i).2.1 (Wt P f F F₀ Ξ i).2.2 (hWok P f F F₀ Ξ i).1 (hWok P f F F₀ Ξ i).2, ?_, ?_⟩
  · intro P f F F₀ Ξ z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
    exact hsalg _ _ _ _ _ z hi
  · intro B px I hB hI hS a
    obtain ⟨i, hi⟩ := hWcov B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi) B px I hB hI rfl HEq.rfl rfl rfl HEq.rfl
    exact hs _ _ _ _ _ B px I hB hI hi (fun z hz => hS z (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hz⟩)) a

theorem heckeFields :
    ∃ So : ∀ P : Pre, Top.Fr P → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Set (Formalism.L2.Host.HChar P.host.E) → Finset ℂ,
  (∀ P f F F₀ Ξ, ∀ z ∈ So P f F F₀ Ξ, IsAlgebraic ℚ z) ∧
  ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok →
    (∀ z ∈ So B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi), z ∈ B.LLC) → ∀ a : I.ι,
      Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
        ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ :=
  heckeFields_of GlobalTheory.T.exists_finite_columnConfigurations_witnesses GlobalTheory.T.exists_finite_algebraic_set_heckeFields_split

end GlobalTheory.Mem.HFld

end
