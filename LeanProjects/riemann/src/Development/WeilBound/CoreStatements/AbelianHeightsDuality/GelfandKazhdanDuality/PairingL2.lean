import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open scoped InnerProductSpace

namespace PositivityTheory.PRW.GKD

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_haar_GA : ∃ μ : Measure (GA E a), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩

theorem memL2_normalised_cusp_form (hB : GlobalTheory.Published.CuspFormsBoundedGL) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    {π : CuspSub E a} (hπ : IsNormalised π) : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1 := by
  intro φ hφ
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h := π.cusp φ hφ
  obtain ⟨C, hC⟩ := hB E a φ h fun t g => by rw [hπ φ hφ t g]
  exact GlobalTheory.CuspQuot.memL2_of_bound (ContAut.continuous_of_isOpen_stab E a φ h.1.level)
    (leftInv_latticeGL h.1.left (hπ φ hφ)) hC

theorem continuous_of_mem {π : CuspSub E a} : ∀ φ ∈ π.V, Continuous φ.1 := fun φ hφ =>
  ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level

theorem inner_R (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : GA E a)
    (F F' : L2 (latticeGL E a) μ) :
    ⟪R (latticeGL E a) μ g F, R (latticeGL E a) μ g F'⟫_ℂ = ⟪F, F'⟫_ℂ :=
  LinearIsometry.inner_map_map
    { toLinearMap := (R (latticeGL E a) μ g : L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ).toLinearMap
      norm_map' := norm_R g } F F'

end PositivityTheory.PRW.GKD

end
