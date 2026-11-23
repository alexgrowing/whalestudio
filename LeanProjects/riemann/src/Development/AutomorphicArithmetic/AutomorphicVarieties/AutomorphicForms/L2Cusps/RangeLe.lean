import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.DenseHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.CmpForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsCuspidalOfConstantTermEqZero

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.rangeLe_holds :
    UpperTheory.V.KernelIndexFullLattice.RangeLe := by
  intro E _ _ _ a μ _ μ₁ _ hp v
  have hv : v ∈ ((centralCuspForms E a).map (cuspVecL μ₁)).topologicalClosure := by
    rw [UpperTheory.V.KernelIndexFullLattice.dense_holds E a μ₁]; trivial
  have hcl : IsClosed (UpperTheory.V.KernelIndexFullLattice.cmp hp ⁻¹' (L2cusp μ : Set (L2 (latticeGL E a) μ))) :=
    (Submodule.isClosed_topologicalClosure _).preimage (UpperTheory.V.KernelIndexFullLattice.cmp hp).continuous
  refine closure_minimal ?_ hcl hv
  rintro _ ⟨φ, hφ, rfl⟩
  have hc : Continuous φ.1 := φ.2.1.continuous
  have hl : IsLeftInvariant φ.1 := φ.2.1.isLeftInvariant
  refine Submodule.le_topologicalClosure _ ⟨φ.1, mem_cuspCont.2 ⟨hc, fun γ g => hl γ g, fun t g => ?_,
    UpperTheory.isCuspidal_of_constantTerm_eq_zero E a φ.1 hl hc φ.2.2⟩, UpperTheory.V.KernelIndexFullLattice.cmpForm_holds E a μ μ₁ hp φ hφ⟩
  rw [splitCentre_comm, UpperTheory.V.KernelIndexFullLattice.splitEq_holds]
  exact apply_mul_centralSection_of_mem hφ _ _
