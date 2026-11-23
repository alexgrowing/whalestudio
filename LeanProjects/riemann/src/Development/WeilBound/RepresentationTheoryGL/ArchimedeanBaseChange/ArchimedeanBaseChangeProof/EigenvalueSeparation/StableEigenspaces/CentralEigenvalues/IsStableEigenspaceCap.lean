import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteLeOfClosureClasses
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAut
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.E.E3

namespace centeig

theorem isStable_eigenspace_cap {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (τ : E →+* ℂ)
    (u c : ℂ) : IsStable (Module.End.eigenspace (cap (a := N) τ u) c) := by
  intro o φ hφ
  rw [Module.End.mem_eigenspace_iff] at hφ ⊢
  rw [← Module.End.mul_apply, (GlobalTheory.SpehInfChar.cap_commute_act τ u o).eq, Module.End.mul_apply, hφ, map_smul]

theorem isStable_autSub {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} :
    IsStable (GlobalTheory.DiscClosure.autSub E N) := by
  intro o φ hφ
  exact PositivityTheory.Rg.Rs.PrAut.isAutForm_act PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL o hφ

end centeig

theorem hullaut_holds : HullAut := by
  intro E _ _ _ N S hS
  refine ⟨fun φ hφ => ?_, fun τ m hm => ⟨hm.1, fun u φ hφ => ?_⟩⟩
  · have hle : hull S ≤ GlobalTheory.DiscClosure.autSub E N := sInf_le ⟨fun ψ h => hS ψ h, centeig.isStable_autSub⟩
    exact hle hφ
  · have hle : hull S ≤ Module.End.eigenspace (cap (a := N) τ u) ((m.map (u + ·)).prod) :=
      sInf_le ⟨fun ψ h => Module.End.mem_eigenspace_iff.2 (hm.2 u ψ (Submodule.subset_span h)),
        centeig.isStable_eigenspace_cap τ u _⟩
    exact Module.End.mem_eigenspace_iff.1 (hle hφ)

end PositivityTheory.Rg.BcB.E.E3

end
