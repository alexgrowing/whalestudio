import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleContragredientSocle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericCommutationOfReorder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSmoothQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.StdQuot

section Theta

variable {k : Type} [Field k] {N : ℕ}

theorem thetaW_apply (g : GL (Fin N) k) (i j : Fin N) :
    (thetaW k N g).val i j = (g⁻¹).val (Fin.rev j) (Fin.rev i) := by
  simp [thetaW, invT, Matrix.reindexAlgEquiv_apply]

theorem thetaW_mem_unipB {u : GL (Fin N) k} (hu : u ∈ unipB k (Fin N)) : thetaW k N u ∈ unipB k (Fin N) := by
  have hi := (mem_unipB k).1 (inv_mem hu)
  refine (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [thetaW_apply]
    exact hi.1 _ _ (Fin.rev_lt_rev.2 hij)
  · rw [thetaW_apply]
    exact hi.2 _

theorem whitChar_thetaW (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    whitChar ψ N ⟨thetaW k N u, thetaW_mem_unipB u.2⟩ = whitChar ψ N u⁻¹ := by
  show Circle.toUnits (ψ _) = Circle.toUnits (ψ _)
  refine congrArg (fun s => Circle.toUnits (ψ s)) ?_
  refine Finset.sum_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1)) (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have h := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [Fin.val_rev]
    have := p.1.2
    have := p.2.2
    omega
  · intro p hp
    have h := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [Fin.val_rev]
    have := p.1.2
    have := p.2.2
    omega
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp only [thetaW_apply]
    rfl

theorem whitChar_inv (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    whitChar ψ⁻¹ N u = whitChar ψ N u⁻¹ := by
  rw [map_inv]
  show Circle.toUnits (ψ⁻¹ _) = (Circle.toUnits (ψ _))⁻¹
  rw [AddChar.inv_apply', map_inv]

end Theta

section Main

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {k}

variable (k)

end Main

end GlobalTheory.CompanionTheory.StdQuot

end
