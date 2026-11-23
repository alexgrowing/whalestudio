import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

namespace GlobalTheory.TransportLemma

theorem transport {V : Type} [AddCommGroup V] [Module ℂ V] [DecidableEq V] (T : V ≃+ V)
    {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V}
    (hS : Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S)
    (h₁ : ∀ x : V, (T : V → V) x ∈ M₁ ↔ x ∈ Λ₁)
    (h₂ : ∀ x : V, (T : V → V) x ∈ M₂ ↔ x ∈ Λ₂) :
    Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → V) S) := by
  obtain ⟨hmem, hinj, hcov⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact (h₂ s).mpr (hmem s hs)
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have h : (T : V → V) (s - t) ∈ M₁ := by
      rw [map_sub]; exact hxy
    rw [hinj s hs t ht ((h₁ _).mp h)]
  · intro y hy
    have hy' : T.symm y ∈ Λ₂ := (h₂ _).mp (by simpa using hy)
    obtain ⟨s, hs, hd⟩ := hcov _ hy'
    refine ⟨(T : V → V) s, Finset.mem_image_of_mem _ hs, ?_⟩
    have h : (T : V → V) (T.symm y - s) ∈ M₁ := (h₁ _).mpr hd
    rw [map_sub] at h
    simpa using h

theorem main : ∀ {V : Type} [inst : AddCommGroup V] [Module ℂ V] [inst_2 : DecidableEq V] (T : V ≃+ V) {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V}, Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S → (∀ (x : V), (T : V → V) x ∈ M₁ ↔ x ∈ Λ₁) → (∀ (x : V), (T : V → V) x ∈ M₂ ↔ x ∈ Λ₂) → Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → V) S) :=
  @transport

end GlobalTheory.TransportLemma
