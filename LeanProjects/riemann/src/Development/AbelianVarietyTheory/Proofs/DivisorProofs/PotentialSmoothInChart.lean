import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ContDiff Topology

namespace GlobalTheory

theorem isPotential_contDiffAt_compatChart {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ)
    (z : Fin e → ℂ) (hz : z ∈ ψ.target) :
    ContDiffAt ℝ ∞ (P.φ (ψ.symm z) ∘ ψ.symm) z := by
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have h2 : ContDiffAt ℝ ∞ (A.chart j ∘ ψ.symm) z :=
    (((hψ j).2 z ⟨hz, hj⟩).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U (ψ.symm z)) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U _)
  have hmem : (A.chart j ∘ ψ.symm) z ∈
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U (ψ.symm z) := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Function.comp_apply, Set.mem_preimage, (A.chart j).left_inv hj]
    exact P.mem_U _
  have h1 : ContDiffAt ℝ ∞ (P.φ (ψ.symm z) ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z) :=
    (hP.1 (ψ.symm z) j).contDiffAt (hopen.mem_nhds hmem)
  refine (h1.comp z h2).congr_of_eventuallyEq ?_
  have hev : ∀ᶠ y in 𝓝 z, ψ.symm y ∈ (A.chart j).source :=
    (ψ.continuousAt_symm hz).eventually ((A.chart j).open_source.mem_nhds hj)
  filter_upwards [hev] with y hy
  simp only [Function.comp_apply, (A.chart j).left_inv hy]

end GlobalTheory
