import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualStdModelField
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

namespace StandardDualFibreRatios

theorem nonempty_of_basis {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) (hi : 1 ≤ i) : Nonempty T := by
  by_contra hT
  rw [not_nonempty_iff] at hT
  have h := DualArithmeticVariety.span_basis (K := K) b
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  have h1 : (Pi.single (⟨0, hi⟩ : Fin i) 1 : Fin i → K) ∈ (⊥ : Submodule K (Fin i → K)) := h ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at h1
  have h2 := congrFun h1 ⟨0, hi⟩
  simp at h2

end StandardDualFibreRatios

open StandardDualFibreRatios in

theorem DualStdFibreRatios.proof (hTr : GenFibreModelTransport.Statement) (hMod : DualStdGraphModel.Statement)
    (hRk : DualStdModelRank.Statement) (hTc : DualStdModelTransc.Statement) : DualStdFibreRatios.Statement := by
  intro K _ _ i T _ _ b G hi
  obtain ⟨c⟩ := nonempty_of_basis b hi
  let Φ₀ : Subfield (dualStdModelField K i) :=
    Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i)))
  have hΦ₀ : (algebraMap Φ₀ (dualStdModelField K i)).fieldRange = Φ₀ := Subfield.fieldRange_subtype _
  obtain ⟨h0, hrk, htr⟩ := hTr Unit (PBlk i) (Unit ⊕ Unit) (Sum.elim (dualBlocks T) (PBlk i))
    (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
    (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) G (dualStdModelField K i)
    (dualStdModelPt b) (hMod K i T b) Φ₀ hΦ₀ T
    (fun t => (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))
    (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)
  obtain ⟨hz, hrk₀⟩ := hRk K i T b Φ₀ hΦ₀ hi c
  refine ⟨c, fun h => hz (h0.mp h), ?_, ?_⟩
  · exact hrk.trans hrk₀
  · exact htr.mpr (hTc K i T b Φ₀ hΦ₀ hi c)

end GroundTheory.Heights₂.Heights
