import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitIndex

theorem rStab_index_ne_zero_of_compact : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G) (d : G) (f : G → ℂ),
  Continuous θ → IsCompact (K : Set G) → IsOpen (K' : Set G) → (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) →
  ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0 := by
  intro G _ _ _ θ K K' d f hθ hKc ho hf y
  set W : Subgroup G := K' ⊓ K'.comap θ with hW
  have hWo : IsOpen (W : Set G) := by
    rw [hW, Subgroup.coe_inf]
    exact ho.inter (ho.preimage hθ)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hWo' : IsOpen ((W.subgroupOf K : Subgroup K) : Set K) :=
    hWo.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hWo'
  haveI : (W.subgroupOf K).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hle : W.subgroupOf K ≤ rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k)) := by
    intro k' hk' k
    have hk'W : (k' : G) ∈ W := Subgroup.mem_subgroupOf.mp hk'
    have hl : (k' : G)⁻¹ ∈ K' := K'.inv_mem hk'W.1
    have hr : θ (k' : G) ∈ K' := hk'W.2
    have e : (y * ((k * k' : K) : G))⁻¹ * d * θ (y * ((k * k' : K) : G)) =
        (k' : G)⁻¹ * (((y * (k : G))⁻¹ * d * θ (y * (k : G))) * θ (k' : G)) := by
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    show f _ = f _
    rw [e, (hf _ hl _).1, (hf _ hr _).2]
  exact (Subgroup.finiteIndex_of_le hle).index_ne_zero

end GlobalTheory.CompanionTheory.SplitIndex
