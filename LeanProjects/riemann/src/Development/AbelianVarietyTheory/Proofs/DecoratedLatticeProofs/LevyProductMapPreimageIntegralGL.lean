import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

namespace GlobalTheory.HaarR

theorem rootExchangeEmbedGL_mem_integralGL {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (c : ℕ) {g : GL n k} (hg : g ∈ KO k n) :
    embX c g ∈ KO k (n ⊕ Fin c) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have key : ∀ x : GL n k, (∀ i j, x.val i j ∈ 𝒪[k]) → ∀ i j, (embX c x).val i j ∈ 𝒪[k] := by
    intro x hx i j
    rw [GlobalTheory.RootEx.Radical.embX_val]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hx i j
    · simp
    · simp
    · simp only [fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨key g h1, ?_⟩
  rw [← map_inv]
  exact key _ h2

theorem prodR_preimage_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), prodR (k := k) (n := n) (c := c) p ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = (KO k n : Set (GL n k)) ×ˢ {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} := by
  intro k _ _ _ _ n _ _ c p
  ext ⟨g, u⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq, prodR_coe, Set.mem_prod, SetLike.mem_coe]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 h
    have hg : g ∈ KO k n := by
      refine (GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨fun i j => ?_, fun i j => ?_⟩
      · have e := GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul (c := c) g u.2
        have := h1 (Sum.inl i) (Sum.inl j)
        rw [← e]; exact this
      · have hu' : embX c g * ((u : GL (n ⊕ Fin c) k))⁻¹ * (embX c g)⁻¹ ∈ N k n c p :=
          GlobalTheory.RootEx.Radical.conj_mem g (inv_mem u.2)
        have e := GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul (c := c) g⁻¹ hu'
        have hinv : (embX c g * (u : GL (n ⊕ Fin c) k))⁻¹
            = embX c g⁻¹ * (embX c g * ((u : GL (n ⊕ Fin c) k))⁻¹ * (embX c g)⁻¹) := by
          rw [map_inv]; group
        have := h2 (Sum.inl i) (Sum.inl j)
        rw [hinv] at this
        rw [← e]
        exact this
    refine ⟨hg, ?_⟩
    have := mul_mem (inv_mem (rootExchangeEmbedGL_mem_integralGL c hg)) h
    rwa [inv_mul_cancel_left] at this
  · rintro ⟨hg, hu⟩
    exact mul_mem (rootExchangeEmbedGL_mem_integralGL c hg) hu

end GlobalTheory.HaarR
