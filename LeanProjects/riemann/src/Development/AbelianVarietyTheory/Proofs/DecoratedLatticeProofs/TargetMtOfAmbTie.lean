import Mathlib
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStep
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLatticeMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmLevelHermitianIntegralStatement
open Module NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.AmbTieStep

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem posAt_of_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K)
    (h : (H.map v.embedding).PosDef) : PosAt H v := by
  refine ⟨fun x y => ?_, fun x hx => ?_⟩
  · simp only [hAt, star_sum, star_mul', star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := h.1.apply i j
    simp only [Matrix.map_apply] at this
    rw [← this, star_star]
    ring
  · rw [hAt_eq_dot]
    have hx' : (fun i => v.embedding (x i)) ≠ 0 := by
      intro h0
      apply hx
      funext i
      have := congrFun h0 i
      simpa using this
    exact (Complex.pos_iff.1 (h.dotProduct_mulVec_pos hx')).1

theorem hAt_single {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (i j : Fin n) :
    hAt H v (Pi.single i 1) (Pi.single j 1) = v.embedding (H i j) := by
  simp [hAt, Pi.single_apply]

end GlobalTheory.Core.AmbTieStep

theorem GlobalTheory.Core.target_Mt_of_ambTie : ∀ (D : D7) (Gp : Type) [Group Gp] [Fintype Gp] (Pl0 Tu : Type) (m : ℕ) (A : FamIn D.what₂.LL Gp Pl0 Tu m) (Am : AmbForm D (RowSide.sharp D)) (P : Subgroup Gp) (ψ : P →* D.what₂.LLˣ) (tup : Tu → D.what₂.Tup) (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] (RowSide.sharp D).Amb (tup t)) (J : AmbIds D A (RowSide.sharp D) Am P ψ tup), AmbTie D A (RowSide.sharp D) Am P ψ tup jA J → ∀ t : Tu, tup t = D.what₂.mu0 → (A.fam.R t).S.Good 1 → (∀ i j, (A.fam.R t).S.H i j ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ v : InfinitePlace D.what₂.LL, ((A.fam.R t).S.H.map v.embedding).PosDef) → (A.fam.R t).S.ActGood (A.fam.R t).r → (A.fam.R t).S.ActRat (A.fam.R t).r → GlobalTheory.Core.Target (GlobalTheory.Core.Rk.Mt D Am) := by
  intro D Gp _ _ Pl0 Tu m A Am P ψ tup jA J hT t ht hG hcm hpos hAG hAR
  obtain ⟨v0, hv0⟩ := GlobalTheory.isConjAt_exists_main D.what₂.LL ⟨D.what₂.embLL, D.starLL_cx⟩
  have hL := GlobalTheory.T.cm_level_hermitian_integral D.what₂.LL v0 hv0 (A.fam.R t).S hG hcm hpos Gp (A.fam.R t).r hAG hAR
    (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ
  have hU : DV.Used D (tup t) := Or.inl ht
  have key : GlobalTheory.Core.Target (Am.MtH (tup t)) := by
    intro hr
    refine GlobalTheory.T.muMaxDual_nonpos_of_dual_le D.what₂.LL (Formalism.DivisionValues.cmMax D.what₂.LL) (isCMSub_cmMax' D.what₂.LL) v0 hv0 (Am.MtH (tup t)) _
      (rH D A P ψ t) (J.eA t hU) (rNab D A P ψ t) (Am.MtH_good _ hU) hr hL.1 ?_ (hT.lat t hU) hL.2.2
    intro v i j
    rw [hT.metric t hU v (GlobalTheory.Core.AmbTieStep.posAt_of_posDef _ v (hL.2.1 v)), GlobalTheory.Core.AmbTieStep.hAt_single]
  show GlobalTheory.Core.Target (Am.MtH D.what₂.mu0)
  rw [← ht]
  exact key
