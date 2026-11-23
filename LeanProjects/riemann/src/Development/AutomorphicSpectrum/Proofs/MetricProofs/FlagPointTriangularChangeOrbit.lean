import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

private theorem sum_eq_sum_orderEmbOfFin_of_zero_off {N : ℕ} (S : Finset (Fin N)) (F : Fin N → ℂ)
    (hz : ∀ a, a ∉ S → F a = 0) :
    ∑ a, F a = ∑ z : Fin S.card, F (S.orderEmbOfFin rfl z) := by
  calc ∑ a, F a = ∑ a ∈ S, F a :=
        (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hz a ha)).symm
    _ = ∑ i : S, F i := (Finset.sum_coe_sort S F).symm
    _ = ∑ z : Fin S.card, F (S.orderEmbOfFin rfl z) :=
        (Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _
          (fun z => by simp [Finset.coe_orderIsoOfFin_apply])).symm

private theorem minorIJ_mul_of_block {N : ℕ} (h B : Matrix (Fin N) (Fin N) ℂ) (S I : Finset (Fin N))
    (hB : ∀ a c, c ∈ S → a ∉ S → B a c = 0) :
    minorIJ (h * B) I S = minorIJ h I S * minorIJ B S S := by
  unfold minorIJ
  by_cases e : I.card = S.card
  · rw [dif_pos e, dif_pos e, dif_pos rfl, ← Matrix.det_mul]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    exact sum_eq_sum_orderEmbOfFin_of_zero_off S (fun a => h (I.orderEmbOfFin e x) a * B a (S.orderEmbOfFin rfl y))
      (fun a ha => by rw [hB a _ (Finset.orderEmbOfFin_mem S rfl y) ha, mul_zero])
  · rw [dif_neg e, dif_neg e, zero_mul]

private theorem apply_eq_zero_of_mem_stepCols_not_mem {N j : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (hd : IsBlockDiag j B) (ht : B.BlockTriangular id) :
    ∀ a c, c ∈ stepCols N j i → a ∉ stepCols N j i → B a c = 0 := by
  intro a c hc ha
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc ha
  have hi := i.isLt
  by_cases hblk : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)
  · apply ht
    show c < a
    rw [Fin.lt_def]
    split_ifs at hc ha <;> omega
  · exact hd a c hblk

private theorem minorIJ_ne_zero_of_blockTriangular {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (ht : B.BlockTriangular id) (hdet : B.det ≠ 0) : minorIJ B S S ≠ 0 := by
  unfold minorIJ
  rw [dif_pos rfl]
  have hdiag : ∀ a, B a a ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular ht] at hdet
    exact fun a => (Finset.prod_ne_zero_iff.mp hdet) a (Finset.mem_univ a)
  have htS : (B.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)).BlockTriangular id :=
    fun x y hxy => ht ((S.orderEmbOfFin rfl).strictMono hxy)
  rw [Matrix.det_of_isUpperTriangular htS]
  exact Finset.prod_ne_zero_iff.mpr (fun z _ => hdiag _)

theorem sameOrbit_flagPt_mul : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h B : Ψ → Matrix (Fin N) (Fin N) ℂ), (∀ τ', IsBlockDiag j (B τ') ∧ (B τ').BlockTriangular id ∧ (B τ').det ≠ 0) → SameOrbit (FC.flagPt M F b fun τ' => h τ' * B τ') (FC.flagPt M F b h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b h B hB
  refine Exists.intro (fun k => if hk : ∀ p, M.blk p ≠ some k then (1 : ℂ) else
    minorIJ (B (not_forall.1 hk).choose.1) (stepCols N j (not_forall.1 hk).choose.2)
      (stepCols N j (not_forall.1 hk).choose.2)) ⟨fun k => ?_, ?_⟩
  · dsimp only
    split_ifs with hk
    · exact one_ne_zero
    · generalize (not_forall.1 hk).choose = p
      exact minorIJ_ne_zero_of_blockTriangular (B p.1) (stepCols N j p.2) (hB p.1).2.1 (hB p.1).2.2
  · funext q
    simp only [flagPt]
    split_ifs with hk
    · rw [one_mul]
    · generalize (not_forall.1 hk).choose = p
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun I _ => ?_)
      rw [minorIJ_mul_of_block (h p.1) (B p.1) (stepCols N j p.2) I
        (apply_eq_zero_of_mem_stepCols_not_mem (B p.1) p.2 (hB p.1).1 (hB p.1).2.1)]
      ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
