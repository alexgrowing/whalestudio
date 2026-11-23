import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem IsSncChart.neg_one_lt_formOrd_sub_sum : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (E : DivOver q), E.Through y → ∀ a : Fin n → ℚ, ((∀ j ∈ J, a j < 1) → -1 < (E.formOrd (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) ∧ ((∀ j ∈ J, a j ≤ 1) → -1 ≤ (E.formOrd (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) := by
  intro k _ _ Y _ _ q n _ B y U hy z J w u hc E hE a
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen k _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)
  have h0 : formOf U (gen_mem hy) (dOn q z) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy) hc.frame).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have hnn : ∀ j ∈ J, 0 ≤ E.ord (u j) := fun j hj =>
    (E.ord_nonneg_iff _).2 (by rw [hc.val j hj]; exact hE _ (regAt_fnOf hy _ (z j)))
  have hA := DivOver.sum_ord_sub_one_le_formOrd_dOn hn E hy hE z h0 (J := {j // j ∈ J})
    Subtype.val Subtype.val_injective (fun j => u j.1) fun j => hc.val j.1 j.2
  rw [Finset.sum_coe_sort J (fun j => E.ord (u j))] at hA
  have hF := DivOver.formOrd_formOf_nonneg hn hy hE (dOn q z) h0
  set F := E.formOrd (formOf U (gen_mem hy) (dOn q z))
  have hAq : ∑ j ∈ J, (E.ord (u j) : ℚ) - 1 ≤ F := by exact_mod_cast hA
  have hFq : (0 : ℚ) ≤ F := by exact_mod_cast hF
  have hnq : ∀ j ∈ J, (0 : ℚ) ≤ E.ord (u j) := fun j hj => by exact_mod_cast hnn j hj
  have hle : (∀ j ∈ J, a j ≤ 1) → ∀ j ∈ J, a j * (E.ord (u j) : ℚ) ≤ E.ord (u j) :=
    fun ha j hj => by nlinarith [ha j hj, hnq j hj]
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · by_cases hz : ∀ j ∈ J, (E.ord (u j) : ℚ) = 0
    · rw [Finset.sum_eq_zero fun j hj => by rw [hz j hj, mul_zero]]
      linarith
    · push Not at hz
      obtain ⟨j, hj, hj0⟩ := hz
      have hpos : (0 : ℚ) < E.ord (u j) := lt_of_le_of_ne (hnq j hj) hj0.symm
      have := Finset.sum_lt_sum (hle fun j hj => (ha j hj).le)
        ⟨j, hj, by nlinarith [ha j hj]⟩
      linarith
  · have := Finset.sum_le_sum (hle ha)
    linarith

end GlobalTheory.Discrepancy
