import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreExtra
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.PHorizNotMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace RegularityRelativeClosedPoint

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq K]

def killBlocks (S : Finset K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval fun p => if p.1 ∈ S then 0 else X p

theorem killBlocks_form (S : Finset K) {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) :
    killBlocks S g = (∏ k, (if k ∈ S then (0 : MRing ι) else 1) ^ a k) * g := by
  have e : (fun p : (Σ k, ι k) => if p.1 ∈ S then (0 : MRing ι) else X p) =
      fun p => (if p.1 ∈ S then (0 : MRing ι) else 1) * X p := by
    funext p
    split_ifs <;> simp
  have h := regularityLocalResidue_holds.aeval_blockScale_int hg (fun k => if k ∈ S then (0 : MRing ι) else 1) X
  rw [aeval_X_left_apply] at h
  rw [killBlocks, e]
  exact h

theorem le_comap_killBlocks (S : Finset K) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W) :
    W ≤ W.comap (killBlocks S) := by
  obtain ⟨T, hT, rfl⟩ := hW
  rw [Ideal.span_le]
  intro g hg
  obtain ⟨a, ha⟩ := hT g hg
  rw [SetLike.mem_coe, Ideal.mem_comap, killBlocks_form S ha]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span hg)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem killBlocks_comp {S T : Finset K} (hST : S ⊆ T) :
    (killBlocks T).comp (killBlocks S) = (killBlocks T : MRing ι →ₐ[ℤ] MRing ι) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  simp only [AlgHom.comp_apply, killBlocks, aeval_X]
  by_cases h : p.1 ∈ S
  · simp [h, hST h]
  · simp [h]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem killBlocks_empty : (killBlocks ∅ : MRing ι →ₐ[ℤ] MRing ι) = AlgHom.id ℤ (MRing ι) :=
  MvPolynomial.algHom_ext fun p => by simp [killBlocks]

theorem card_le_ringKrullDim (W : Ideal (MRing ι)) [W.IsPrime] (hWh : IsMultiHomogIdeal W)
    (hWr : IsRelevant W) : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ W) := by
  choose j hj using hWr
  let Q : Finset K → Ideal (MRing ι) := fun S => W.comap (killBlocks S)
  have hQp : ∀ S, (Q S).IsPrime := fun S => Ideal.comap_isPrime _ _
  have hstep : ∀ S k, k ∉ S → Q S < Q (insert k S) := by
    intro S k hk
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun g hg => ?_, X ⟨k, j k⟩, ?_, ?_⟩
    · have h1 := Ideal.mem_comap.mp (le_comap_killBlocks (insert k S) hWh (Ideal.mem_comap.mp hg))
      rw [← AlgHom.comp_apply, killBlocks_comp (Finset.subset_insert k S)] at h1
      exact Ideal.mem_comap.mpr h1
    · rw [Ideal.mem_comap]
      simp [killBlocks]
    · intro h
      rw [Ideal.mem_comap] at h
      simp only [killBlocks, aeval_X, if_neg hk] at h
      exact hj k h
  have chain : ∀ S : Finset K, (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) ≤
      ringKrullDim (MRing ι ⧸ Q ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih =>
      have : (Q S).IsPrime := hQp S
      have : (Q (insert k S)).IsPrime := hQp _
      have h1 := HorizNotMem.ringKrullDim_quotient_add_one_le (hstep S k hk)
      rw [Finset.card_insert_of_notMem hk]
      calc (((S.card + 1 : ℕ)) : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q (insert k S))
          = (S.card : WithBot ℕ∞) + (ringKrullDim (MRing ι ⧸ Q (insert k S)) + 1) := by
            push_cast; abel
        _ ≤ (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) := by gcongr
        _ ≤ _ := ih
  have hQ0 : Q ∅ = W := by
    ext g
    simp [Q, killBlocks_empty]
  have : (Q Finset.univ).IsPrime := hQp _
  have : IsDomain (MRing ι ⧸ Q Finset.univ) := Ideal.Quotient.isDomain _
  have h3 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ Q Finset.univ) := ringKrullDim_nonneg_of_nontrivial
  have hc := chain Finset.univ
  rw [Finset.card_univ, hQ0] at hc
  calc ((Fintype.card K : ℕ) : WithBot ℕ∞) = (Fintype.card K : WithBot ℕ∞) + 0 := (add_zero _).symm
    _ ≤ (Fintype.card K : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q Finset.univ) := by gcongr
    _ ≤ _ := hc

end RegularityRelativeClosedPoint

theorem RegularityRelativeClosedPoint.proof : RegularityRelativeClosedPoint.Statement := by
  intro K _ ι _ P W hP hW hPW hne
  classical
  refine ⟨hW, ?_⟩
  obtain ⟨-, ⟨hPp, -, -⟩, -, hPdim⟩ := hP
  obtain ⟨hWp, hWh, hWr⟩ := hW
  have := hPp
  have := hWp
  have e := mvPolynomialInt_dimFormula P W hPW
  rw [hPdim] at e
  have hh : (W.map (Ideal.Quotient.mk P)).height ≠ 0 := fun h0 =>
    hne (le_antisymm (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0) hPW)
  have hlow := RegularityRelativeClosedPoint.card_le_ringKrullDim W hWh hWr
  generalize ringKrullDim (MRing ι ⧸ W) = m at e hlow ⊢
  generalize (W.map (Ideal.Quotient.mk P)).height = h at e hh
  induction m using WithBot.recBotCoe with
  | bot => exact absurd hlow (by simp)
  | coe m =>
    have e' : m + h = ((1 + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast e
    have hlow' : ((Fintype.card K : ℕ) : ℕ∞) ≤ m := by exact_mod_cast hlow
    induction m using ENat.recTopCoe with
    | top => simp at e'; exact absurd e'.symm (ENat.natCast_ne_top _)
    | coe m =>
      induction h using ENat.recTopCoe with
      | top => simp at e'; exact absurd e'.symm (ENat.natCast_ne_top _)
      | coe h =>
        have h1 : m + h = 1 + Fintype.card K := by exact_mod_cast e'
        have h2 : Fintype.card K ≤ m := by exact_mod_cast hlow'
        have h3 : h ≠ 0 := by exact_mod_cast hh
        have h4 : m = Fintype.card K := by omega
        rw [h4]
        rfl

end

end GroundTheory.Heights₂.Heights.Inter
