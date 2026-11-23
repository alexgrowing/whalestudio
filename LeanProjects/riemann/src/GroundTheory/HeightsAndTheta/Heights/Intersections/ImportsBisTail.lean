import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtraAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerBis
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerSide
import GroundTheory.HeightsAndTheta.Heights.Intersections.XcNotMemOfIsRelevant
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem VerticalEmbedding.proof (hD : regularityDehomogenization_holds.Statement) (hC : regularityLocalCardinality_holds.Statement) (hL : RegularityLocalProduct.Statement) :
    VerticalEmbedding.Statement := by
  classical
  intro K _ ι _ P f g a x hP hf hg hfP hgP hx
  have : P.IsPrime := hP.2.1.1

  let t : Ideal (MRing ι) → MRing ι := fun W =>
    if h : IsRelevant W then ∏ k, (X ⟨k, (h k).choose⟩ : MRing ι) ^ a k else 1
  have ht : ∀ W : Ideal (MRing ι), W.IsPrime → IsRelevant W → IsMultiHomog (t W) a ∧ t W ∉ W := by
    intro W hWp hW
    simp only [t, dif_pos hW]
    refine ⟨AvoidRing.isMultiHomog_coordProd _ _, fun hmem => ?_⟩
    obtain ⟨k, -, hk⟩ := hWp.prod_mem_iff.mp hmem
    exact (hW k).choose_spec (hWp.mem_of_pow_mem _ hk)
  have hne : ∀ W : Ideal (MRing ι), P ≤ W → t W ∉ W →
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) ≠ 0 := by
    intro W hPW htW h0
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact htW (hPW h0)

  let y : MRing ι → Ideal (MRing ι) → FractionRing (MRing ι ⧸ P) := fun s W =>
    algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) /
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W))
  have hdata : ∀ (s : MRing ι), ∀ W ∈ divSupp P s, P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧
      ∀ s' : MRing ι, y s' W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s') := by
    intro s W hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    obtain ⟨h1, h2⟩ := ht W hW.1.1.1 hW.2
    exact ⟨hPW, hW.1.1.1, h1, h2, fun s' => div_mul_cancel₀ _ (hne W hPW h2)⟩

  have term : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P → ∀ W ∈ divSupp P s,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
          (if IsHorizontal W then 0 else
            (geoNum 0 W (fun j => ((Fin.elim0 : Fin 0 → HermLine ι) j).a) : ℝ) * Real.log (charOf W)) =
        Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP W hW
    have hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (a k : ℤ))) s :=
      ⟨a, fun _ => rfl, hs, hsP⟩
    rw [if_neg (not_isHorizontal_of_dimOne arithVarZero hP hA hW)]
    obtain ⟨-, -, hta, htW, hy⟩ := hdata s W hW
    obtain ⟨hyW, hm⟩ := hD K ι P s (t W) a W (y s W) hP.2.1 hs hsP hW hta htW (hy s)
    have hy0 : y s W ≠ 0 := by
      intro h0
      have h1 := hy s
      rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact hsP h1
    rw [hm]
    exact hC K ι P s a W _ (y s W) hP hs hsP hW hyW hy0
  have hvert : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P →
      vertR P (Fin.elim0 : Fin 0 → HermLine ι) s =
        ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP
    unfold vertR
    exact finsum_mem_congr rfl fun W hW => term s hs hsP W hW
  rw [hvert f hf hfP, hvert g hg hgP]
  refine hL K ι P f g a x t (y f) (y g) hP hf hg hfP hgP hx fun W hW => ?_
  obtain ⟨-, -, hta, htW, hy⟩ : P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧ _ := by
    rcases hW with hW | hW
    · exact hdata f W hW
    · exact hdata g W hW
  exact ⟨hta, htW, hy f, hy g⟩

end

end GroundTheory.Heights₂.Heights.Inter
