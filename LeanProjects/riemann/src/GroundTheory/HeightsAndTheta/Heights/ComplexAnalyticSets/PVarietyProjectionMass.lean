import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyProjectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGraphProjectionMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal

noncomputable section

theorem VarietyProjectionMass.proof (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hD : ComplexSets.DiscriminantCover.Statement) (hL : LocalGraphProjectionMass.Statement) :
    VarietyProjectionMass.Statement := by
  intro n d J hJ hd U hU B hB
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  obtain ⟨W, hW, hWfin⟩ := (hG n d J hJ hd).2.2.2 1 (fun _ => 1)
  obtain ⟨b, hb⟩ := MassFinite.exists_frame W hW
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hdn)
  set A := W.submatrix (I₀.orderEmbOfFin hI₀) id
  have hAfin : ComplexSets.IsFiniteProjection J A := by
    simpa using hWfin 0 (I₀.orderEmbOfFin hI₀).toEmbedding
  obtain ⟨P, hP0, hP⟩ := hD n d J A hJ hd hAfin
  set G := zeroSetEuc J ∩ {z | eval (A *ᵥ WithLp.ofLp z) P ≠ 0}
  have hPJ : ComplexSets.pullback A P ∉ J := fun hmem => hP0 <| hAfin.injective <| by
    rw [map_zero, ComplexSets.projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hbad : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) = 0 :=
    NullSmaller.proof n d _ (MassFinite.dim_sup_lt J hJ hd _ hPJ)
  have hsub : zeroSetEuc J ∩ B ⊆
      zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ B := by
    rintro z ⟨hz, hzB⟩
    by_cases hzP : eval (A *ᵥ WithLp.ofLp z) P = 0
    · left
      intro q hq
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      have hzj : eval (fun i => z i) j = 0 := hz j hj
      have hpb : eval (fun i => z i) (ComplexSets.pullback A P) = 0 := by
        rw [MassFinite.eval_pullback]
        exact hzP
      simp [hzj, hpb]
    · exact Or.inr ⟨⟨hz, hzP⟩, hzB⟩
  have hgood := hL n d b I₀ G hI₀ (MassFinite.good_localGraph J W b hb I₀ hI₀ P
    (fun y hy x hx => (hP y hy).2.2 x hx)) U hU B hB
  have hGZ : G ∩ B ⊆ zeroSetEuc J ∩ B := Set.inter_subset_inter_left _ Set.inter_subset_left
  calc μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B)
      ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ B) :=
        measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) +
          μH[((2 * d : ℕ) : ℝ)] (G ∩ B) := measure_union_le _ _
    _ = μH[((2 * d : ℕ) : ℝ)] (G ∩ B) := by rw [hbad, zero_add]
    _ ≤ _ := hgood
    _ ≤ _ := by
      refine Finset.sum_le_sum fun s _ => mul_le_mul' (iSup_mono fun x => ?_)
        (measure_mono (Set.image_mono hGZ))
      exact ENat.toENNReal_le.2 (Set.encard_le_encard fun z hz => ⟨hGZ hz.1, hz.2⟩)

end

end GroundTheory.Heights₂.Heights
