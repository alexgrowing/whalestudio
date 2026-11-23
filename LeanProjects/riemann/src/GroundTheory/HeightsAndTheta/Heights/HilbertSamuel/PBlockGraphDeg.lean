import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphFibreRatio
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsChartRankAdjoin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGraphDeg

theorem isMultiHomog_blockForms {K : Type} [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type}
    (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (q : Σ k, GlobalTheory κ k) :
    IsMultiHomog (blockForms k₀ M q) (blockDeg k₀ 1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk, Sigma.ext_iff]

theorem x'_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K₂ : Type} [Fintype K₂]
    {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι}
    (G : GenFibre (inrV (ι := ι) (ι₂ := ι₂)) (graphIdeal P g)) (k : K) (i : ι k)
    (hi : (X ⟨k, i⟩ : MRing ι) ∉ P) : G.x' ⟨Sum.inl k, i⟩ ≠ 0 := by
  intro h
  have h1 : (X ⟨Sum.inl k, i⟩ : MRing (Sum.elim ι ι₂)) ∈ graphIdeal P g := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    simpa using h
  rw [graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at h1
  exact hi (Ideal.Quotient.eq_zero_iff_mem.1 (MvPolynomial.C_eq_zero.1 h1))

end BlockGraphDeg

open BlockGraphDeg in

theorem BlockGraphDeg.proof (hGr : GraphStatement) (hImg : BlockGraphImage.Statement)
    (hEx : GenFibreExistsStatement) (hDim : FibreDimStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCR : Inter.ChartRankAdjoin.Statement) (hRat : BlockGraphFibreRatio.Statement) :
    BlockGraphDeg.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hy hB hx hI
  have hImage := hImg K ι Ω κ y k₀ M N x hI
  have hIm : IsArithVar (imageZ (inrV (ι := ι) (ι₂ := GlobalTheory κ))
      (graphIdeal (mCoordIdeal y) (blockForms k₀ M))) (D + 1) := by
    rw [hImage]
    exact hx

  have hnv : ∀ u : Unit, ∃ j, blockForms k₀ M ⟨u, j⟩ ∉ mCoordIdeal y := by
    intro u
    obtain ⟨j, hj⟩ := hIm.2.1.2.2 u
    refine ⟨j, fun hm => hj ?_⟩
    rw [imageZ, Ideal.mem_comap]
    change rename inrV (X ⟨u, j⟩) ∈ _
    rw [rename_X, graphIdeal, RingHom.mem_ker, inrV, graphMap, eval₂Hom_X']
    change C (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨u, j⟩)) * X u = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero, zero_mul]
  have hΓ := (hGr K ι Unit (GlobalTheory κ) (mCoordIdeal y) (D + 1) (blockForms k₀ M) (fun _ => blockDeg k₀ 1) hy
    (isMultiHomog_blockForms k₀ M) hnv).1
  obtain ⟨G⟩ := hEx Unit (GlobalTheory κ) (K ⊕ Unit) (Sum.elim ι (GlobalTheory κ)) Sum.inr inrV _ (D + 1) isBlockMap_inr hΓ
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → K ⊕ Unit)) (fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr)
  have hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 :=
    hDim Unit (GlobalTheory κ) (K ⊕ Unit) (Sum.elim ι (GlobalTheory κ)) Sum.inr inrV _ (D + 1) 0 G isBlockMap_inr hΓ hIm

  choose c hc using hy.2.1.2.2
  let ch : (k : FibreBlock (Sum.inr : Unit → K ⊕ Unit)) → fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr k := fun
    | ⟨Sum.inl k, _⟩ => c k
    | ⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h
  have hz : ∀ k : FibreBlock (Sum.inr : Unit → K ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0 := by
    rintro ⟨(k | u), h⟩
    · exact x'_ne_zero G k (c k) (hc k)
    · exact absurd ⟨u, rfl⟩ h
  have hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch := by
    intro k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact hz k
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ hpt hch]
  have hdeg := hCR (FibreBlock (Sum.inr : Unit → K ⊕ Unit)) (fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr) G.Φ G.Φ'
    (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1
  have hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → K ⊕ Unit),
      fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨⟨(k | u), h⟩, i⟩, rfl⟩
    · exact IntermediateField.mem_bot.2 (hRat D K ι Ω κ y k₀ M N x hy hB hI G k i (c k) (x'_ne_zero G k (c k) (hc k)))
    · exact absurd ⟨u, rfl⟩ h
  change ((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
