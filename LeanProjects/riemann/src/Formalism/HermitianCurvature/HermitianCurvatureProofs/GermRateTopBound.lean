import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVNonloc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSumLeOfGram

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Formalism.FourierDecayAlt.P.GermFibreKernels Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

theorem germ_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Vec : C.LPt → H) (b s : ℕ) (hs : 2 ≤ s) (hbs : b + s - 1 = S.G.r + 1) (h : C.LPt)
    (x D : ℂ) (hD : D ≠ 0) :
    utOf s (vOf (KB.dlB S (b + s - 1) 1) Vec) h x D -
        mainD s (betaL S) 1 (fun z => (fun _ => (1 : ℂ)) z • btOf s (KB.dlB S b s) Vec h z) x D =
      ∑ j ∈ Finset.insertNone (G.rootSet s D), coJ S b s x j • Vec (ptJ s h x D j) := by
  rw [Finset.sum_insertNone, hbs, sub_eq_add_neg]
  have hz : ∀ z ∈ G.rootSet s D, z ≠ 0 := by
    intro z hz h0
    unfold G.rootSet at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
    rw [h0, zero_pow (by omega)] at hz
    exact hD hz.symm
  congr 1
  · simp only [utOf, vOf, ptX, coJ, ptJ, smul_smul, List.append_assoc, List.singleton_append]
    push_cast
    rfl
  · unfold mainD
    rw [one_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hzm => ?_
    simp only [btOf, if_neg (hz z hzm), one_smul, coJ, ptJ, smul_smul, neg_smul, one_mul]

end

end Formalism.FourierDecayAlt.P.GermRateSplit

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Formalism.FourierDecayAlt.P.GermFibreKernels Formalism.FourierDecayAlt.P.GermRateSplit Finset
open scoped ComplexConjugate InnerProductSpace

theorem germ_rate_top_bound : Formalism.FourierDecayAlt.P.GermRateSplit.GermRateTopB := by
  intro hA Cb
  obtain ⟨c1, hc1⟩ := GermFibreKernels.cutSeq_cpt Cb
  refine ⟨c1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  have hF := hc1 c1 le_rfl E Wp Wq S p f χ A₀ hB n
  intro ε hε b s hb hs hbs a ha H _ _ _ Vec hVec
  refine ⟨1, fun _ => 1, by simp, fun _ => by simp, continuousOn_const, ?_⟩
  intro h hsz K hK hK0
  have hbs' : b + s = S.G.r + 2 := hbs
  have hb1 : b + s - 1 = S.G.r + 1 := by omega
  obtain ⟨I, hI, c, Fi, L, hc, hFi, hgram⟩ :=
    gN_top_gram hB (PBASM.cutSeq S p f χ n) (fun v ε hε => hF v ε hε) v ε hε a ha
  choose Ci hCi using fun i => top_core hB v (Fi i) (hFi i) a.length b s hb hs hbs' h hsz K hK hK0
  refine ⟨∑ i, √(c i) * ‖L i‖ * Ci i, fun x hx D hD => ?_⟩
  have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
  rw [germ_sum (PBL.setC S p (PBASM.cutSeq S p f χ n)) Vec b s hs hb1 h x D hD0]
  have hk : ∀ j ∈ Finset.insertNone (G.rootSet s D), ∀ l ∈ Finset.insertNone (G.rootSet s D),
      KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε (b + s - 1) a (ptJ s h x D j) (ptJ s h x D l) =
        ∑ i, (c i : ℂ) * ⟪(omN S a.length (ptJ s h x D l) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D l))),
          (omN S a.length (ptJ s h x D j) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))⟫_ℂ := by
    intro j _ l _
    rw [hb1]
    exact hgram _ _
  have h2 := norm_sum_le_of_gram (fun P Q => KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε (b + s - 1) a P Q)
    Vec hVec c hc (fun i P => (omN S a.length P : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S P)))
    (Finset.insertNone (G.rootSet s D)) (ptJ s h x D) hk (coJ S b s x)
  refine h2.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have e : ∑ j ∈ Finset.insertNone (G.rootSet s D), conj (coJ S b s x j) •
        ((omN S a.length (ptJ s h x D j) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))) =
      L i (∑ j ∈ Finset.insertNone (G.rootSet s D), (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) •
        (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_smul]
  rw [e]
  have h3 := hCi i x hx D hD
  have hsq := Real.sqrt_nonneg (c i)
  calc √(c i) * ‖L i (∑ j ∈ Finset.insertNone (G.rootSet s D),
        (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) • (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))‖
      ≤ √(c i) * (‖L i‖ * ‖∑ j ∈ Finset.insertNone (G.rootSet s D),
        (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) • (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j))‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hsq
    _ ≤ √(c i) * (‖L i‖ * (Ci i * ‖x‖⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) hsq
    _ = √(c i) * ‖L i‖ * Ci i * ‖x‖⁻¹ := by ring

end Formalism.FourierDecayAlt.P
