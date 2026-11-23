import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
open UpperTheory.Gal.LocalSmoothExtension

private lemma sum_swap {A : Type} (s : Finset A) (a : A → ℂ) (g : A → ℂ → ℂ) (R : Multiset ℂ) :
    (R.map fun μ => ∑ α ∈ s, a α * g α μ).sum = ∑ α ∈ s, a α * (R.map (g α)).sum := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons b R ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, mul_add, Finset.sum_add_distrib]

theorem UpperTheory.Gal.LocalSmoothExtension.groupTop_of :
    GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd → GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace → RootW → InvRoots → InvPolProps → MarkRoots → DPairPol → DSumCongr → TestOf → TestOne → GroupTop := by
  classical
  intro hW hT hR hInv hProps hMark hDP hDS hTest hOne p _ D G L lam i₀ h hh
  have hcj : NumberField.ComplexEmbedding.conjugate (D.tau i₀) ≠ D.tau i₀ := fun e =>
    NumberField.IsTotallyComplex.complexEmbedding_not_isReal (D.tau i₀)
      (NumberField.ComplexEmbedding.isReal_iff.2 e)
  obtain ⟨k₀, hk⟩ := hR D.F G.n (D.tau i₀) (epsOf D) lam h hcj hh
  refine ⟨k₀, fun k hkk => ?_⟩
  obtain ⟨c, hc1, hc2⟩ := hk k hkk
  refine ⟨c, hc1, ?_⟩
  intro ha hga hodd v hv V _ _ _ ξ hξ Lv f hf hG y
  have hTf := hTest _ _ f hf
  have hO := hOne p G
  rw [hW p G hga hodd v hv _ Lv f hTf.1 hG.reg (Kp G) (oneP G) hO.1 hG.pairs]
  have key : ∀ P : GlobalTheory.LKDef.DPair G,
      GlobalTheory.RootSumWeights.rootSum G v (fun P μ => c.sum fun α r => r * cW L i₀ v α y P μ) P.pol =
        (fun P => schW lam (endPol L P)) P.pol * ∑ i, y ^ h i := by
    intro P
    obtain ⟨h0, q, hq⟩ := hDP p G P v
    have hroots := hMark p D G L ha i₀ v hv hInv P.pol h0
    have h0' : (P.pol.map (L.e.symm : G.F →+* D.F)).coeff 0 ≠ 0 := by
      rw [Polynomial.coeff_map]
      exact (map_ne_zero _).2 h0
    obtain ⟨d1, d2, d3⟩ := hProps D.F (P.pol.map (L.e.symm : G.F →+* D.F)) h0'
    have hdeg : (endPol L P.pol).natDegree = G.n := by
      show (invPol _).natDegree = _
      rw [d1, Polynomial.natDegree_map]
      exact P.reg.1
    have hsep : (endPol L P.pol).Separable := d3 (P.reg.2.map)
    have habs : ∃ q : ℝ, ∀ z ∈ UpperTheory.Gal.W2.rts (endPol L P.pol) (D.tau i₀),
        z * (starRingEnd ℂ) z = q := by
      refine ⟨q⁻¹, fun z hz => ?_⟩
      rw [← hroots, Multiset.mem_map] at hz
      obtain ⟨μ, hμ, rfl⟩ := hz
      have hm := hq μ hμ
      have hq' : ((q⁻¹ : ℝ) : ℂ) = (μ * (starRingEnd ℂ) μ)⁻¹ := by
        rw [hm]; push_cast; rfl
      rw [hq']
      unfold markOf
      split_ifs
      · rw [map_inv₀, mul_inv]
      · rw [map_inv₀, Complex.conj_conj, mul_inv, mul_comm]
    have := hc2 (endPol L P.pol) hdeg hsep d2 habs y
    show _ = schW lam (endPol L P.pol) * _
    rw [← this]
    unfold GlobalTheory.RootSumWeights.rootSum
    simp only [Finsupp.sum]
    rw [sum_swap]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← hroots, Multiset.map_map]
    rfl
  rw [hDS p G _ (fun P => schW lam (endPol L P)) (∑ i, y ^ h i) key Lv.K.toSubgroup f 1 (Kp G) (oneP G)]
  rw [hT p G hga V ξ (fun P => schW lam (endPol L P)) hξ Lv f hTf.1 hTf.2 (Kp G) (oneP G) hO.1 hO.2 hG.forms]
