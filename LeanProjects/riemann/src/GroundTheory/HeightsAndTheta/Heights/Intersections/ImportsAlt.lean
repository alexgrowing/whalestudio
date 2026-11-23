import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalSpanTwo
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImageVarIdBotTwo
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 PointVertical

theorem ArithmeticIntersectionVertical.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι')
    (hPD : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjDegStatement F ι ι')
    (hDeg : VerticalDegree.Statement) :
    ArithmeticIntersectionVertical.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n a s α W' hv hP' hP hs hsP hW' hvert
  classical

  have hs' : IsSectionOn P' (HermLine.sqMetric (ι := ι') (Function.extend κ α 0)) (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, hsP⟩
  obtain ⟨hW'm, hpr, hW'd⟩ := (divSuppArith K' ι' P' n _ _ W' hP' hs' hW').2 hvert
  set p := charOf W' with hpdef
  have : Fact p.Prime := ⟨hpr⟩
  have hpW' : ((p : ℕ) : MRing ι') ∈ W' := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W'
  have hW'p : IsProjVarF (W'.map (red p)) n :=
    ⟨isMultiProjPrime_red p hW'm hpW', by rw [ringKrullDim_red p hpW', hW'd]⟩

  have hWm : IsMultiProjPrime (imageZ v W') := isMultiProjPrime_imageZ hv hW'm
  have hpW : ((p : ℕ) : MRing ι) ∈ imageZ v W' := by
    show rename v ((p : ℕ) : MRing ι) ∈ W'
    simpa using hpW'
  have hVm := isMultiProjPrime_red p hWm hpW

  obtain ⟨I, hI, -⟩ := hR4 (ZMod p) K ι
  obtain ⟨I', hI', -⟩ := hR4 (ZMod p) K' ι'
  have hgeo' : geoNum n W' (fun j => pullDeg κ (a j)) = I' (W'.map (red p)) n (fun j => pullDeg κ (a j)) :=
    hGeo K' ι' p I' hI' W' n _ hW'm hpW' hW'p
  by_cases hmem : imageZ v W' ∈ divSupp (imageZ v P') s
  ·
    refine Or.inl ⟨hmem, fun G' J' hJ' => ?_⟩
    have hsW : IsSectionOn (imageZ v P') (HermLine.sqMetric (ι := ι) α) s := ⟨α, fun _ => rfl, hs, hsP⟩
    have hWvert : ¬ IsHorizontal (imageZ v W') := fun h => by
      have h2 : ((p : ℕ) : ℤ) ∈ (imageZ v W').comap (C : ℤ →+* MRing ι) := by
        rw [Ideal.mem_comap, map_natCast]
        exact hpW
      rw [h, Ideal.mem_bot] at h2
      exact hpr.ne_zero (by exact_mod_cast h2)
    obtain ⟨-, -, hWd⟩ := (divSuppArith K ι (imageZ v P') n _ _ _ hP hsW hmem).2 hWvert
    have hWp : IsProjVarF ((imageZ v W').map (red p)) n := ⟨hVm, by rw [ringKrullDim_red p hpW, hWd]⟩
    have hVi : IsProjVarF (imageVar (ZMod p) v (W'.map (red p))) n := by
      rw [imageVar_red p v hpW']
      exact hWp
    obtain ⟨i', hi'⟩ : ∃ i' : ∀ k', ι' k', IsChart (W'.map (red p)) i' :=
      ⟨fun k => (hW'p.1.2.2 k).choose, fun k => (hW'p.1.2.2 k).choose_spec⟩
    rw [hgeo', hPD (ZMod p) K ι K' ι' I I' hI hI' κ v _ n a i' hv hW'p hVi hi', imageVar_red p v hpW',
      ← hGeo K ι p I hI _ n a hWm hpW hWp, hDeg K ι K' ι' κ v p W' n i' hv hpW' hW'p hVi hi' G' J' hJ']
  ·
    refine Or.inr ⟨hmem, ?_⟩
    have hsW' : rename v s ∈ W' := hW'.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hle : imageZ v P' ⊔ Ideal.span {s} ≤ imageZ v W' :=
      sup_le (Ideal.comap_mono (le_sup_left.trans hW'.1.1.2))
        (Ideal.span_le.2 (Set.singleton_subset_iff.2 hsW'))
    have := hWm.1
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le hle
    have hQne : Q ≠ imageZ v W' := fun h => hmem ⟨h ▸ hQ, hWm.2.2⟩
    obtain ⟨x, hxW, hxQ⟩ : ∃ x ∈ imageZ v W', x ∉ Q := by
      by_contra hc
      exact hQne (le_antisymm hQW fun y hy => by_contra fun h => hc ⟨y, hy, h⟩)
    have := hQ.1.1
    have := hP.2.1.1
    have h1 := dim_quot_minimal_add_one (imageZ v P') Q s hsP hQ
    rw [hP.2.2.2] at h1
    have hQd : ringKrullDim (MRing ι ⧸ Q) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
    have hdim := krullDim_quot_add_one_le hQW hxW hxQ
    obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
    rw [← ringKrullDim_red p hpW, hD, hQd] at hdim
    have hD' : D + 1 ≤ n + Fintype.card K := by exact_mod_cast hdim
    have hVi : IsProjVarF (imageVar (ZMod p) v (W'.map (red p))) (D - Fintype.card K) := by
      rw [imageVar_red p v hpW']
      exact ⟨hVm, by rw [hD, Nat.sub_add_cancel hKD]⟩
    rw [hgeo']
    exact hPC (ZMod p) K ι K' ι' I' hI' κ v _ n (D - Fintype.card K) a hv hW'p hVi (by omega)

end GroundTheory.Heights₂.Heights.Inter
