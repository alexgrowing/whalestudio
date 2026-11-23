import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StCentreOverW
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogOfPullWeight
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 PullbackElimination

namespace CentreOverW

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem imageZ_isRelevant {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {y : Ideal (MRing ι')} (hy : IsRelevant y) : IsRelevant (imageZ v y) := by
  intro k
  obtain ⟨i', hi'⟩ := hy (κ k)
  obtain ⟨⟨k0, i⟩, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have hk : k0 = k := hv.1 ((hv.2.2.1 ⟨k0, i⟩).symm.trans (congrArg Sigma.fst hp))
  subst hk
  refine ⟨i, fun h => hi' ?_⟩
  have h' : rename v (X ⟨k0, i⟩ : MRing ι) ∈ y := h
  rwa [rename_X, hp] at h'

theorem imageZ_le {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} [P'.IsPrime] {W : Ideal (MRing ι)} (hQW : imageZ v P' ≤ W)
    (R : ValuationSubring (FractionRing (MRing ι' ⧸ P')))
    (hR : ∀ a ∈ locRing (imageZ v P') W, fracMapZ v P' a ∈ R) {y : Ideal (MRing ι')}
    (hy : IsValCentre P' R y) : imageZ v y ≤ W := by
  classical
  obtain ⟨hyM, hP'y, hcen⟩ := hy
  have := hyM.1
  have := imageZ_isPrime_of_prime v P'
  intro a ha
  by_contra haW
  obtain ⟨D, hDW⟩ : ∃ D : K' → ℕ, weightedHomogeneousComponent (pullWeight v) D a ∉ W := by
    by_contra h
    push Not at h
    apply haW
    rw [← sum_weightedHomogeneousComponent (w := pullWeight v) (φ := a),
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp a)]
    exact Ideal.sum_mem _ fun D _ => h D
  set c := weightedHomogeneousComponent (pullWeight v) D a with hcdef
  have hcy : rename v c ∈ y := by
    rw [hcdef, rename_component]
    exact LocRingPow.component_mem hyM.2.1 ha D
  have hc : IsMultiHomog c (fun k => D (κ k)) :=
    isMultiHomog_of_pullWeight hv (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨u, hu, huy⟩ := exists_form_notMem (imageZ_isRelevant hv hyM.2.2) (imageZ_isPrime_of_prime v y)
    (fun k => D (κ k))
  have hcQ : c ∉ imageZ v P' := fun h => hDW (hQW h)
  have hcnz : Ideal.Quotient.mk (imageZ v P') c ∈ nonZeroDivisors (MRing ι ⧸ imageZ v P') :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hmem := hR _ (Subring.subset_closure ⟨u, c, _, hcnz, hDW, hu, hc, rfl⟩)
  rw [IsFractionRing.mk'_eq_div, map_div₀, fracMapZ_algebraMap, fracMapZ_algebraMap] at hmem
  have h2 := ((hcen _ _ _ (rename_isMultiHomog hv hc) (rename_isMultiHomog hv hu) huy).2).mp hcy
  have hne : ∀ g, g ∉ P' → algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))
      (Ideal.Quotient.mk P' g) ≠ 0 := fun g hg => by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hc0 := hne (rename v c) (fun h => hcQ h)
  have hu0 := hne (rename v u) (fun h => huy (hP'y h))
  rw [ValuationSubring.mem_nonunits_iff] at h2
  have h3 := (R.valuation_le_one_iff _).mpr hmem
  have h4 := mul_lt_one_of_lt_of_le h2 h3
  rw [← map_mul, div_mul_div_cancel₀ hu0, div_self hc0, map_one] at h4
  exact lt_irrefl _ h4

theorem eq_or_eq_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A] {Q Y W : Ideal A}
    [Q.IsPrime] [Y.IsPrime] {s : A} (hW : W ∈ (Q ⊔ Ideal.span {s}).minimalPrimes) (hQY : Q ≤ Y) (hYW : Y ≤ W) :
    Y = Q ∨ Y = W := by
  have := hW.1.1
  have hQW : Q ≤ W := le_sup_left.trans hW.1.2
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hH := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have : (Y.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (Ideal.mk_ker.trans_le hQY)
  have : (W.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (Ideal.mk_ker.trans_le hQW)
  have : (⊥ : Ideal (A ⧸ Q)).IsPrime := Ideal.isPrime_bot
  have hb : (⊥ : Ideal (A ⧸ Q)) < Y.map (Ideal.Quotient.mk Q) := by
    refine bot_lt_iff_ne_bot.mpr fun e => h1 ?_
    rw [← Ideal.comap_map_mk hQY, e, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hYW' : Y.map (Ideal.Quotient.mk Q) < W.map (Ideal.Quotient.mk Q) := by
    refine lt_of_le_of_ne (Ideal.map_mono hYW) fun e => h2 ?_
    rw [← Ideal.comap_map_mk hQY, e, Ideal.comap_map_mk hQW]
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hb
  have e2 := (Ideal.height_add_one_le_of_lt_of_isPrime hYW').trans hH
  have e3 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add (le_add_self.trans e1) le_rfl).trans e2
  exact absurd e3 (by decide)

theorem eq_of_imageZ_eq {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} {n : ℕ} (hP' : IsArithVar P' (n + 1)) (hQ : IsArithVar (imageZ v P') (n + 1))
    {y : Ideal (MRing ι')} (hy : IsMultiProjPrime y) (hPy : P' ≤ y) (h : imageZ v y = imageZ v P') : y = P' := by
  classical
  have := hy.1
  by_contra hne
  obtain ⟨f, hfy, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPy (Ne.symm hne))
  obtain ⟨D, hD⟩ := LocRingPow.exists_component_not_mem hfP
  set g := weightedHomogeneousComponent (LocRingPow.multiDegWeight ι') D f
  have hgy : g ∈ y := LocRingPow.component_mem hy.2.1 hfy D
  have hg : IsMultiHomog g D :=
    LocRingPow.isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  choose c hc using hy.2.2
  obtain ⟨r, a, ha0, hsum⟩ := exists_elim hv hP' hQ hg hD c (fun k' h => hc k' (hPy h))
  have hT : (∏ k', (X ⟨k', c k'⟩ : MRing ι') ^ D k') ^ r ∉ y := by
    intro hm
    obtain ⟨k', -, hk⟩ := hy.1.prod_mem_iff.mp (hy.1.mem_of_pow_mem _ hm)
    exact hc k' (hy.1.mem_of_pow_mem _ hk)
  have hsum' := hPy hsum
  rw [Finset.sum_range_succ'] at hsum'
  have hrest : ∑ i ∈ Finset.range r, rename v (a (i + 1)) *
      (g ^ (i + 1) * (∏ k', (X ⟨k', c k'⟩ : MRing ι') ^ D k') ^ (r - (i + 1))) ∈ y :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
      (Ideal.mul_mem_right _ _ (y.pow_mem_of_mem hgy _ (Nat.succ_pos i)))
  have h0 := (Ideal.add_mem_iff_right _ hrest).mp hsum'
  rw [pow_zero, one_mul, Nat.sub_zero] at h0
  have ha : a 0 ∈ imageZ v y := (hy.1.mem_or_mem h0).resolve_right hT
  rw [h] at ha
  exact ha0 ha

end CentreOverW

theorem CentreOverW.proof : CentreOverW.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ _ _ hW
  have := hP'.2.1.1
  intro R hR y hy
  have hQW : imageZ v P' ≤ W := le_sup_left.trans hW.1.1.2
  have hYW := CentreOverW.imageZ_le hv hQW R hR hy
  have := hy.1.1
  have := imageZ_isPrime_of_prime v P'
  have := imageZ_isPrime_of_prime v y
  rcases CentreOverW.eq_or_eq_of_mem_minimalPrimes hW.1 (Ideal.comap_mono hy.2.1) hYW with h | h
  · exact Or.inl (CentreOverW.eq_of_imageZ_eq hv hP' hQ hy.1 hy.2.1 h)
  · exact Or.inr ⟨hy.1, hy.2.1, h⟩

end GroundTheory.Heights₂.Heights.Inter
