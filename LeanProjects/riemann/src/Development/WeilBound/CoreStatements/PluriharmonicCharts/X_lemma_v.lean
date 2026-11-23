import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.lemma_v

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_of_mem {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)} (h : W ∈ divSupp P s) :
    divCycle P s W = multAt (P ⊔ Ideal.span {s}) W := by
  simp [divCycle, Finsupp.ofSupportFinite_coe, h]

theorem divCycle_of_notMem {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)} (h : W ∉ divSupp P s) :
    divCycle P s W = 0 := by
  simp [divCycle, Finsupp.ofSupportFinite_coe, h]

theorem finsum_eq_sum (P : Ideal (MRing ι)) (s : MRing ι) (F : Ideal (MRing ι) → ℝ) (S : Finset (Ideal (MRing ι)))
    (hS : (divSupp_finite P s).toFinset ⊆ S) :
    ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) * F W = ∑ W ∈ S, (divCycle P s W : ℝ) * F W := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), ← Finset.sum_subset hS]
  · refine Finset.sum_congr rfl fun W hW => ?_
    rw [divCycle_of_mem ((Set.Finite.mem_toFinset _).1 hW)]
  · intro W _ hW
    rw [divCycle_of_notMem (fun h => hW ((Set.Finite.mem_toFinset _).2 h)), Nat.cast_zero, zero_mul]

theorem sub_eq_cycR {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {D : ℕ} {L : Fin D → HermLine ι} {A B : HermLine ι} (hP : IsArithVar P (D + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) {f g : MRing ι} {df dg : K → ℕ}
    (hf : IsMultiHomog f df) (hg : IsMultiHomog g dg) (hfP : f ∉ P) (hgP : g ∉ P)
    (hd : ∀ k, (df k : ℤ) - dg k = A.a k - B.a k)
    (hn : ∀ z ∈ mcPts P,
      ‖eval z (map (Int.castRingHom ℂ) f)‖ * B.h z = ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z) :
    I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L B) = cycR I P L f - cycR I P L g := by
  obtain ⟨-, hAdd, hR⟩ := hI
  set M : HermLine ι := (HermLine.sqMetric (ι := ι) dg).tensor B.inv with hMdef
  have hM : IsSmoothHerm M :=
    ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (isSmoothHerm_sqMetric dg) (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_inv hB)
  have hRf := hR P D L _ f df hP hL (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA hM) (fun k => by
    show A.a k + ((dg k : ℤ) + -B.a k) = df k
    linarith [hd k]) hf hfP
  have hRg := hR P D L _ g dg hP hL (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hB hM) (fun k => by
    show B.a k + ((dg k : ℤ) + -B.a k) = dg k
    ring) hg hgP
  have h1 := hAdd P D L A M hP hL hA hM
  have h2 := hAdd P D L B M hP hL hB hM
  have hint : arInt P f (A.tensor M) L = arInt P g (B.tensor M) L := by
    unfold arInt
    refine GroundTheory.Heights₂.Heights.Inter.ptsIntegral_congr_pts P _ fun z hz => ?_
    have hA0 := A.pos z hz.1
    have hB0 := B.pos z hz.1
    have hM0 := M.pos z hz.1
    show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * M.h z)) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (B.h z * M.h z))
    congr 1
    rw [div_eq_div_iff (mul_pos hA0 hM0).ne' (mul_pos hB0 hM0).ne', ← mul_assoc, ← mul_assoc, hn z hz]
  rw [recR_eq] at hRf hRg
  linarith

theorem geoNum_nonneg (hK : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg) {P : Ideal (MRing ι)} {D : ℕ}
    (hP : IsArithVar P (D + 1)) {p : ℕ} (hp : p.Prime) {a : Fin D → K → ℤ} (ha : ∀ j, NefAt P p (a j))
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp P (C (p : ℤ))) : 0 ≤ geoNum D W a := by
  have hle : P ⊔ Ideal.span {(C (p : ℤ) : MRing ι)} ≤ W := hW.1.1.2
  have hpW : (p : MRing ι) ∈ W := by
    have := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rwa [map_natCast] at this
  have hnot : ∀ V : Ideal (MRing ι), IsHorizontal V → (C (p : ℤ) : MRing ι) ∉ V := by
    intro V hV h
    have h1 : (p : ℤ) ∈ V.comap (C : ℤ →+* MRing ι) := h
    rw [hV, Ideal.mem_bot] at h1
    exact hp.ne_zero (by exact_mod_cast h1)
  have hsec : IsSectionOn P (oneLine (ι := ι)) (C (p : ℤ)) := by
    refine ⟨0, fun k => rfl, fun m hm k => ?_, hnot P hP.2.2.1⟩
    classical
    have hm0 : m = 0 := by
      by_contra h
      exact (mem_support_iff.1 hm) (by rw [coeff_C, if_neg (Ne.symm h)])
    simp [hm0]
  have hnh : ¬ IsHorizontal W := fun h => hnot W h (by rwa [map_natCast])
  obtain ⟨h1, h2, h3⟩ := (ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith K ι P D _ _ W hP hsec hW).2 hnh
  refine hK K ι W D a h1 h2.ne_zero h3 fun j W' hW' hWW' hdim => ?_
  exact ha j W' hW' (le_sup_left.trans (hle.trans hWW'))
    (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.charOf_eq_of_mem hW'.1 hp (hWW' hpW)) hdim

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem not_isHorizontal {W : Ideal (MRing ι)} (h : charOf W ≠ 0) : ¬ IsHorizontal W := by
  intro hW
  apply h
  have : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 :=
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).1 hW
  simp [charOf, this]

end PositivityTheory.Xgp.lemma_v

theorem PositivityTheory.Xgp.t_lemma_v : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (L : Fin D → HermLine ι) (A B : HermLine ι) (T : Finset ℕ) (α : ℕ → ℝ), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B → (∀ p ∈ T, p.Prime ∧ 0 ≤ α p) → VertClose P T α A B → (∀ p ∈ T, ∀ j, NefAt P p (L j).a) → |II K ι P (D + 1) (Fin.snoc L A) - II K ι P (D + 1) (Fin.snoc L B)| ≤ (∑ p ∈ T, α p * Real.log p) * ptsIntegral P (pot L) fun _ => 1 := by
  intro hIn II hII K _ ι _ P D L A B T α hP hL hA hB hT hV hnef
  classical
  obtain ⟨f, g, df, dg, hf, hg, hfP, hgP, hd, hn, hout, hin⟩ := hV
  rw [PositivityTheory.Xgp.lemma_v.sub_eq_cycR (hII.1 K ι) hP hL hA hB hf hg hfP hgP hd hn]
  set S : Finset (Ideal (MRing ι)) := (divSupp_finite P f).toFinset ∪ (divSupp_finite P g).toFinset ∪
    T.biUnion fun p => (divSupp_finite P (C (p : ℤ) : MRing ι)).toFinset with hS
  have hrhs : (∑ p ∈ T, α p * Real.log p) * ptsIntegral P (pot L) (fun _ => 1) =
      ∑ W ∈ S, ∑ p ∈ T, α p * Real.log p *
        ((divCycle P (C (p : ℤ)) W : ℝ) * (geoNum D W (fun j => (L j).a) : ℝ)) := by
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hIn.degree K ι P D L p hP hL (hT p hp).1, PositivityTheory.Xgp.lemma_v.finsum_eq_sum P _ _ S, Finset.mul_sum]
    exact (Finset.subset_biUnion_of_mem (fun p : ℕ => (divSupp_finite P (C (p : ℤ) : MRing ι)).toFinset) hp).trans
      Finset.subset_union_right
  have hpos : ∀ W, ∀ p ∈ T, 0 ≤ (divCycle P (C (p : ℤ)) W : ℝ) * (geoNum D W (fun j => (L j).a) : ℝ) ∧
      (divCycle P (C (p : ℤ)) W : ℝ) * |(geoNum D W (fun j => (L j).a) : ℝ)| =
        (divCycle P (C (p : ℤ)) W : ℝ) * (geoNum D W (fun j => (L j).a) : ℝ) := by
    intro W p hp
    by_cases hW : W ∈ divSupp P (C (p : ℤ))
    · have h0 : (0 : ℝ) ≤ (geoNum D W (fun j => (L j).a) : ℝ) := by
        exact_mod_cast PositivityTheory.Xgp.lemma_v.geoNum_nonneg hIn.kleimanNef hP (hT p hp).1 (hnef p hp) hW
      exact ⟨mul_nonneg (Nat.cast_nonneg _) h0, by rw [abs_of_nonneg h0]⟩
    · rw [PositivityTheory.Xgp.lemma_v.divCycle_of_notMem hW]
      simp
  have hterm : ∀ W, ∀ p ∈ T, 0 ≤ α p * Real.log p *
      ((divCycle P (C (p : ℤ)) W : ℝ) * (geoNum D W (fun j => (L j).a) : ℝ)) := fun W p hp =>
    mul_nonneg (mul_nonneg (hT p hp).2 (Real.log_natCast_nonneg p)) (hpos W p hp).1
  rw [hrhs]
  unfold cycR
  rw [PositivityTheory.Xgp.lemma_v.finsum_eq_sum P f _ S (Finset.subset_union_left.trans Finset.subset_union_left),
    PositivityTheory.Xgp.lemma_v.finsum_eq_sum P g _ S (Finset.subset_union_right.trans Finset.subset_union_left),
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun W _ => ?_)
  rw [← sub_mul]
  by_cases hW : charOf W ∈ T
  · refine le_trans ?_ (Finset.single_le_sum (hterm W) hW)
    rw [if_neg (PositivityTheory.Xgp.lemma_v.not_isHorizontal (hT _ hW).1.ne_zero), abs_mul, abs_mul,
      abs_of_nonneg (Real.log_natCast_nonneg _), ← (hpos W _ hW).2]
    refine (mul_le_mul_of_nonneg_right (hin W hW)
      (mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg _))).trans (le_of_eq ?_)
    ring
  · rw [hout W hW, sub_self, zero_mul, abs_zero]
    exact Finset.sum_nonneg (hterm W)
