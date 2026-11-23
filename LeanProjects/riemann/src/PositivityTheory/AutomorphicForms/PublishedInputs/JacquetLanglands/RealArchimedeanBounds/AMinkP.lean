import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

open NumberField MeasureTheory Module Finset

namespace UpperTheory.Esk.MinkowskiBoundLemmas

open scoped Classical

abbrev Ix (F : Type) [Field F] [NumberField F] := Free.ChooseBasisIndex ℤ (𝓞 F)

abbrev Rp (F : Type) [Field F] [NumberField F] := {w : InfinitePlace F // w.IsReal}

instance instHaarRp (F : Type) [Field F] [NumberField F] :
    Measure.IsAddHaarMeasure ((volume : Measure (Rp F → ℝ)).prod (volume : Measure (Rp F → ℝ))) :=
  Measure.prod.instIsAddHaarMeasure _ _

noncomputable def B (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    (Ix F → ℝ) ≃ₗ[ℝ] (Rp F → ℝ) :=
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isComplex_iff_isReal.2 (IsTotallyReal.isReal _) w.2⟩
  (mixedEmbedding.latticeBasis F).equivFun.symm.trans LinearEquiv.prodUnique

lemma B_apply (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (m : Ix F → ℝ) (w : Rp F) :
    B F m w = ∑ i, m i * InfinitePlace.embedding_of_isReal w.2 (integralBasis F i) := by
  simp [B, Basis.equivFun_symm_apply, mixedEmbedding.mixedEmbedding_apply_isReal]

noncomputable def Phi (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    (Ix F ⊕ Ix F → ℝ) ≃ₗ[ℝ] (Rp F → ℝ) × (Rp F → ℝ) :=
  (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).trans ((B F).prodCongr (B F))

lemma Phi_apply (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : Ix F ⊕ Ix F → ℝ) :
    Phi F y = (B F (fun i => y (Sum.inl i)), B F (fun i => y (Sum.inr i))) := rfl

noncomputable def cst (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : NNReal :=
  Measure.addHaarScalarFactor
    (Measure.map (Phi F).toContinuousLinearEquiv (volume : Measure (Ix F ⊕ Ix F → ℝ)))
    ((volume : Measure (Rp F → ℝ)).prod (volume : Measure (Rp F → ℝ)))

lemma map_eq (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Measure.map (Phi F).toContinuousLinearEquiv (volume : Measure (Ix F ⊕ Ix F → ℝ))
      = cst F • ((volume : Measure (Rp F → ℝ)).prod (volume : Measure (Rp F → ℝ))) := by
  unfold cst; exact Measure.isAddLeftInvariant_eq_smul _ _

lemma cst_pos (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : 0 < cst F := by
  unfold cst; exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

lemma vol_S {κ : Type} [Fintype κ] (α β x : κ → ℝ) (hβ : ∀ w, 0 ≤ β w) :
    ((volume : Measure (κ → ℝ)).prod (volume : Measure (κ → ℝ)))
      {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w}
      = ∏ w, ENNReal.ofReal (4 * (α w * β w)) := by
  have hS : MeasurableSet
      {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w} := by
    have : IsClosed
        {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w} := by
      simp only [Set.ofPred_forall, Set.ofPred_and]
      exact isClosed_iInter fun w =>
        (isClosed_le (by fun_prop) continuous_const).inter (isClosed_le (by fun_prop) continuous_const)
    exact this.measurableSet
  rw [Measure.prod_apply hS]
  have hslice : (fun p1 : κ → ℝ => volume (Prod.mk p1 ⁻¹'
      {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w}))
      = (Set.Icc (-α) α).indicator (fun _ => ∏ w, ENNReal.ofReal (2 * β w)) := by
    funext p1
    by_cases h : p1 ∈ Set.Icc (-α) α
    · rw [Set.indicator_of_mem h]
      rw [Set.mem_Icc, Pi.le_def, Pi.le_def] at h
      have hA : ∀ w, |p1 w| ≤ α w := fun w => abs_le.2 ⟨by simpa using h.1 w, h.2 w⟩
      have e : Prod.mk p1 ⁻¹'
          {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w}
          = Set.Icc (fun w => -β w - p1 w * x w) (fun w => β w - p1 w * x w) := by
        ext q
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def]
        constructor
        · intro hq
          refine ⟨fun w => ?_, fun w => ?_⟩
          · have := abs_le.1 (hq w).2; linarith [this.1]
          · have := abs_le.1 (hq w).2; linarith [this.2]
        · rintro ⟨h1, h2⟩ w
          exact ⟨hA w, abs_le.2 ⟨by linarith [h1 w], by linarith [h2 w]⟩⟩
      rw [e, Real.volume_Icc_pi]
      congr 1; funext w; congr 1; ring
    · rw [Set.indicator_of_notMem h]
      have e : Prod.mk p1 ⁻¹'
          {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w} = ∅ := by
        ext q
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hq
        apply h
        rw [Set.mem_Icc, Pi.le_def, Pi.le_def]
        exact ⟨fun w => by simpa using (abs_le.1 (hq w).1).1, fun w => (abs_le.1 (hq w).1).2⟩
      rw [e, measure_empty]
  rw [hslice, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc_pi,
    ← Finset.prod_mul_distrib]
  congr 1; funext w
  rw [← ENNReal.ofReal_mul (by linarith [hβ w])]
  congr 1; simp only [Pi.neg_apply]; ring

lemma sum_integral (F : Type) [Field F] [NumberField F] (u : Ix F → ℤ) :
    IsIntegral ℤ (∑ i, (u i : F) * integralBasis F i) := by
  have : (∑ i, (u i : F) * integralBasis F i) ∈ integralClosure ℤ F :=
    Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _)
      (by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
  exact this

lemma emb_sum (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (u : Ix F → ℤ) (w : Rp F) :
    InfinitePlace.embedding_of_isReal w.2 (∑ i, (u i : F) * integralBasis F i)
      = B F (fun i => (u i : ℝ)) w := by
  rw [B_apply]; simp [map_sum, map_mul, map_intCast]

theorem core (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : ∃ C : ℝ, 0 < C ∧
    ∀ z : InfinitePlace F → ℂ, (∀ v, (z v).im ≠ 0) →
    ∃ s : Fin 2 → F, s ≠ 0 ∧ (∀ i, IsIntegral ℤ (s i)) ∧ ∀ v,
      ‖((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (s 0) : ℝ) : ℂ) * z v +
        ((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (s 1) : ℝ) : ℂ)‖ ^ 2
        ≤ C * |(z v).im| := by
  classical
  set c : ℝ := (cst F : ℝ) with hc_def
  have hc : 0 < c := cst_pos F
  set t : ℝ := 1 + 1 / c with ht_def
  have ht1 : 1 ≤ t := by have := one_div_pos.2 hc; linarith
  refine ⟨2 * t ^ 2, by positivity, fun z hz => ?_⟩
  set d := Fintype.card (Rp F) with hd_def
  have hne : Nonempty (Rp F) :=
    ⟨⟨Classical.arbitrary (InfinitePlace F), IsTotallyReal.isReal _⟩⟩
  have hd : d ≠ 0 := Fintype.card_ne_zero
  have hcard : Fintype.card (Ix F) = d := by
    have := (B F).finrank_eq
    rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at this
  let r : Rp F → ℝ := fun w => Real.sqrt |(z w.1).im|
  have hr : ∀ w, 0 < r w := fun w => Real.sqrt_pos.2 (abs_pos.2 (hz w.1))
  have hr2 : ∀ w, r w ^ 2 = |(z w.1).im| := fun w => Real.sq_sqrt (abs_nonneg _)
  let α : Rp F → ℝ := fun w => t / r w
  let β : Rp F → ℝ := fun w => t * r w
  let xx : Rp F → ℝ := fun w => (z w.1).re
  let S := {p : (Rp F → ℝ) × (Rp F → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * xx w + p.2 w| ≤ β w}
  have hSm : MeasurableSet S := by
    have : IsClosed S := by
      simp only [S, Set.ofPred_forall, Set.ofPred_and]
      exact isClosed_iInter fun w =>
        (isClosed_le (by fun_prop) continuous_const).inter (isClosed_le (by fun_prop) continuous_const)
    exact this.measurableSet
  have hαβ : ∀ w, α w * β w = t ^ 2 := fun w => by
    simp only [α, β]; field_simp [(hr w).ne']
  have hvS : ((volume : Measure (Rp F → ℝ)).prod (volume : Measure (Rp F → ℝ))) S = ENNReal.ofReal ((4 * t ^ 2) ^ d) := by
    rw [vol_S α β xx (fun w => by positivity)]
    simp only [hαβ, Finset.prod_const, Finset.card_univ]
    rw [ENNReal.ofReal_pow (by positivity)]
  have hvs : volume ((Phi F) ⁻¹' S) = ENNReal.ofReal (c * (4 * t ^ 2) ^ d) := by
    have e1 : volume ((Phi F) ⁻¹' S) =
        Measure.map (Phi F).toContinuousLinearEquiv (volume : Measure (Ix F ⊕ Ix F → ℝ)) S := by
      rw [Measure.map_apply (Phi F).toContinuousLinearEquiv.continuous.measurable hSm]; rfl
    rw [e1, map_eq, Measure.smul_apply, hvS, ENNReal.smul_def, smul_eq_mul,
      ENNReal.ofReal_mul hc.le, hc_def, ENNReal.ofReal_coe_nnreal]
  have hsymm : ∀ y ∈ (Phi F) ⁻¹' S, -y ∈ (Phi F) ⁻¹' S := by
    intro y hy
    simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, map_neg] at hy ⊢
    intro w
    obtain ⟨h1, h2⟩ := hy w
    refine ⟨by simpa using h1, ?_⟩
    have e : (-(Phi F y)).1 w * xx w + (-(Phi F y)).2 w = -((Phi F y).1 w * xx w + (Phi F y).2 w) := by
      simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]; ring
    rw [e, abs_neg]; exact h2
  have hconvS : Convex ℝ S := by
    intro p hp q hq a b ha hb hab
    simp only [S, Set.mem_ofPred_eq] at hp hq ⊢
    intro w
    obtain ⟨h1, h2⟩ := hp w
    obtain ⟨h3, h4⟩ := hq w
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    constructor
    · calc |a * p.1 w + b * q.1 w| ≤ |a * p.1 w| + |b * q.1 w| := abs_add_le _ _
        _ = a * |p.1 w| + b * |q.1 w| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * α w + b * α w := by gcongr
        _ = α w := by rw [← add_mul, hab, one_mul]
    · calc |(a * p.1 w + b * q.1 w) * xx w + (a * p.2 w + b * q.2 w)|
          = |a * (p.1 w * xx w + p.2 w) + b * (q.1 w * xx w + q.2 w)| := by congr 1; ring
        _ ≤ |a * (p.1 w * xx w + p.2 w)| + |b * (q.1 w * xx w + q.2 w)| := abs_add_le _ _
        _ = a * |p.1 w * xx w + p.2 w| + b * |q.1 w * xx w + q.2 w| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * β w + b * β w := by gcongr
        _ = β w := by rw [← add_mul, hab, one_mul]
  have hconv : Convex ℝ ((Phi F) ⁻¹' S) := hconvS.linear_preimage (Phi F).toLinearMap
  have hF0 : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Ix F ⊕ Ix F))) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp [Real.volume_Ico]
  have key : (2 : ℝ) ^ (d + d) < c * (4 * t ^ 2) ^ d := by
    have h4 : (2 : ℝ) ^ (d + d) = 4 ^ d := by rw [pow_add, ← mul_pow]; norm_num
    have ht2 : t ≤ (t ^ 2) ^ d :=
      le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) hd)
    have hct : c * t = c + 1 := by rw [ht_def]; field_simp
    have h4p : (0 : ℝ) < 4 ^ d := by positivity
    rw [h4, mul_pow]
    calc (4 : ℝ) ^ d < 4 ^ d * (c * t) := by rw [hct]; nlinarith
      _ ≤ 4 ^ d * (c * (t ^ 2) ^ d) := by gcongr
      _ = c * (4 ^ d * (t ^ 2) ^ d) := by ring
  have hvol : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Ix F ⊕ Ix F))) *
      2 ^ finrank ℝ (Ix F ⊕ Ix F → ℝ) < volume ((Phi F) ⁻¹' S) := by
    rw [hF0, one_mul, hvs, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, hcard]
    rw [show (2 : ENNReal) ^ (d + d) = ENNReal.ofReal ((2 : ℝ) ^ (d + d)) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 key
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Ix F ⊕ Ix F)))).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Ix F ⊕ Ix F)))))
  obtain ⟨⟨y, hyL⟩, hy0, hys⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (μ := volume) (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Ix F ⊕ Ix F)) volume)
    hsymm hconv hvol
  have hint : ∀ j, ∃ n : ℤ, y j = n := by
    intro j
    obtain ⟨n, hn⟩ := (Basis.mem_span_iff_repr_mem (R := ℤ) (Pi.basisFun ℝ (Ix F ⊕ Ix F)) y).1 hyL j
    exact ⟨n, by simpa using hn.symm⟩
  choose n hn using hint
  set a : F := ∑ i, (n (Sum.inl i) : F) * integralBasis F i with ha_def
  set b : F := ∑ i, (n (Sum.inr i) : F) * integralBasis F i with hb_def
  have hPhi : Phi F y = (B F (fun i => (n (Sum.inl i) : ℝ)), B F (fun i => (n (Sum.inr i) : ℝ))) := by
    rw [Phi_apply]; congr 1 <;> congr 1 <;> funext i <;> exact hn _
  have hys' : Phi F y ∈ S := hys
  rw [hPhi] at hys'
  simp only [S, Set.mem_ofPred_eq] at hys'
  refine ⟨![a, b], ?_, ?_, ?_⟩
  · intro h0
    have ha0 : a = 0 := by simpa using congrFun h0 0
    have hb0 : b = 0 := by simpa using congrFun h0 1
    have hm : (fun i => (n (Sum.inl i) : ℝ)) = 0 := by
      apply (B F).injective
      rw [map_zero]; funext w
      rw [← emb_sum F (fun i => n (Sum.inl i)) w, ← ha_def, ha0, map_zero]; rfl
    have hm' : (fun i => (n (Sum.inr i) : ℝ)) = 0 := by
      apply (B F).injective
      rw [map_zero]; funext w
      rw [← emb_sum F (fun i => n (Sum.inr i)) w, ← hb_def, hb0, map_zero]; rfl
    apply hy0
    apply Subtype.ext
    funext j
    cases j with
    | inl i => show y (Sum.inl i) = 0; rw [hn]; simpa using congrFun hm i
    | inr i => show y (Sum.inr i) = 0; rw [hn]; simpa using congrFun hm' i
  · exact Fin.forall_fin_two.2 ⟨sum_integral F _, sum_integral F _⟩
  · intro v
    obtain ⟨h1, h2⟩ := hys' ⟨v, IsTotallyReal.isReal v⟩
    rw [← emb_sum F (fun i => n (Sum.inl i))] at h1
    rw [← emb_sum F (fun i => n (Sum.inl i)), ← emb_sum F (fun i => n (Sum.inr i))] at h2
    have h1' : |InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) a|
        ≤ t / r ⟨v, IsTotallyReal.isReal v⟩ := h1
    have h2' : |InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) a * (z v).re +
        InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) b|
        ≤ t * r ⟨v, IsTotallyReal.isReal v⟩ := h2
    have hrv : 0 < r ⟨v, IsTotallyReal.isReal v⟩ := hr _
    have hr2v : r ⟨v, IsTotallyReal.isReal v⟩ ^ 2 = |(z v).im| := hr2 _
    show ‖((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) a : ℝ) : ℂ) * z v +
        ((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) b : ℝ) : ℂ)‖ ^ 2
        ≤ 2 * t ^ 2 * |(z v).im|
    clear_value r α β xx S a b c t
    generalize InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) a = A at h1' h2' ⊢
    generalize InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) b = Bb at h2' ⊢
    generalize r ⟨v, IsTotallyReal.isReal v⟩ = R at hrv hr2v h1' h2'
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.mul_im, zero_mul, sub_zero, add_zero, mul_zero]
    have e1 : (A * (z v).re + Bb) ^ 2 ≤ (t * R) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2' 2
    have e2 : A ^ 2 ≤ (t / R) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1' 2
    have hy2 : (z v).im ^ 2 = R ^ 4 := by
      rw [← sq_abs, ← hr2v]; ring
    have e3 : A ^ 2 * (z v).im ^ 2 ≤ t ^ 2 * R ^ 2 := by
      calc A ^ 2 * (z v).im ^ 2 ≤ (t / R) ^ 2 * (z v).im ^ 2 :=
            mul_le_mul_of_nonneg_right e2 (sq_nonneg _)
        _ = t ^ 2 * R ^ 2 := by
          rw [hy2, div_pow, div_mul_eq_mul_div, div_eq_iff (by positivity)]; ring
    have e4 : (t * R) ^ 2 = t ^ 2 * R ^ 2 := by ring
    rw [← hr2v]
    nlinarith [e1, e3, e4]

end UpperTheory.Esk.MinkowskiBoundLemmas

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aMink : AMink := fun F _ _ _ => MinkowskiBoundLemmas.core F

end UpperTheory.Esk
