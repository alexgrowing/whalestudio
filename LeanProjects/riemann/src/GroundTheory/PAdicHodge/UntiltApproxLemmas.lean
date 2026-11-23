import Mathlib
import GroundTheory.PAdicHodge.TiltAlgebra
import GroundTheory.PAdicHodge.AxLemma
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial

section Conj

variable {F E : Type*} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [NormedField E] [NormedAlgebra F E]

theorem norm_eq_of_isConjRoot {x x' : E} (hx : IsIntegral F x) (h : IsConjRoot F x x') :
    ‖x‖ = ‖x'‖ := by
  have hx' : IsIntegral F x' := h.isIntegral hx
  have e1 := NormedAlgebra.norm_eq_spectralNorm F (⟨x, hx⟩ : algebraicClosure F E)
  have e2 := NormedAlgebra.norm_eq_spectralNorm F (⟨x', hx'⟩ : algebraicClosure F E)
  change ‖x‖ = _ at e1
  change ‖x'‖ = _ at e2
  rw [e1, e2, spectralNorm, spectralNorm, IntermediateField.minpoly_eq,
    IntermediateField.minpoly_eq]
  change spectralValue (minpoly F x) = spectralValue (minpoly F x')
  rw [h]

theorem mem_range_of_norm_sub_lt [IsAlgClosed E] {α : E} (b : F) (hα : IsSeparable F α)
    (h : ∀ α' : E, IsConjRoot F α α' → α ≠ α' → ‖α - algebraMap F E b‖ < ‖α - α'‖) :
    α ∈ Set.range (algebraMap F E) := by
  have hαi : IsIntegral F α := hα.isIntegral
  let L := algebraicClosure F E
  let x : L := ⟨α, hαi⟩
  have : IsKrasner F L := IsKrasner.of_completeSpace F L
  have hxsep : (minpoly F x).Separable := by
    rw [IntermediateField.minpoly_eq]; exact hα
  have sp : ((minpoly F x).map (algebraMap F L)).Splits := by
    rw [IntermediateField.minpoly_eq]
    refine IntermediateField.splits_of_splits (IsAlgClosed.splits _) fun z hz => ?_
    rw [mem_rootSet] at hz
    exact ⟨minpoly F α, minpoly.monic hαi, by rw [← aeval_def]; exact hz.2⟩
  have key := IsKrasner.krasner hxsep sp (isIntegral_algebraMap (x := b)) fun x' hx' hne => by
    have hc : IsConjRoot F α (x' : E) := by
      unfold IsConjRoot at hx' ⊢
      rwa [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq] at hx'
    have hne' : α ≠ (x' : E) := fun e => hne (Subtype.ext e)
    exact h x' hc hne'
  rw [IntermediateField.adjoin_simple_eq_bot_iff.2 (IntermediateField.algebraMap_mem _ _)] at key
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 key
  exact ⟨c, congrArg Subtype.val hc⟩

end Conj

section Roots

variable {E : Type*} [NormedField E] [IsUltrametricDist E]

theorem norm_le_one_of_eval_eq_zero {f : E[X]} (hf : f.Monic) (hc : ∀ n, ‖f.coeff n‖ ≤ 1)
    {r : E} (hr : f.eval r = 0) : ‖r‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  set d := f.natDegree
  have hr0 : 0 < ‖r‖ := one_pos.trans hlt
  have hsum : ‖∑ i ∈ Finset.range d, f.coeff i * r ^ i‖ < ‖r‖ ^ d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd]; simp
    have hle : ∀ i ∈ Finset.range d, ‖f.coeff i * r ^ i‖ ≤ ‖r‖ ^ (d - 1) := by
      intro i hi
      rw [norm_mul, norm_pow]
      calc ‖f.coeff i‖ * ‖r‖ ^ i ≤ 1 * ‖r‖ ^ i := by gcongr; exact hc i
        _ = ‖r‖ ^ i := one_mul _
        _ ≤ ‖r‖ ^ (d - 1) := pow_le_pow_right₀ hlt.le (by
            have := Finset.mem_range.1 hi; omega)
    calc ‖∑ i ∈ Finset.range d, f.coeff i * r ^ i‖ ≤ ‖r‖ ^ (d - 1) := by
          have := norm_multiset_sum_le_of_forall_le (s := (Finset.range d).val.map
            fun i => f.coeff i * r ^ i) (pow_nonneg hr0.le _) (by
              intro a ha
              obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 ha
              exact hle i hi)
          simpa [Finset.sum_eq_multiset_sum] using this
      _ < ‖r‖ ^ d := pow_lt_pow_right₀ hlt (by omega)
  have heval : f.eval r = ∑ i ∈ Finset.range d, f.coeff i * r ^ i + r ^ d := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, one_mul]
  rw [heval] at hr
  have : ‖r ^ d‖ = ‖∑ i ∈ Finset.range d, f.coeff i * r ^ i‖ := by
    rw [eq_neg_of_add_eq_zero_right hr, norm_neg]
  rw [norm_pow] at this
  exact (lt_irrefl _) (this ▸ hsum)

theorem norm_coeff_prod_X_sub_C_le_one {s : Multiset E} (hs : ∀ r ∈ s, ‖r‖ ≤ 1) (k : ℕ) :
    ‖((s.map fun r => X - C r).prod).coeff k‖ ≤ 1 := by
  by_cases hk : k ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hk, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
    simpa using norm_esymm_le zero_le_one hs (Multiset.card s - k)
  · rw [coeff_eq_zero_of_natDegree_lt]
    · simp
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

end Roots

section Tilt

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField C p]

local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem exists_multiset_eq_prod [IsAlgClosed C♭] {Q : 𝒪C♭[X]} (hQ : Q.Monic) :
    ∃ s : Multiset 𝒪C♭, Q = (s.map fun b => X - Polynomial.C b).prod := by
  set f := Q.map (algebraMap 𝒪C♭ C♭)
  have hfm : f.Monic := hQ.map _
  have hfc : ∀ n, ‖f.coeff n‖ ≤ 1 := fun n => by
    rw [coeff_map, norm_algebraMap_preTilt]; exact preTilt_norm_le_one _
  have hroot : ∀ r ∈ f.roots, ‖r‖ ≤ 1 := fun r hr =>
    norm_le_one_of_eval_eq_zero hfm hfc (isRoot_of_mem_roots hr)
  classical
  let g : C♭ → 𝒪C♭ := fun r =>
    if h : ‖r‖ ≤ 1 then (norm_le_one_iff_exists_algebraMap.1 h).choose else 0
  have hg : ∀ r ∈ f.roots, algebraMap 𝒪C♭ C♭ (g r) = r := fun r hr => by
    simp only [g, dif_pos (hroot r hr)]
    exact (norm_le_one_iff_exists_algebraMap.1 (hroot r hr)).choose_spec
  have hf : f = (f.roots.map fun r => X - Polynomial.C r).prod :=
    (IsAlgClosed.splits f).eq_prod_roots_of_monic hfm
  refine ⟨f.roots.map g, map_injective _ (IsFractionRing.injective 𝒪C♭ C♭) ?_⟩
  change f = _
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  conv_lhs => rw [hf]
  congr 1
  refine Multiset.map_congr rfl fun r hr => ?_
  simp [hg r hr]

theorem norm_prod_sub_untilt_le (s : Multiset 𝒪C♭) {Q : (normInteger C)[X]}
    (hQ : Q.map (Ideal.Quotient.mk (Ideal.span {(p : normInteger C)})) =
      ((s.map fun b => X - Polynomial.C b).prod).map (PreTilt.coeff 0))
    {z : normInteger C} (hz : Q.eval z = 0) :
    ‖(s.map fun b => (z : C) - ((PreTilt.untilt b : normInteger C) : C)).prod‖ ≤ ‖(p : C)‖ := by
  set mk := Ideal.Quotient.mk (Ideal.span {(p : normInteger C)})
  set R : (normInteger C)[X] := (s.map fun b => X - Polynomial.C (PreTilt.untilt b)).prod
  have h1 : ((s.map fun b => X - Polynomial.C b).prod).map (PreTilt.coeff 0) = R.map mk := by
    simp only [R, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, mk, PreTilt.mk_untilt_eq_coeff_zero]
  have h2 : mk (R.eval z) = 0 := by
    rw [← eval₂_at_apply, ← eval_map, ← h1, ← hQ, eval_map, eval₂_at_apply, hz, map_zero]
  have h3 := (mk_eq_zero_iff_norm_le (p := p)).1 h2
  have h4 : ((R.eval z : normInteger C) : C) =
      (s.map fun b => (z : C) - ((PreTilt.untilt b : normInteger C) : C)).prod := by
    simp only [R, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub, eval_X,
      eval_C]
    rw [← (normInteger C).subtype_apply, map_multiset_prod, Multiset.map_map]
    rfl
  rw [← h4]
  exact h3

def monicOfCoeffs (e : ℕ) (a : ℕ → 𝒪C♭) : 𝒪C♭[X] :=
  X ^ e + ∑ m ∈ Finset.range e, Polynomial.C (a m) * X ^ m

theorem monic_monicOfCoeffs (e : ℕ) (a : ℕ → 𝒪C♭) : (monicOfCoeffs e a).Monic := by
  refine Polynomial.monic_X_pow_add ?_
  refine (Polynomial.degree_sum_le _ _).trans_lt ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe e)).2 fun m hm => ?_
  refine (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact WithBot.coe_lt_coe.2 (Finset.mem_range.1 hm)

theorem coeff_monicOfCoeffs (e : ℕ) (a : ℕ → 𝒪C♭) (m : ℕ) :
    (monicOfCoeffs e a).coeff m = if m = e then 1 else if m < e then a m else 0 := by
  simp only [monicOfCoeffs, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
  split_ifs with h1 h2
  · subst h1
    rw [Finset.sum_eq_zero fun i hi => if_neg (by have := Finset.mem_range.1 hi; omega), add_zero]
  · rw [Finset.sum_eq_single m (fun i _ hi => if_neg (Ne.symm hi)) (fun h => absurd
      (Finset.mem_range.2 h2) h), if_pos rfl, zero_add]
  · rw [zero_add, Finset.sum_eq_zero fun i hi => if_neg (by
      have := Finset.mem_range.1 hi; omega)]

theorem natDegree_monicOfCoeffs (e : ℕ) (a : ℕ → 𝒪C♭) : (monicOfCoeffs e a).natDegree = e := by
  have hm := monic_monicOfCoeffs e a
  refine le_antisymm (natDegree_le_iff_coeff_eq_zero.2 fun m hm' => ?_) ?_
  · rw [coeff_monicOfCoeffs, if_neg (by
      have : e < m := by exact_mod_cast hm'
      omega), if_neg (by
      have : e < m := by exact_mod_cast hm'
      omega)]
  · refine le_natDegree_of_ne_zero ?_
    rw [coeff_monicOfCoeffs, if_pos rfl]
    exact one_ne_zero

theorem exists_root_norm_sub_untilt_pow_le [IsAlgClosed C♭] {Q : (normInteger C)[X]}
    (hQ : Q.Monic) (hdeg : 0 < Q.natDegree) (a : ℕ → 𝒪C♭)
    (ha : ∀ m < Q.natDegree, Ideal.Quotient.mk (Ideal.span {(p : normInteger C)}) (Q.coeff m) =
      PreTilt.coeff 0 (a m))
    {z : normInteger C} (hz : Q.eval z = 0) :
    ∃ b : 𝒪C♭, (monicOfCoeffs Q.natDegree a).eval b = 0 ∧
      ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ^ Q.natDegree ≤ ‖(p : C)‖ := by
  set e := Q.natDegree
  obtain ⟨s, hs⟩ := exists_multiset_eq_prod (monic_monicOfCoeffs (C := C) (p := p) e a)
  have hcard : Multiset.card s = e := by
    have := natDegree_monicOfCoeffs (C := C) (p := p) e a
    rw [hs, natDegree_multiset_prod_X_sub_C_eq_card] at this
    exact this
  have hQ' : Q.map (Ideal.Quotient.mk (Ideal.span {(p : normInteger C)})) =
      ((s.map fun b => X - Polynomial.C b).prod).map (PreTilt.coeff 0) := by
    rw [← hs]
    ext m
    rw [coeff_map, coeff_map, coeff_monicOfCoeffs]
    split_ifs with h1 h2
    · subst h1; rw [hQ.coeff_natDegree, map_one, map_one]
    · exact ha m h2
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero, map_zero]
  have hprod := norm_prod_sub_untilt_le s hQ' hz
  rw [norm_multiset_prod_eq, Multiset.map_map] at hprod
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hcard; omega
  obtain ⟨b, hb, hbl⟩ := exists_pow_card_le_of_prod_le hs0 (fun _ _ => norm_nonneg _) hprod
  refine ⟨b, ?_, by rwa [hcard] at hbl⟩
  rw [hs, eval_multiset_prod]
  exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map.2 ⟨b, hb, rfl⟩,
    by simp⟩)

end Tilt

section Scale

theorem exists_lt_one_le_pow {q : ℝ} (hq : q < 1) (d : ℕ) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ q ≤ μ ^ d := by
  set q' := max q 0
  have hq' : q' < 1 := max_lt hq one_pos
  have hq0 : 0 ≤ q' := le_max_right _ _
  rcases Nat.eq_zero_or_pos d with hd | hd
  · exact ⟨1 / 2, by norm_num, by norm_num, by rw [hd, pow_zero]; exact hq.le⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set a : ℝ := -((1 - q') / (2 * d))
  have ha1 : (1 - q') / (2 * d) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have ha0 : 0 < (1 - q') / (2 * d) := by
    apply div_pos <;> linarith
  refine ⟨1 + a, by simp only [a]; linarith, by simp only [a]; linarith, ?_⟩
  have hb := one_add_mul_le_pow (a := a) (by simp only [a]; linarith) d
  have : (d : ℝ) * a = -((1 - q') / 2) := by
    simp only [a]; field_simp
  rw [this] at hb
  calc q ≤ q' := le_max_left _ _
    _ ≤ 1 + -((1 - q') / 2) := by linarith
    _ ≤ _ := hb

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]

theorem map_scale_eq_prod {Q : F[X]} (hQ : Q.Monic) (β c : F) (hc : c ≠ 0) :
    (Polynomial.C (c⁻¹ ^ Q.natDegree) * Q.comp (Polynomial.C β + Polynomial.C c * X)).map
        (algebraMap F E) =
      ((Q.map (algebraMap F E)).roots.map fun γ =>
        X - Polynomial.C ((γ - algebraMap F E β) / algebraMap F E c)).prod := by
  set f := Q.map (algebraMap F E)
  have hf : f = (f.roots.map fun γ => X - Polynomial.C γ).prod :=
    (IsAlgClosed.splits f).eq_prod_roots_of_monic (hQ.map _)
  have hcard : Multiset.card f.roots = Q.natDegree := by
    rw [← (IsAlgClosed.splits f).natDegree_eq_card_roots, natDegree_map]
  have hc' : algebraMap F E c ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).2 hc
  rw [Polynomial.map_mul, Polynomial.map_C, map_comp, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_C, Polynomial.map_X]
  change _ * f.comp _ = _
  conv_lhs => rw [hf]
  rw [multiset_prod_comp, Multiset.map_map, ← hcard]
  have key : ∀ γ : E, (X - Polynomial.C γ).comp (Polynomial.C (algebraMap F E β) +
      Polynomial.C (algebraMap F E c) * X) = Polynomial.C (algebraMap F E c) *
      (X - Polynomial.C ((γ - algebraMap F E β) / algebraMap F E c)) := by
    intro γ
    simp only [sub_comp, X_comp, C_comp, mul_sub, ← Polynomial.C_mul]
    rw [mul_div_cancel₀ _ hc', Polynomial.C_sub]
    ring
  simp only [Function.comp_def, key]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← mul_assoc,
    map_pow, map_inv₀, ← Polynomial.C_pow, ← Polynomial.C_mul, ← mul_pow, inv_mul_cancel₀ hc',
    one_pow, Polynomial.C_1, one_mul]

end Scale

section IntermediateField

variable {K C : Type*} [NontriviallyNormedField K] [NormedField C] [NormedAlgebra K C]

instance normedAlgebraIntermediateField (F : IntermediateField K C) : NormedAlgebra F C where
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul]
    rfl

end IntermediateField

end GroundTheory.PAdicHodge
