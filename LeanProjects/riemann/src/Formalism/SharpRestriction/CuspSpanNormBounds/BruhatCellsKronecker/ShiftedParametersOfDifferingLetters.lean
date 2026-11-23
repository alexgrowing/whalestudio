import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.PrimeIdealNormRpowSumLe

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryVolumeMass NumberField IsDedekindDomain
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HS

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hilbert_schmidt_eq_sum_basis (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
    | exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)
    | (rw [inner_self_eq_norm_sq_to_K]; simp [sq])

theorem hilbert_schmidt_sq_nonneg (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [hilbert_schmidt_eq_sum_basis]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem sq_le_weighted_sum_sq (a b c t : ℝ) (hc : 0 ≤ c) (h : c ≤ a + b) (ht : 0 < t) :
    c ^ 2 ≤ (1 + t) * b ^ 2 + (1 + 1 / t) * a ^ 2 := by
  have h1 : c ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hc h 2
  have key : t * b ^ 2 + 1 / t * a ^ 2 - 2 * a * b = (t * b - a) ^ 2 / t := by
    field_simp
    ring
  have h2 : 0 ≤ (t * b - a) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  nlinarith

theorem hilbert_schmidt_add_le (X Y : Wq →L[ℂ] Wp) {t : ℝ} (ht : 0 < t) :
    hsNormSq (X + Y) ≤ (1 + t) * hsNormSq Y + (1 + 1 / t) * hsNormSq X := by
  rw [hilbert_schmidt_eq_sum_basis, hilbert_schmidt_eq_sum_basis, hilbert_schmidt_eq_sum_basis, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [ContinuousLinearMap.add_apply]
  exact sq_le_weighted_sum_sq _ _ _ t (norm_nonneg _) (norm_add_le _ _) ht

end HS

section Sums

variable {T V : Type*} [NormedAddCommGroup V] [CompleteSpace V]

theorem tsum_split_four (a : T → V) (ha : Summable a) (S1 S2 S3 S4 : Set T)
    (h : ∀ t, a t = S1.indicator a t + S2.indicator a t + S3.indicator a t + S4.indicator a t) :
    ∑' t, a t = ∑' t : S1, a t + ∑' t : S2, a t + ∑' t : S3, a t + ∑' t : S4, a t := by
  have h1 := ha.indicator S1
  have h2 := ha.indicator S2
  have h3 := ha.indicator S3
  have h4 := ha.indicator S4
  rw [tsum_congr h, ((h1.add h2).add h3).tsum_add h4, (h1.add h2).tsum_add h3, h1.tsum_add h2]
  simp only [tsum_subtype]

theorem tsum_split_two (a : T → V) (ha : Summable a) (S S1 S2 : Set T)
    (h : ∀ t, S.indicator a t = S1.indicator a t + S2.indicator a t) :
    ∑' t : S, a t = ∑' t : S1, a t + ∑' t : S2, a t := by
  simp only [tsum_subtype]
  rw [← (ha.indicator S1).tsum_add (ha.indicator S2)]
  exact tsum_congr h

end Sums

section Parts

variable (D : D7) (u u' : D.what₂.Word)

theorem kernel_matrix_decomposition (hE : KExpansion D.s u u') (hid : ∀ t : D.s.Term u u', D.s.isId t → D.s.Gterm t = 0) :
    Kmat D.s u u' = KOf D.s u u' {t | D.s.isId t} + Kpp D u u' + Kng D u u' + KOf D.s u u' (famG D.s) := by
  haveI := FiniteDimensional.complete ℂ (D.s.Cu u)
  rw [← hE.tsum_eq]
  unfold Kpp Kng KOf
  refine tsum_split_four _ hE.summable _ _ _ _ (fun t => ?_)
  by_cases h1 : D.s.isId t
  · have h2 := hid t h1
    simp [Set.indicator, famNG, famG, h1, h2]
  · by_cases h2 : D.s.Gterm t = 0
    · simp [Set.indicator, famNG, famG, h1, h2]
    · by_cases h3 : D.s.generic t
      · simp [Set.indicator, famNG, famG, h1, h2, h3]
      · simp [Set.indicator, famNG, famG, h1, h2, h3]

def genericLoopPairs : Set (D.s.Pair u u') := {p | p ∈ pairsIn D.s (famG D.s) ∧ loopP D.s p}

theorem generic_pairs_tsum_split (hs : Summable (fun p : D.s.Pair u u' => ‖D.s.pval p‖))
    (h3 : ∀ p : D.s.Pair u u', D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → 1 ≤ D.s.s0 p) :
    ∑' p : pairsIn D.s (famG D.s (u := u) (u' := u')), D.s.pval p.1 =
      ∑' p : genericLoopPairs D u u', D.s.pval p.1 + ∑' p : scalG D u u', D.s.pval p.1 := by
  refine tsum_split_two (fun p => D.s.pval p) hs.of_norm _ _ _ (fun p => ?_)
  by_cases hp : p ∈ pairsIn D.s (famG D.s (u := u) (u' := u'))
  · have hg1 : D.s.generic (D.s.pfst p) := hp.1.2.2
    have hg2 : D.s.generic (D.s.psnd p) := hp.2.2.2
    have hG1 : D.s.Gterm (D.s.pfst p) ≠ 0 := hp.1.2.1
    have hG2 : D.s.Gterm (D.s.psnd p) ≠ 0 := hp.2.2.1
    have h1 := h3 p hG1 hG2
    by_cases hsc : scalarP D.s p
    · have hl : ¬ loopP D.s p := by
        rintro ⟨_, _, h | h⟩
        · have := hsc.2.2.1; omega
        · exact h.2.2.2 hsc.2.2.2
      have m1 : p ∉ genericLoopPairs D u u' := fun h => hl h.2
      have m2 : p ∈ scalG D u u' := ⟨hp, hsc⟩
      rw [Set.indicator_of_mem hp, Set.indicator_of_notMem m1, Set.indicator_of_mem m2, zero_add]
    · have hl : loopP D.s p := by
        refine ⟨hG1, hG2, ?_⟩
        by_cases h2 : 2 ≤ D.s.s0 p
        · exact Or.inl h2
        · refine Or.inr ⟨hg1, hg2, by omega, fun h => hsc ⟨hg1, hg2, by omega, h⟩⟩
      have m1 : p ∈ genericLoopPairs D u u' := ⟨hp, hl⟩
      have m2 : p ∉ scalG D u u' := fun h => hsc h.2
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem m1, Set.indicator_of_notMem m2, add_zero]
  · have m1 : p ∉ genericLoopPairs D u u' := fun h => hp h.1
    have m2 : p ∉ scalG D u u' := fun h => hp h.1
    rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem m1, Set.indicator_of_notMem m2, add_zero]

theorem generic_loop_sum_bound (c : ℝ) (hB : LoopPairSumBound D u u' c) (hs : Summable (fun p : D.s.Pair u u' => ‖D.s.pval p‖)) :
    gaG D * (∑' p : genericLoopPairs D u u', D.s.pval p.1).re ≤
      Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) *
        ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar := by
  have hga : 0 ≤ gaG D := by
    unfold gaG
    refine finprod_mem_induction (fun x : ℝ => 0 ≤ x) zero_le_one (fun x y hx hy => mul_nonneg hx hy) ?_
    intro p _
    refine Finset.prod_nonneg (fun i _ => ?_)
    have hn : Ideal.absNorm p.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact p.ne_bot
    have h1 : (1:ℝ) ≤ (Ideal.absNorm p.asIdeal : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have := one_le_pow₀ (n := i) h1
    linarith
  have hsL : Summable (fun p : genericLoopPairs D u u' => ‖D.s.pval p.1‖) := hs.subtype _
  have hfin : ∀ s : Finset (genericLoopPairs D u u'), ∑ p ∈ s, gaG D * ‖D.s.pval p.1‖ ≤
      Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) *
        ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar := by
    intro s
    rw [← Finset.mul_sum]
    have := hB (s.map (Function.Embedding.subtype _)) (by
      intro q hq
      rw [Finset.mem_map] at hq
      obtain ⟨p, _, rfl⟩ := hq
      obtain ⟨_, hl⟩ := p.2
      exact hl)
    simpa only [Finset.sum_map, Function.Embedding.coe_subtype] using this
  have h1 : ∑' p : genericLoopPairs D u u', gaG D * ‖D.s.pval p.1‖ ≤
      Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) *
        ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar := by
    first
      | exact (hsL.mul_left (gaG D)).tsum_le_of_sum_le hfin
      | exact Summable.tsum_le_of_sum_le (hsL.mul_left (gaG D)) hfin
      | exact tsum_le_of_sum_le' (fun p => mul_nonneg hga (norm_nonneg _)) hfin
  rw [tsum_mul_left] at h1
  have h2 : (∑' p : genericLoopPairs D u u', D.s.pval p.1).re ≤ ∑' p : genericLoopPairs D u u', ‖D.s.pval p.1‖ := by
    first
      | exact (Complex.re_le_norm _).trans (norm_tsum_le_tsum_norm hsL)
      | exact (Complex.re_le_abs _).trans (norm_tsum_le_tsum_norm hsL)
  exact (mul_le_mul_of_nonneg_left h2 hga).trans h1

theorem one_le_typed_factor : 1 ≤ f3 D := by
  unfold f3
  refine finprod_mem_induction (fun x : ℝ => 1 ≤ x) le_rfl ?_ ?_
  · intro x y hx hy
    exact one_le_mul_of_one_le_of_one_le hx hy
  · intro p _
    exact le_add_of_nonneg_right (div_nonneg (by norm_num) (Nat.cast_nonneg _))

theorem generic_part_hilbert_schmidt_le (c : ℝ) (h2a : c2aG D) (hB : LoopPairSumBound D u u' c)
    (hs : Summable (fun p : D.s.Pair u u' => ‖D.s.pval p‖))
    (h3 : ∀ p : D.s.Pair u u', D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → 1 ≤ D.s.s0 p) :
    hsNormSq (KOf D.s u u' (famG D.s)) ≤
      f3 D * (Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) *
        ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar) +
      f3 D * gaG D * (∑' p : scalG D u u', D.s.pval p.1).re := by
  have hG : ∀ t ∈ famG D.s (u := u) (u' := u'), D.s.Gterm t ≠ 0 := fun t ht => ht.2.1
  have h1 := h2a u u' (famG D.s) (Or.inl rfl) hG (hs.subtype _)
  rw [generic_pairs_tsum_split D u u' hs h3, Complex.add_re, mul_add] at h1
  have h4 := generic_loop_sum_bound D u u' c hB hs
  have hf := one_le_typed_factor D
  have h5 : f3 D * gaG D * (∑' p : genericLoopPairs D u u', D.s.pval p.1).re ≤
      f3 D * (Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) *
        ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h4 (by linarith)
  linarith

theorem generic_scalar_eq (hid : ∀ t : D.s.Term u u', D.s.isId t → D.s.Gterm t = 0) :
    genScal D u u' = f3 D * gaG D * (∑' p : scalG D u u', D.s.pval p.1).re := by
  classical
  unfold genScal f3
  congr 2
  rw [tsum_subtype (scalG D u u') (fun p => D.s.pval p)]
  refine tsum_congr (fun p => ?_)
  by_cases hp : p ∈ scalG D u u'
  · rw [Set.indicator_of_mem hp, if_pos ⟨hp.2, hp.1.1.2.1, hp.1.2.2.1⟩]
  · rw [Set.indicator_of_notMem hp, if_neg]
    rintro ⟨h1, h2, h3⟩
    exact hp ⟨⟨⟨fun h => h2 (hid _ h), h2, h1.1⟩, ⟨fun h => h3 (hid _ h), h3, h1.2.1⟩⟩, h1⟩

end Parts

section Record

open scoped nonZeroDivisors

variable (D : D7) (large₂ : SizeData₂ D)

theorem shifted_parameter_letter (u : D.what₂.Word) (τ : D.what₂.Tau) (l : ℕ) (h : l < D.R.k - 2) :
    uS D u τ ⟨l + 1, by omega⟩ =
      (((D.hc τ).v ⟨l, by omega⟩ : ℚ) : ℝ) - 1 / 2 - (if D.s.letter u ⟨l, h⟩ then (D.s.Del : ℝ) else 0) := by
  unfold uS
  rw [D.s.u_letter u τ l h, D.hcW_v]
  split_ifs <;> push_cast <;> ring

theorem shifted_parameter_succ (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (h : i < D.R.k) :
    uOne D u τ (i + 1) = uS D u τ ⟨i, h⟩ := by
  unfold uOne
  rw [dif_pos (by omega)]
  exact congrArg (uS D u τ) (Fin.ext (by simp))

theorem vertex_parameter_eq (τ : D.what₂.Tau) (l : ℕ) (h : l < D.R.k - 1) :
    vOne D τ (l + 1) = (((D.hc τ).v ⟨l, h⟩ : ℚ) : ℝ) := by
  unfold vOne
  rw [dif_pos (by omega)]
  simp

theorem separating_interval_real (v Δ x y : ℝ) (hΔ : 5 ≤ Δ)
    (hxy : (x = v - 1 / 2 - Δ ∧ y = v - 1 / 2 - 0) ∨ (x = v - 1 / 2 - 0 ∧ y = v - 1 / 2 - Δ)) :
    x ≠ y ∧ 5 / 2 - v ≤ Δ / 2 - v ∧ min (-x) (-y) < 5 / 2 - v ∧ Δ / 2 - v < max (-x) (-y) ∧
      ∀ z ∈ Set.Icc (5 / 2 - v) (Δ / 2 - v), 2 ≤ |z + x| ∧ 2 ≤ |z + y| := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨fun h => by linarith, by linarith, min_lt_iff.2 (Or.inr (by linarith)),
      lt_max_iff.2 (Or.inl (by linarith)), fun z hz => ⟨?_, ?_⟩⟩
    · rw [le_abs]
      right
      linarith [hz.2]
    · rw [le_abs]
      left
      linarith [hz.1]
  · refine ⟨fun h => by linarith, by linarith, min_lt_iff.2 (Or.inl (by linarith)),
      lt_max_iff.2 (Or.inr (by linarith)), fun z hz => ⟨?_, ?_⟩⟩
    · rw [le_abs]
      left
      linarith [hz.1]
    · rw [le_abs]
      right
      linarith [hz.2]

theorem shifted_parameters_of_differing_letters (u u' : D.what₂.Word) (τ : D.what₂.Tau) (l : ℕ) (h : l < D.R.k - 2)
    (hne : D.s.letter u ⟨l, h⟩ ≠ D.s.letter u' ⟨l, h⟩) :
    (uS D u τ ⟨l + 1, by omega⟩ = vOne D τ (l + 1) - 1 / 2 - (D.s.Del : ℝ) ∧
      uS D u' τ ⟨l + 1, by omega⟩ = vOne D τ (l + 1) - 1 / 2 - 0) ∨
    (uS D u τ ⟨l + 1, by omega⟩ = vOne D τ (l + 1) - 1 / 2 - 0 ∧
      uS D u' τ ⟨l + 1, by omega⟩ = vOne D τ (l + 1) - 1 / 2 - (D.s.Del : ℝ)) := by
  rw [shifted_parameter_letter D u τ l h, shifted_parameter_letter D u' τ l h, vertex_parameter_eq D τ l (by omega)]
  split_ifs <;> simp_all

theorem separating_interval (u u' : D.what₂.Word) (τ : D.what₂.Tau) (l : ℕ) (h : l < D.R.k - 2)
    (hne : D.s.letter u ⟨l, h⟩ ≠ D.s.letter u' ⟨l, h⟩) (hDel : 5 ≤ (D.s.Del : ℝ)) :
    IsCutS (uS D u τ) (uS D u' τ)
      (Set.Icc (5 / 2 - vOne D τ (l + 1)) ((D.s.Del : ℝ) / 2 - vOne D τ (l + 1))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    separating_interval_real (vOne D τ (l + 1)) (D.s.Del : ℝ) _ _ hDel (shifted_parameters_of_differing_letters D u u' τ l h hne)
  unfold IsCutS
  exact ⟨⟨l + 1, by omega⟩, _, _, h1, h2, rfl, h3, h4, h5⟩

def s76x (u u' : D.what₂.Word) (l : ℕ) : D.what₂.Tau → LocalDataRealPlace D := fun τ =>
  { lam := lamSH D.R (D.hc τ), u := uS D u τ, u' := uS D u' τ,
    l := ⟨0, by have := D.R.m_add_three_le_k; omega⟩,
    a := 5 / 2 - vOne D τ l, b := (D.s.Del : ℝ) / 2 - vOne D τ l,
    a1 := 5 / 2 - vOne D τ l, b1 := NA D ^ 3 - vOne D τ l }

def s76L : LatticeDataWithDual D :=
  { La := fun _ _ => ⊥, La' := fun _ _ => ⊥,
    aaV := fun i s => ddE D ^ (-((2 * ((D.R.rS : ℤ) + 1) - i - (i + s - 1)) + 1)) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹,
    aaP := fun i s => ddE D ^ (-(2 * ((D.R.rS : ℤ) + 1) - i - (i + s - 1))) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹,
    κ := 0, ρ := rhoReal D }

theorem local_condition_holds (u u' : D.what₂.Word) (l : ℕ) : IsLocC D u u' l (s76x D u u' l) :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

theorem lattice_global_holds : IsLatGLOB D (s76L D) := fun _ _ => ⟨rfl, rfl, rfl⟩

def nongenericFactor (c C : ℝ) : ℝ :=
  Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) +
    (2 : ℝ) ^ (-((D.R.k : ℝ) - 2 * (D.R.rS : ℝ) - 5)) * Real.exp (C * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L)

def loopFactor (c : ℝ) : ℝ := Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ)))

structure AdmissibleConstantInequalities (ca : AdmissibleBoundsFromSource.AdmC) : Prop where
  cut : ca.CA * ((D.R.k : ℝ) * NA D * ((D.R.rS : ℝ) + 1) ^ 2 + NA D ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 + NA D ^ 3) ≤
    (D.s.Del : ℝ) / 2 - 5 / 2
  cut2 : NA D ^ 3 ≤ (D.s.Del : ℝ) / 2
  th : ca.CA' ≤ (D.R.k : ℝ) ^ ca.c5
  off : ∃ t : ℝ, 0 < t ∧
    (1 + t) * (f3 D * loopFactor D ca.cL + (1 + ca.CA * large₂.sc.b ^ (-7 : ℝ)) * (1 + eSum D ca.Ce) * f3 D) +
      (1 + 1 / t) * nongenericFactor D large₂ ca.cN ca.CN ≤ 1 + AdmissibleBoundsFromSource.eta0 D large₂
  diag : ∃ t : ℝ, 0 < t ∧
    (1 + t) * (f3 D * loopFactor D ca.cL + f3 D * Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L)) +
      (1 + 1 / t) * nongenericFactor D large₂ ca.cN ca.CN ≤ AdmissibleBoundsFromSource.Gam D

theorem error_sum_nonneg (Ce : ℝ) (h : 0 ≤ Ce) : 0 ≤ eSum D Ce := by
  unfold eSum
  exact mul_nonneg h (tsum_nonneg (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem twenty_le_count : (20 : ℝ) ≤ NA D := by
  unfold NA
  have := (Nat.cast_nonneg D.R.rS : (0:ℝ) ≤ (D.R.rS : ℝ))
  linarith

theorem dstar_pos_generic : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq D.u₀]; exact (D.mem D.u₀).A.Dstar_pos

theorem theorem_S_of_numerical_inequalities (C0 C' Cl Cg cb Cu cT CT : ℝ) (ca : AdmissibleBoundsFromSource.AdmC) (hOk : ca.Ok Cg) (hC' : 1 ≤ C') (hCl : 2 < Cl)
    (hH : AdmissibleBoundsFromSource.hyp D large₂ C0 C' Cl Cg cb Cu cT CT) (hA : AdmissibleBoundsFromSource.Adm1 D large₂ C0 C' Cl Cg cb Cu cT CT ca)
    (hN : AdmissibleConstantInequalities D large₂ ca) : AdmissibleBoundsFromSource.Conclusion1 D large₂ := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, -, -, a13, a14, a15⟩ := hA
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, -⟩ := hOk
  have hD := hH.1
  have hS := hH.2.1
  have h0 := hH.2.2
  have p6 : AdmissibleBoundsFromSource.DiagonalKernelBoundParameters D large₂ Cl Cg CT := (NonGenericAndKTwoTheorems.Hyp_of D large₂ C' Cl Cg cb Cu cT CT C0 hD hS h0 hC').2
  have e1 := a1 hH
  have e2 := a2 hH
  have e3 := a3 hH p6
  have e4 := a4 hH
  have e5 := a5 hH p6
  have e7 := a7 hH
  have e8 := a8 hH
  have e9 := a9 hH
  have e13 := a13 hH
  have e14 := a14 hH
  have e15 := a15 hH
  have hsz : Sizes3b D ca.A5 := by
    refine ⟨fun u u' => (e13.2.2.1 u u').trans o3, fun u u' τ => ?_⟩
    have hC1 : 0 ≤ ca.C1 := by
      refine le_trans ?_ (e13.2.1 u u τ)
      by_cases hz : Tcrit D u τ = 0
      · simp [hz]
      · rw [div_self hz]; exact zero_le_one
    exact (vand_ratio_of D ca.C1 e13.2.1 u u' τ).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC1 o2 _) (vand_uS_pos D u τ).le)
  have p5 : ∀ u u' : D.what₂.Word, AdmissibleBoundsFromSource.WordPairParameters D large₂ u u' Cl ca.A5 := fun u u' =>
    (count_hypotheses_of_sizes D large₂ C' Cl Cg cb Cu cT CT C0 ca.A5 hD hS h0 hCl hC' o1 hsz u u').2
  have e6 := fun u u' => a6 hH u u' (p5 u u')
  have hDst := dstar_pos_generic D
  have hf3 : 0 ≤ f3 D := le_trans zero_le_one (one_le_typed_factor D)
  have c1 : ∀ u u' : D.what₂.Word, u ≠ u' → Kpp D u u' = 0 := by
    intro u u' hne
    unfold Kpp KOf
    rw [tsum_congr (fun t : ↥{t : D.s.Term u u' | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} => e3 u u' hne t.1 t.2.1), tsum_zero]
  refine ⟨c1, e5, ?_, ?_⟩
  · intro u u' hne
    have hid : ∀ t : D.s.Term u u', D.s.isId t → D.s.Gterm t = 0 := (e14 u u').2.1
    have hsplit := kernel_matrix_decomposition D u u' (e1 u u').1 hid
    have hId : KOf D.s u u' {t | D.s.isId t} = 0 := by
      unfold KOf
      rw [tsum_congr (fun t : ↥{t : D.s.Term u u' | D.s.isId t} => e3 u u' hne t.1 (hid t.1 t.2)), tsum_zero]
    have hK : Kmat D.s u u' - Kpp D u u' = Kng D u u' + KOf D.s u u' (famG D.s) := by
      rw [hsplit, hId]; abel
    obtain ⟨t, ht, hoff⟩ := hN.off
    have hadd := hilbert_schmidt_add_le (Kng D u u') (KOf D.s u u' (famG D.s)) ht
    have hng := e7 u u'
    have hgen := generic_part_hilbert_schmidt_le D u u' ca.cL e4 (e6 u u') (e15 u u') (e14 u u').2.2
    rw [← generic_scalar_eq D u u' hid] at hgen
    obtain ⟨l, hl⟩ : ∃ l : Fin (D.R.k - 2), D.s.letter u l ≠ D.s.letter u' l := by
      by_contra hcon
      push_neg at hcon
      exact hne (D.s.letter_inj (funext hcon))
    have hl2 := l.2
    have hNA := twenty_le_count D
    have hNA3 : (5 : ℝ) ≤ NA D ^ 3 := by nlinarith [sq_nonneg (NA D)]
    have hcutpos : 0 ≤ ca.CA * ((D.R.k : ℝ) * NA D * ((D.R.rS : ℝ) + 1) ^ 2 + NA D ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 +
        NA D ^ 3) := by
      have : (0 : ℝ) ≤ NA D := by linarith
      positivity
    have hDel : 5 ≤ (D.s.Del : ℝ) := by linarith [hN.cut]
    have hth := e13.2.2.2 u u' (l.1 + 1) (by omega) (by omega)
      (fun τ => by
        rw [shifted_parameter_succ D u τ (l.1 + 1) (by omega), shifted_parameter_succ D u' τ (l.1 + 1) (by omega)]
        exact (separating_interval_real _ _ _ _ hDel (shifted_parameters_of_differing_letters D u u' τ l.1 l.2 hl)).1)
      (s76x D u u' (l.1 + 1)) (s76L D) (local_condition_holds D u u' _) (lattice_global_holds D)
    have hb7 : large₂.sc.b ^ (-7 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (sc_one_lt_b large₂).le (by norm_num)
    have h9 := e9 u u' hne (s76x D u u' (l.1 + 1)) (s76L D) (local_condition_holds D u u' _).1 (lattice_global_holds D)
      (fun τ => ⟨separating_interval D u u' τ l.1 l.2 hl hDel, by
          show _ ≤ ((D.s.Del : ℝ) / 2 - vOne D τ (l.1 + 1)) - (5 / 2 - vOne D τ (l.1 + 1))
          linarith [hN.cut], le_rfl, by
          show NA D ^ 3 - vOne D τ (l.1 + 1) ≤ (D.s.Del : ℝ) / 2 - vOne D τ (l.1 + 1)
          linarith [hN.cut2], by
          show _ ≤ (NA D ^ 3 - vOne D τ (l.1 + 1)) - (5 / 2 - vOne D τ (l.1 + 1))
          linarith⟩)
      (le_trans hth.2 hb7) (le_trans hN.th hth.1)
    set Th := ThA D ca.CA u u' (s76x D u u' (l.1 + 1)) (s76L D) with hTh
    set X : ℝ := (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar with hX
    have hX0 : 0 ≤ X := by positivity
    have he0 := error_sum_nonneg D ca.Ce o10
    have g1 : genScal D u u' ≤ (1 + ca.CA * large₂.sc.b ^ (-7 : ℝ)) * (1 + eSum D ca.Ce) * f3 D * X := by
      refine le_trans h9 ?_
      have q1 : ca.CA * ((D.R.rS : ℝ) + 1) * (ca.CA / Th) ^ (D.R.f : ℝ) ≤ ca.CA * large₂.sc.b ^ (-7 : ℝ) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hth.2 o8.le
      have q2 : (1 + ca.CA * ((D.R.rS : ℝ) + 1) * (ca.CA / Th) ^ (D.R.f : ℝ)) * (1 + eSum D ca.Ce) * f3 D * AdmissibleBoundsFromSource.du D u *
          AdmissibleBoundsFromSource.du D u' / AdmissibleBoundsFromSource.Dst D =
          (1 + ca.CA * ((D.R.rS : ℝ) + 1) * (ca.CA / Th) ^ (D.R.f : ℝ)) * ((1 + eSum D ca.Ce) * f3 D * X) := by
        rw [hX]; unfold AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst; ring
      rw [q2]
      have q3 : (1 + ca.CA * large₂.sc.b ^ (-7 : ℝ)) * (1 + eSum D ca.Ce) * f3 D * X =
          (1 + ca.CA * large₂.sc.b ^ (-7 : ℝ)) * ((1 + eSum D ca.Ce) * f3 D * X) := by ring
      rw [q3]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have g2 : hsNormSq (KOf D.s u u' (famG D.s)) ≤
        (f3 D * loopFactor D ca.cL + (1 + ca.CA * large₂.sc.b ^ (-7 : ℝ)) * (1 + eSum D ca.Ce) * f3 D) * X := by
      refine le_trans hgen ?_
      have : f3 D * (Real.exp (-(ca.cL * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) *
          ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar) = f3 D * loopFactor D ca.cL * X := by
        rw [hX]; unfold loopFactor; ring
      rw [this]
      linarith
    have g3 : hsNormSq (Kng D u u') ≤ nongenericFactor D large₂ ca.cN ca.CN * X := by
      refine le_trans hng (le_of_eq ?_)
      rw [hX]; unfold nongenericFactor; ring
    rw [hK]
    have ht1 : 0 ≤ 1 + t := by linarith
    have ht2 : 0 ≤ 1 + 1 / t := by positivity
    calc hsNormSq (Kng D u u' + KOf D.s u u' (famG D.s))
        ≤ (1 + t) * hsNormSq (KOf D.s u u' (famG D.s)) + (1 + 1 / t) * hsNormSq (Kng D u u') := hadd
      _ ≤ (1 + t) * ((f3 D * loopFactor D ca.cL + (1 + ca.CA * large₂.sc.b ^ (-7 : ℝ)) * (1 + eSum D ca.Ce) * f3 D) * X) +
          (1 + 1 / t) * (nongenericFactor D large₂ ca.cN ca.CN * X) :=
        add_le_add (mul_le_mul_of_nonneg_left g2 ht1) (mul_le_mul_of_nonneg_left g3 ht2)
      _ = ((1 + t) * (f3 D * loopFactor D ca.cL + (1 + ca.CA * large₂.sc.b ^ (-7 : ℝ)) * (1 + eSum D ca.Ce) * f3 D) +
          (1 + 1 / t) * nongenericFactor D large₂ ca.cN ca.CN) * X := by ring
      _ ≤ (1 + AdmissibleBoundsFromSource.eta0 D large₂) * X := mul_le_mul_of_nonneg_right hoff hX0
      _ = (1 + AdmissibleBoundsFromSource.eta0 D large₂) * AdmissibleBoundsFromSource.du D u * AdmissibleBoundsFromSource.du D u' / AdmissibleBoundsFromSource.Dst D := by
        rw [hX]; unfold AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst; ring
  · intro u
    have hid : ∀ t : D.s.Term u u, D.s.isId t → D.s.Gterm t = 0 := (e14 u u).2.1
    have hsplit := kernel_matrix_decomposition D u u (e1 u u).1 hid
    have hId : KOf D.s u u {t | D.s.isId t} = ContinuousLinearMap.id ℂ (D.s.Cu u) := (e2 u).tsum_eq
    have hK : Kmat D.s u u - Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u) =
        Kng D u u + KOf D.s u u (famG D.s) := by
      rw [hsplit, hId]; abel
    obtain ⟨t, ht, hdg⟩ := hN.diag
    have hadd := hilbert_schmidt_add_le (Kng D u u) (KOf D.s u u (famG D.s)) ht
    have hng := e7 u u
    have hgen := generic_part_hilbert_schmidt_le D u u ca.cL e4 (e6 u u) (e15 u u) (e14 u u).2.2
    set X : ℝ := (D.duS u : ℝ) * (D.duS u : ℝ) / D.what₂.Dstar with hX
    have hX0 : 0 ≤ X := by positivity
    have g1 : f3 D * gaG D * (∑' p : scalG D u u, D.s.pval p.1).re ≤
        f3 D * Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) * X := by
      have q1 : gaG D * (∑' p : scalG D u u, D.s.pval p.1).re =
          ((gaG D : ℂ) * ∑' p : scalG D u u, D.s.pval p.1).re := by
        rw [Complex.re_ofReal_mul]
      have q2 := le_trans (Complex.re_le_norm _) (e8 u).2
      rw [← q1] at q2
      have q3 : Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) * (D.duS u : ℝ) ^ 2 / D.what₂.Dstar =
          Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) * X := by rw [hX]; ring
      rw [q3] at q2
      calc _ = f3 D * (gaG D * (∑' p : scalG D u u, D.s.pval p.1).re) := by ring
        _ ≤ f3 D * (Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) * X) :=
          mul_le_mul_of_nonneg_left q2 hf3
        _ = _ := by ring
    have g2 : hsNormSq (KOf D.s u u (famG D.s)) ≤
        (f3 D * loopFactor D ca.cL + f3 D * Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L)) * X := by
      refine le_trans hgen ?_
      have : f3 D * (Real.exp (-(ca.cL * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) *
          ((D.duS u : ℝ) * (D.duS u : ℝ)) / D.what₂.Dstar) = f3 D * loopFactor D ca.cL * X := by
        rw [hX]; unfold loopFactor; ring
      rw [this]
      linarith
    have g3 : hsNormSq (Kng D u u) ≤ nongenericFactor D large₂ ca.cN ca.CN * X := by
      refine le_trans hng (le_of_eq ?_)
      rw [hX]; unfold nongenericFactor; ring
    rw [hK]
    have ht1 : 0 ≤ 1 + t := by linarith
    have ht2 : 0 ≤ 1 + 1 / t := by positivity
    calc hsNormSq (Kng D u u + KOf D.s u u (famG D.s))
        ≤ (1 + t) * hsNormSq (KOf D.s u u (famG D.s)) + (1 + 1 / t) * hsNormSq (Kng D u u) := hadd
      _ ≤ (1 + t) * ((f3 D * loopFactor D ca.cL + f3 D * Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L)) * X) +
          (1 + 1 / t) * (nongenericFactor D large₂ ca.cN ca.CN * X) :=
        add_le_add (mul_le_mul_of_nonneg_left g2 ht1) (mul_le_mul_of_nonneg_left g3 ht2)
      _ = ((1 + t) * (f3 D * loopFactor D ca.cL + f3 D * Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L)) +
          (1 + 1 / t) * nongenericFactor D large₂ ca.cN ca.CN) * X := by ring
      _ ≤ AdmissibleBoundsFromSource.Gam D * X := mul_le_mul_of_nonneg_right hdg hX0
      _ = AdmissibleBoundsFromSource.Gam D * AdmissibleBoundsFromSource.du D u ^ 2 / AdmissibleBoundsFromSource.Dst D := by
        rw [hX]; unfold AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst; ring

end Record

section Numbers

theorem off_diagonal_numerics (F E e A δ CA η : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hF0 : 0 ≤ F) (hF : F ≤ 1 + δ) (hE0 : 0 ≤ E)
    (hE : E ≤ δ) (he : e ≤ δ) (hA : A ≤ δ ^ 3) (hCA : 0 ≤ CA) (hη : (13 + 8 * CA) * δ ≤ η) :
    (1 + δ) * (F * E + (1 + CA * δ) * (1 + e) * F) + (1 + 1 / δ) * A ≤ 1 + η := by
  have hd1 : 0 ≤ 1 + δ := by linarith
  have a1 : (1 + e) * F ≤ (1 + δ) * (1 + δ) := by
    nlinarith [mul_nonneg (sub_nonneg.2 he) hF0, mul_nonneg hd1 (sub_nonneg.2 hF)]
  have a3 : (1 + CA * δ) * (1 + e) * F ≤ (1 + CA * δ) * ((1 + δ) * (1 + δ)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left a1 (by nlinarith [mul_nonneg hCA hδ0.le])
  have a4 : F * E ≤ (1 + δ) * δ := mul_le_mul hF hE hE0 hd1
  have a5 : (1 + 1 / δ) * A ≤ δ ^ 3 + δ ^ 2 := by
    have e : (1 + 1 / δ) * δ ^ 3 = δ ^ 3 + δ ^ 2 := by
      field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have a6 : (1 + δ) * (F * E + (1 + CA * δ) * (1 + e) * F) ≤
      (1 + δ) * ((1 + δ) * δ + (1 + CA * δ) * ((1 + δ) * (1 + δ))) :=
    mul_le_mul_of_nonneg_left (by linarith) hd1
  have hd2 : δ ^ 2 ≤ δ := by nlinarith [mul_nonneg hδ0.le (sub_nonneg.2 hδ1)]
  have hd3 : δ ^ 3 ≤ δ := by nlinarith [mul_nonneg (pow_nonneg hδ0.le 2) (sub_nonneg.2 hδ1)]
  have hd4 : δ ^ 4 ≤ δ := by nlinarith [mul_nonneg (pow_nonneg hδ0.le 3) (sub_nonneg.2 hδ1)]
  have c2 := mul_le_mul_of_nonneg_left hd2 hCA
  have c3 := mul_le_mul_of_nonneg_left hd3 hCA
  have c4 := mul_le_mul_of_nonneg_left hd4 hCA
  have key : (1 + δ) * ((1 + δ) * δ + (1 + CA * δ) * ((1 + δ) * (1 + δ))) + (δ ^ 3 + δ ^ 2) =
      1 + 4 * δ + 6 * δ ^ 2 + 3 * δ ^ 3 + CA * δ + 3 * (CA * δ ^ 2) + 3 * (CA * δ ^ 3) + CA * δ ^ 4 := by
    ring
  have e2 : (13 + 8 * CA) * δ = 13 * δ + 8 * (CA * δ) := by ring
  linarith

theorem diagonal_numerics (F E x A G : ℝ) (hF : F ≤ 2) (hE0 : 0 ≤ E) (hE : E ≤ 1) (hx : 1 ≤ x) (hA : A ≤ 1)
    (hG : 10 * x ≤ G) : (1 + 1) * (F * E + F * x) + (1 + 1 / 1) * A ≤ G := by
  have h1 : F * E + F * x ≤ 2 * (E + x) := by
    have e : F * E + F * x = F * (E + x) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hF (by linarith)
  have h2 : (1 + 1 : ℝ) * (F * E + F * x) + (1 + 1 / 1) * A = 2 * (F * E + F * x) + 2 * A := by ring
  rw [h2]
  linarith

theorem basic_scale_inequalities (k m f L C' CG CN : ℝ) (hm : 2 ≤ m) (hf : 2 ≤ f) (hL : 1 < L) (a1 : 8 * CG ≤ C')
    (a2 : C' * m ^ 5 * f * L ≤ k) (hCG1 : 1 ≤ CG) (hCGN : CN + 1 ≤ CG) :
    64 * L ≤ m ^ 5 * f * L ∧ 8 * (m ^ 5 * f * L) ≤ k ∧ CN * (m ^ 5 * f * L) ≤ k / 8 ∧ m ≤ m ^ 5 * f * L := by
  have hm0 : 0 ≤ m := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hm5 : (32:ℝ) ≤ m ^ 5 := by
    calc (32:ℝ) = 2 ^ 5 := by norm_num
      _ ≤ m ^ 5 := pow_le_pow_left₀ (by norm_num) hm 5
  have hm4 : (16:ℝ) ≤ m ^ 4 := by
    calc (16:ℝ) = 2 ^ 4 := by norm_num
      _ ≤ m ^ 4 := pow_le_pow_left₀ (by norm_num) hm 4
  have hX0 : 0 ≤ m ^ 5 * f * L := mul_nonneg (mul_nonneg (pow_nonneg hm0 5) hf0) hL0
  have h64 : 64 ≤ m ^ 5 * f := by
    have := mul_le_mul hm5 hf (by norm_num) (pow_nonneg hm0 5)
    linarith
  have h32 : 32 ≤ m ^ 4 * f := by
    have := mul_le_mul hm4 hf (by norm_num) (pow_nonneg hm0 4)
    linarith
  have hY : 1 ≤ m ^ 4 * f * L := by
    have := mul_le_mul h32 hL.le (by norm_num) (mul_nonneg (pow_nonneg hm0 4) hf0)
    linarith
  have hC8 : 8 ≤ C' := by linarith
  have e1 : C' * (m ^ 5 * f * L) = C' * m ^ 5 * f * L := by ring
  have b1 := mul_le_mul_of_nonneg_right hC8 hX0
  have b2 := mul_le_mul_of_nonneg_right (by linarith : CN ≤ C' / 8) hX0
  have e2 : C' / 8 * (m ^ 5 * f * L) = (C' * (m ^ 5 * f * L)) / 8 := by ring
  refine ⟨mul_le_mul_of_nonneg_right h64 hL0, by linarith, by linarith, ?_⟩
  have e3 : m ^ 5 * f * L = m * (m ^ 4 * f * L) := by ring
  rw [e3]
  exact le_mul_of_one_le_right hm0 hY

theorem two_pow_neg_le_exp_neg_half (k m r : ℝ) (hk : 2000 ≤ k) (hmk : m ≤ k / 8) (hrm : 2 * r + 2 = m) :
    (2 : ℝ) ^ (-(k - 2 * r - 5)) ≤ Real.exp (-(k / 2)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hl := Real.log_two_gt_d9
  have hpos : 0 ≤ k - 2 * r - 5 := by linarith
  have h1 := mul_le_mul_of_nonneg_right hl.le hpos
  have e : Real.log 2 * -(k - 2 * r - 5) = -(Real.log 2 * (k - 2 * r - 5)) := by ring
  rw [e]
  linarith

theorem loop_factor_le_exp (k f L c : ℝ) (hkL : 512 * L ≤ k) (hf : 2 ≤ f) (hL : 1 < L) (hc : 1 ≤ c * Real.log k) :
    Real.exp (-(c * k * f * Real.log k)) ≤ Real.exp (-(22 * L)) := by
  apply Real.exp_le_exp.mpr
  have hk0 : 0 ≤ k := by linarith
  have hkf : 0 ≤ k * f := mul_nonneg hk0 (by linarith)
  have e : c * k * f * Real.log k = (c * Real.log k) * (k * f) := by ring
  have h1 := mul_le_mul_of_nonneg_right hc hkf
  have h2 := mul_le_mul_of_nonneg_left hf hk0
  rw [e]
  linarith

theorem nongeneric_factor_le (k m f L r CN cN b : ℝ) (hb : b = Real.exp L) (h2b : 2 ≤ b) (hkL : 512 * L ≤ k) (hf : 2 ≤ f)
    (hL : 1 < L) (hc : 1 ≤ cN * Real.log k) (e2 : (2 : ℝ) ^ (-(k - 2 * r - 5)) ≤ Real.exp (-(k / 2)))
    (hCNM : CN * (m ^ 5 * f * L) ≤ k / 8) :
    Real.exp (-(cN * k * f * Real.log k)) + (2 : ℝ) ^ (-(k - 2 * r - 5)) * Real.exp (CN * m ^ 5 * f * L) ≤
      Real.exp (-(7 * L)) ^ 3 := by
  have hk0 : 0 ≤ k := by linarith
  have hkf : 0 ≤ k * f := mul_nonneg hk0 (by linarith)
  have t1 : Real.exp (-(cN * k * f * Real.log k)) ≤ Real.exp (-(192 * L)) := by
    apply Real.exp_le_exp.mpr
    have e : cN * k * f * Real.log k = (cN * Real.log k) * (k * f) := by ring
    have h1 := mul_le_mul_of_nonneg_right hc hkf
    have h2 := mul_le_mul_of_nonneg_left hf hk0
    rw [e]
    linarith
  have t2 : (2:ℝ) ^ (-(k - 2 * r - 5)) * Real.exp (CN * m ^ 5 * f * L) ≤ Real.exp (-(192 * L)) := by
    calc (2:ℝ) ^ (-(k - 2 * r - 5)) * Real.exp (CN * m ^ 5 * f * L)
        ≤ Real.exp (-(k / 2)) * Real.exp (CN * m ^ 5 * f * L) :=
          mul_le_mul_of_nonneg_right e2 (Real.exp_pos _).le
      _ = Real.exp (-(k / 2) + CN * m ^ 5 * f * L) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(192 * L)) := by
          apply Real.exp_le_exp.mpr
          have e : CN * m ^ 5 * f * L = CN * (m ^ 5 * f * L) := by ring
          rw [e]
          linarith
  have t3 : 2 * Real.exp (-(192 * L)) ≤ Real.exp (-(7 * L)) ^ 3 := by
    have h1 : (2:ℝ) ≤ Real.exp (171 * L) := by
      have := Real.add_one_le_exp (171 * L)
      linarith
    have h2 : Real.exp (-(7 * L)) ^ 3 = Real.exp (171 * L) * Real.exp (-(192 * L)) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  linarith

theorem error_term_le_exp_neg (k f L r Ce b : ℝ) (hb : b = Real.exp L) (hCe : 0 ≤ Ce) (hCb : 8 * Ce ≤ b) (hkL : 512 * L ≤ k)
    (hfk : f ≤ k) (hf : 2 ≤ f) (hL : 1 < L) (e2 : (2 : ℝ) ^ (-(k - 2 * r - 5)) ≤ Real.exp (-(k / 2))) :
    Ce * (f * (2 : ℝ) ^ (2 - (k - 2 * r - 3))) ≤ Real.exp (-(7 * L)) := by
  have hk0 : 0 ≤ k := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hexp : (2:ℝ) ^ (2 - (k - 2 * r - 3)) = (2:ℝ) ^ (-(k - 2 * r - 5)) := by
    congr 1
    ring
  rw [hexp]
  have hb0 : 0 ≤ b / 8 := by
    rw [hb]
    positivity
  have s1 : Ce * (f * (2:ℝ) ^ (-(k - 2 * r - 5))) ≤ (b / 8) * (k * Real.exp (-(k / 2))) :=
    mul_le_mul (by linarith) (mul_le_mul hfk e2 (Real.rpow_nonneg (by norm_num) _) hk0)
      (mul_nonneg hf0 (Real.rpow_nonneg (by norm_num) _)) hb0
  have s2 : Real.exp L / 8 * (k * Real.exp (-(k / 2))) ≤ Real.exp (-(7 * L)) := by
    have h1 : k / 8 ≤ Real.exp (k / 2 - 8 * L) := by
      have := Real.add_one_le_exp (k / 2 - 8 * L)
      linarith
    have h2 : Real.exp (-(7 * L)) = Real.exp (k / 2 - 8 * L) * (Real.exp L * Real.exp (-(k / 2))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [h2]
    have h3 : 0 ≤ Real.exp L * Real.exp (-(k / 2)) := by positivity
    calc Real.exp L / 8 * (k * Real.exp (-(k / 2))) = k / 8 * (Real.exp L * Real.exp (-(k / 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 h3
  rw [hb] at s1
  linarith

theorem prod_local_factors_le (k L b g0 g1 : ℝ) (fn : ℕ) (hb : b = Real.exp L) (h12 : 12 ≤ b) (hk : 1 ≤ k) (hfk : (fn : ℝ) ≤ k)
    (a12 : (k * b) ^ 8 ≤ g0) (a14 : (k * b) ^ 8 ≤ g1) :
    ((1 + 3 / g0) * (1 + 3 / g1)) ^ fn ≤ 1 + Real.exp (-(7 * L)) := by
  have hb0 : 0 < b := by
    rw [hb]
    exact Real.exp_pos L
  have hk0 : 0 < k := by linarith
  have hP : 0 < (k * b) ^ 8 := pow_pos (mul_pos hk0 hb0) 8
  have hg0 : 0 < g0 := lt_of_lt_of_le hP a12
  have hg1 : 0 < g1 := lt_of_lt_of_le hP a14
  have hx0 : 3 / g0 ≤ 3 / (k * b) ^ 8 := div_le_div_of_nonneg_left (by norm_num) hP a12
  have hx1 : 3 / g1 ≤ 3 / (k * b) ^ 8 := div_le_div_of_nonneg_left (by norm_num) hP a14
  have hx0' : 0 ≤ 3 / g0 := div_nonneg (by norm_num) hg0.le
  have hx1' : 0 ≤ 3 / g1 := div_nonneg (by norm_num) hg1.le
  have s1 : (1 + 3 / g0) * (1 + 3 / g1) ≤ Real.exp (3 / g0 + 3 / g1) := by
    rw [Real.exp_add]
    exact mul_le_mul (by linarith [Real.add_one_le_exp (3 / g0)])
      (by linarith [Real.add_one_le_exp (3 / g1)]) (by linarith) (Real.exp_pos _).le
  have s2 : ((1 + 3 / g0) * (1 + 3 / g1)) ^ fn ≤ Real.exp ((fn : ℝ) * (3 / g0 + 3 / g1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) s1 fn
  have hy0 : 0 ≤ (fn : ℝ) * (3 / g0 + 3 / g1) := mul_nonneg (Nat.cast_nonneg _) (add_nonneg hx0' hx1')
  have hy1 : (fn : ℝ) * (3 / g0 + 3 / g1) ≤ k * (3 / (k * b) ^ 8 + 3 / (k * b) ^ 8) :=
    mul_le_mul hfk (by linarith) (add_nonneg hx0' hx1') hk0.le
  have hz : Real.exp (-(7 * L)) * b ^ 7 = 1 := by
    rw [hb, ← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  have hk7 : 1 ≤ k ^ 7 := one_le_pow₀ hk
  have hkb7 : 12 ≤ k ^ 7 * b := by
    have := mul_le_mul hk7 h12 (by norm_num) (by positivity : (0:ℝ) ≤ k ^ 7)
    linarith
  have hq : 12 * k ≤ Real.exp (-(7 * L)) * (k * b) ^ 8 := by
    have e : Real.exp (-(7 * L)) * (k * b) ^ 8 = (Real.exp (-(7 * L)) * b ^ 7) * (k * (k ^ 7 * b)) := by ring
    rw [e, hz, one_mul]
    have := mul_le_mul_of_nonneg_left hkb7 hk0.le
    linarith
  have hy2 : 2 * (k * (3 / (k * b) ^ 8 + 3 / (k * b) ^ 8)) ≤ Real.exp (-(7 * L)) := by
    rw [show 2 * (k * (3 / (k * b) ^ 8 + 3 / (k * b) ^ 8)) = 12 * k / (k * b) ^ 8 by ring, div_le_iff₀ hP]
    exact hq
  have hz1 : Real.exp (-(7 * L)) ≤ 1 := by
    have hb7 : 1 ≤ b ^ 7 := one_le_pow₀ (by linarith)
    have := mul_le_mul_of_nonneg_left hb7 (Real.exp_pos (-(7 * L))).le
    linarith
  have hyle1 : |(fn : ℝ) * (3 / g0 + 3 / g1)| ≤ 1 := by
    rw [abs_of_nonneg hy0]
    linarith
  have hexp := Real.abs_exp_sub_one_le hyle1
  rw [abs_of_nonneg hy0] at hexp
  have h3 := (abs_le.mp hexp).2
  linarith

theorem separation_numerics (k m f L r N Cl Del CA : ℝ) (hm : 2 ≤ m) (hf : 2 ≤ f) (hL : 1 < L) (hCl : 2 < Cl) (hCA : 0 < CA)
    (hm4f : m ^ 4 ≤ f) (hrm : 2 * r + 2 = m) (hN : N = 4 * 5 * (r + 1)) (a20 : (k * f * L) ^ Cl ≤ Del)
    (hk1 : 2 * (1030 * CA + 3) ≤ k) (hk2 : 3000 ≤ k) :
    CA * (k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ Del / 2 - 5 / 2 ∧ N ^ 3 ≤ Del / 2 := by
  subst hN
  have hs : 1 ≤ r + 1 := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hs0 : 0 ≤ r + 1 := by linarith
  have hm4 : m ^ 4 = 16 * (r + 1) ^ 4 := by
    rw [← hrm]
    ring
  have hf16 : 16 * (r + 1) ^ 4 ≤ f := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hS4 : 1 ≤ (r + 1) ^ 4 := one_le_pow₀ hs
  have hs34 : (r + 1) ^ 3 ≤ (r + 1) ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  have hP : 16 * (k * (r + 1) ^ 4) ≤ k * f * L := by
    have h1 : k * (16 * (r + 1) ^ 4) ≤ k * f := mul_le_mul_of_nonneg_left hf16 hk0
    have h2 : k * f ≤ k * f * L := le_mul_of_one_le_right (mul_nonneg hk0 hf0) hL.le
    linarith
  have hX : 3000 ≤ k * (r + 1) ^ 4 := by
    have := mul_le_mul hk2 hS4 (by norm_num) hk0
    linarith
  have hDel : (k * f * L) ^ 2 ≤ Del := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ k * f * L) hCl.le
    rw [Real.rpow_two] at h
    linarith
  have hP2 : (16 * (k * (r + 1) ^ 4)) ^ 2 ≤ (k * f * L) ^ 2 := pow_le_pow_left₀ (by linarith) hP 2
  have hQ : (16 * (k * (r + 1) ^ 4)) ^ 2 = 256 * (k * (r + 1) ^ 4) ^ 2 := by ring
  have hXQ : k * (r + 1) ^ 4 ≤ (k * (r + 1) ^ 4) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have hkXQ : k * (k * (r + 1) ^ 4) ≤ (k * (r + 1) ^ 4) ^ 2 := by
    have e : (k * (r + 1) ^ 4) ^ 2 = (k * (k * (r + 1) ^ 4)) * (r + 1) ^ 4 := by ring
    rw [e]
    exact le_mul_of_one_le_right (mul_nonneg hk0 (by linarith)) hS4
  have e : k * (4 * 5 * (r + 1)) * (r + 1) ^ 2 + (4 * 5 * (r + 1)) ^ 2 * (r + 1) ^ 2 + (4 * 5 * (r + 1)) ^ 3 =
      20 * (k * (r + 1) ^ 3) + 400 * (r + 1) ^ 4 + 8000 * (r + 1) ^ 3 := by ring
  have hk34 : k * (r + 1) ^ 3 ≤ k * (r + 1) ^ 4 := mul_le_mul_of_nonneg_left hs34 hk0
  have h84 : 8400 * (r + 1) ^ 4 ≤ 3 * (k * (r + 1) ^ 4) := by
    have := mul_le_mul_of_nonneg_right (by linarith : (8400:ℝ) ≤ 3 * k) (pow_nonneg hs0 4)
    linarith
  have hin : k * (4 * 5 * (r + 1)) * (r + 1) ^ 2 + (4 * 5 * (r + 1)) ^ 2 * (r + 1) ^ 2 + (4 * 5 * (r + 1)) ^ 3 ≤
      23 * (k * (r + 1) ^ 4) := by
    rw [e]
    linarith
  have hin0 : 0 ≤ k * (4 * 5 * (r + 1)) * (r + 1) ^ 2 + (4 * 5 * (r + 1)) ^ 2 * (r + 1) ^ 2 + (4 * 5 * (r + 1)) ^ 3 := by
    rw [e]
    have := mul_nonneg hk0 (pow_nonneg hs0 3)
    linarith [pow_nonneg hs0 4, pow_nonneg hs0 3]
  have hCAk : CA ≤ k := by linarith
  have hL1 := mul_le_mul hCAk hin hin0 hk0
  have e2 : k * (23 * (k * (r + 1) ^ 4)) = 23 * (k * (k * (r + 1) ^ 4)) := by ring
  have h3 : (4 * 5 * (r + 1)) ^ 3 = 8000 * (r + 1) ^ 3 := by ring
  have hs4X : 3000 * (r + 1) ^ 4 ≤ k * (r + 1) ^ 4 := mul_le_mul_of_nonneg_right hk2 (pow_nonneg hs0 4)
  constructor
  · linarith
  · rw [h3]
    linarith

variable (D : D7) (large₂ : SizeData₂ D)

theorem base_rpow_eq_exp (c : ℝ) : large₂.sc.b ^ c = Real.exp (c * large₂.sc.L) := by
  unfold Scale.b
  rw [← Real.exp_mul, mul_comm]

theorem assembly_numerics_of_large (C0 C' Cl Cg cb Cu cT CT : ℝ) (ca : AdmissibleBoundsFromSource.AdmC) (hOk : ca.Ok Cg) (hCl : 2 < Cl)
    (hG : AdmissibleBoundsFromSource.GamDef D large₂ ca.CE ca.CN) (hH : AdmissibleBoundsFromSource.hyp D large₂ C0 C' Cl Cg cb Cu cT CT)
    (hk1 : 2 * (1030 * ca.CA + 3) ≤ (D.R.k : ℝ)) (hk2 : 3000 ≤ (D.R.k : ℝ)) (hk3 : ca.CA' ≤ (D.R.k : ℝ) ^ ca.c5)
    (hk4 : 1 ≤ ca.cL * Real.log D.R.k) (hk5 : 1 ≤ ca.cN * Real.log D.R.k)
    (hb : 13 + 8 * ca.CA + 8 * ca.Ce ≤ large₂.sc.b) : AdmissibleConstantInequalities D large₂ ca := by
  obtain ⟨-, -, -, -, -, -, o7, o8, -, o10, -⟩ := hOk
  have hF3 : HostFactorProductPowerIdentity D := typed_factor_split_of_data D hH.1
  obtain ⟨a1, a2, a3, a4, -, -, -, -, -, -, -, a12, -, a14, -, -, -, -, -, a20, -⟩ := hH.2.1
  have hm2 := two_le_mR D
  have hf2 := two_le_fR D
  have hL1 := sc_one_lt_L large₂
  have hrm : 2 * (D.R.rS : ℝ) + 2 = (D.R.m : ℝ) := by exact_mod_cast two_rS_add_two D
  have hfk : (D.R.f : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast a4
  have hm4f : (D.R.m : ℝ) ^ 4 ≤ (D.R.f : ℝ) := by exact_mod_cast a3
  have hmaxE : ca.CE ≤ max ca.CE ca.CN := le_max_left _ _
  have hmaxN : ca.CN ≤ max ca.CE ca.CN := le_max_right _ _
  unfold AdmissibleBoundsFromSource.GamDef at hG
  obtain ⟨b1, b2, b3, b4⟩ := basic_scale_inequalities (D.R.k : ℝ) (D.R.m : ℝ) (D.R.f : ℝ) large₂.sc.L C' large₂.CGam ca.CN hm2 hf2 hL1 a1 a2
    (by linarith) (by linarith)
  have hkL : 512 * large₂.sc.L ≤ (D.R.k : ℝ) := by linarith
  have hbexp : large₂.sc.b = Real.exp large₂.sc.L := rfl
  have e2 := two_pow_neg_le_exp_neg_half (D.R.k : ℝ) (D.R.m : ℝ) (D.R.rS : ℝ) (by linarith) (by linarith) hrm
  have hδ0 : 0 < Real.exp (-(7 * large₂.sc.L)) := Real.exp_pos _
  have hδ1 : Real.exp (-(7 * large₂.sc.L)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hA : nongenericFactor D large₂ ca.cN ca.CN ≤ Real.exp (-(7 * large₂.sc.L)) ^ 3 :=
    nongeneric_factor_le _ _ _ _ _ _ _ _ hbexp (by linarith) hkL hf2 hL1 hk5 e2 b3
  have hA1 : nongenericFactor D large₂ ca.cN ca.CN ≤ 1 := le_trans hA (pow_le_one₀ hδ0.le hδ1)
  have hE : loopFactor D ca.cL ≤ Real.exp (-(7 * large₂.sc.L)) :=
    le_trans (loop_factor_le_exp _ _ _ _ hkL hf2 hL1 hk4) (Real.exp_le_exp.2 (by linarith))
  have hE0 : 0 ≤ loopFactor D ca.cL := (Real.exp_pos _).le
  have he : eSum D ca.Ce ≤ Real.exp (-(7 * large₂.sc.L)) :=
    le_trans (error_sum_le D ca.Ce o10 (by linarith))
      (error_term_le_exp_neg _ _ _ _ _ _ hbexp o10 (by linarith) hkL hfk hf2 hL1 e2)
  have hf3 : f3 D ≤ 1 + Real.exp (-(7 * large₂.sc.L)) := by
    have y0 : f3 D = (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f := hF3
    rw [y0, Fin.prod_univ_two]
    exact prod_local_factors_le _ _ _ _ _ _ hbexp (by linarith) (by linarith) hfk a12 a14
  have hf30 : 0 ≤ f3 D := le_trans zero_le_one (one_le_typed_factor D)
  obtain ⟨c1, c2⟩ := separation_numerics (D.R.k : ℝ) (D.R.m : ℝ) (D.R.f : ℝ) large₂.sc.L (D.R.rS : ℝ) (NA D) Cl (D.s.Del : ℝ) ca.CA
    hm2 hf2 hL1 hCl o8 hm4f hrm rfl a20 hk1 hk2
  refine ⟨c1, c2, hk3, ⟨Real.exp (-(7 * large₂.sc.L)), hδ0, ?_⟩, ⟨1, one_pos, ?_⟩⟩
  · have hb7 : large₂.sc.b ^ (-7 : ℝ) = Real.exp (-(7 * large₂.sc.L)) := by rw [base_rpow_eq_exp]; congr 1; ring
    rw [hb7]
    refine off_diagonal_numerics _ _ _ _ _ ca.CA _ hδ0 hδ1 hf30 hf3 hE0 hE he hA o8.le ?_
    unfold AdmissibleBoundsFromSource.eta0
    rw [base_rpow_eq_exp]
    have : Real.exp (-(6 : ℝ) * large₂.sc.L) = large₂.sc.b * Real.exp (-(7 * large₂.sc.L)) := by
      rw [hbexp, ← Real.exp_add]; congr 1; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hδ0.le
  · refine diagonal_numerics _ _ _ _ _ (by linarith) hE0 (le_trans hE hδ1) ?_ hA1 ?_
    · exact Real.one_le_exp (by positivity)
    · have hGam : AdmissibleBoundsFromSource.Gam D = Real.exp (large₂.CGam * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) := by
        unfold AdmissibleBoundsFromSource.Gam
        rw [← large₂.Gam_eq D.u₀, Real.exp_log (lt_trans one_pos (D.mem D.u₀).A.one_lt_gammaP)]
      rw [hGam]
      have hM0 : 0 ≤ (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L := by linarith
      have w1 : Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) *
          Real.exp ((D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) ≤
          Real.exp (large₂.CGam * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have : (ca.CE + 1) * ((D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) ≤
            large₂.CGam * ((D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) :=
          mul_le_mul_of_nonneg_right (by linarith) hM0
        calc _ = (ca.CE + 1) * ((D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) := by ring
          _ ≤ large₂.CGam * ((D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) := this
          _ = _ := by ring
      have w2 : (10 : ℝ) ≤ Real.exp ((D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) := by
        have := Real.add_one_le_exp ((D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L)
        linarith
      have w3 : 0 < Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) := Real.exp_pos _
      have w4 : Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) * 10 ≤
          Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) *
          Real.exp ((D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) := mul_le_mul_of_nonneg_left w2 w3.le
      linarith

end Numbers

section Family

variable {eps : ℝ} (Fm : FamP eps)

theorem theorem_S_family (gc : AdmissibleBoundsFromSource.GivC) (ca : AdmissibleBoundsFromSource.AdmC) (hCl : 2 < sCl Fm) : AdmissibleBoundsFromSource.PeriodFamilyStatement Fm gc ca := by
  intro _ hOk hG hA
  obtain ⟨⟨x1, A1⟩, ⟨x2, A2⟩, ⟨x3, A3⟩, ⟨x4, A4⟩, ⟨x5, A5⟩, ⟨x6, A6⟩, ⟨x7, A7⟩, ⟨x8, A8⟩, ⟨x9, A9⟩,
    ⟨⟨x11a, EigenbasisExists⟩, ⟨x11b, FunctionalCalculusLaws⟩, ⟨x11c, EigenspacesOrthogonalAlt⟩⟩, A12, ⟨x13, A13⟩, ⟨x14, A14⟩, ⟨x15, A15⟩⟩ := hA
  have o4 : 0 < ca.cL := hOk.2.2.2.1
  have o5 : 0 < ca.cN := hOk.2.2.2.2.1
  have oc5 : 0 < ca.c5 := hOk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨y0, _, hy0⟩ := ev_rpow oc5 ca.CA'
  obtain ⟨z1, _, Z1⟩ := ev_k Fm (max (max (2 * (1030 * ca.CA + 3)) 3000)
    (max y0 (max (Real.exp (1 / ca.cL)) (Real.exp (1 / ca.cN)))))
  obtain ⟨z2, _, Z2⟩ := ev_L Fm (13 + 8 * ca.CA + 8 * ca.Ce)
  refine ownEv_intro Fm (max (max (max (max x1 x2) (max x3 x4)) (max (max x5 x6) (max x7 x8)))
    (max (max (max x9 x11a) (max x11b x11c)) (max (max x13 x14) (max x15 (max z1 z2))))) (fun x hx hx1 i hH => ?_)
  have le1 : x1 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have le2 : x2 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have le3 : x3 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) (le_max_left _ _)
  have le4 : x4 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) (le_max_left _ _)
  have le5 : x5 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) (le_max_left _ _)
  have le6 : x6 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) (le_max_left _ _)
  have le7 : x7 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_left _ _)
  have le8 : x8 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_left _ _)
  have le9 : x9 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) (le_max_right _ _)
  have le11a : x11a ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) (le_max_right _ _)
  have le11b : x11b ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) (le_max_right _ _)
  have le11c : x11c ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) (le_max_right _ _)
  have le13 : x13 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have le14 : x14 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have le15 : x15 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have lez : max z1 z2 ≤ x := by
    refine le_trans ?_ hx
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have lez1 : z1 ≤ x := le_trans (le_max_left _ _) lez
  have lez2 : z2 ≤ x := le_trans (le_max_right _ _) lez
  have hGam : AdmissibleBoundsFromSource.GamDef (Fm.D x i) (Fm.L x i) ca.CE ca.CN := by
    unfold AdmissibleBoundsFromSource.GamDef; rw [Fm.CGam_eq]; exact hG
  have hC' : 1 ≤ sC' Fm := by
    have h1 : 8 * (Fm.L x i).CGam ≤ sC' Fm := hH.2.1.1
    have h2 : 0 ≤ ca.CE := hOk.2.2.2.2.2.2.1
    have h3 : ca.CE ≤ max ca.CE ca.CN := le_max_left _ _
    unfold AdmissibleBoundsFromSource.GamDef at hGam
    linarith
  have hk := Z1 x lez1 i
  have hkpos : (0 : ℝ) < ((Fm.D x i).R.k : ℝ) := by
    have : (3000 : ℝ) ≤ ((Fm.D x i).R.k : ℝ) :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
    linarith
  have hlog : ∀ c : ℝ, 0 < c → Real.exp (1 / c) ≤ ((Fm.D x i).R.k : ℝ) → 1 ≤ c * Real.log ((Fm.D x i).R.k : ℝ) := by
    intro c hc h
    have := (Real.le_log_iff_exp_le hkpos).2 h
    calc (1 : ℝ) = c * (1 / c) := by field_simp
      _ ≤ c * Real.log ((Fm.D x i).R.k : ℝ) := mul_le_mul_of_nonneg_left this hc.le
  have hN : AdmissibleConstantInequalities (Fm.D x i) (Fm.L x i) ca :=
    assembly_numerics_of_large (Fm.D x i) (Fm.L x i) gc.C0 (sC' Fm) (sCl Fm) gc.Cg gc.cb gc.Cu gc.cT gc.CT ca hOk hCl hGam hH
      (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk)
      (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk)
      (hy0 _ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk))
      (hlog _ o4 (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hk))
      (hlog _ o5 (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hk))
      (by
        have h1 := Z2 x lez2 i
        have h2 := Real.add_one_le_exp (Fm.L x i).sc.L
        have h3 : (Fm.L x i).sc.b = Real.exp (Fm.L x i).sc.L := rfl
        linarith)
  exact theorem_S_of_numerical_inequalities (Fm.D x i) (Fm.L x i) gc.C0 (sC' Fm) (sCl Fm) gc.Cg gc.cb gc.Cu gc.cT gc.CT ca hOk hC' hCl hH
    ⟨A1 x le1 i, A2 x le2 i, A3 x le3 i, A4 x le4 i, A5 x le5 i, A6 x le6 i, A7 x le7 i, A8 x le8 i, A9 x le9 i,
      ⟨EigenbasisExists x le11a i, FunctionalCalculusLaws x le11b i, EigenspacesOrthogonalAlt x le11c i⟩, A12, A13 x le13 i, A14 x le14 i, A15 x le15 i⟩ hN

end Family

section Forms

theorem theorem_S_of_large_parameters (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ) (ca : AdmissibleBoundsFromSource.AdmC) (hCl : 2 < Cl)
    (hk1 : 2 * (1030 * ca.CA + 3) ≤ (D.R.k : ℝ)) (hk2 : 3000 ≤ (D.R.k : ℝ)) (hk3 : ca.CA' ≤ (D.R.k : ℝ) ^ ca.c5)
    (hk4 : 1 ≤ ca.cL * Real.log D.R.k) (hk5 : 1 ≤ ca.cN * Real.log D.R.k)
    (hb : 13 + 8 * ca.CA + 8 * ca.Ce ≤ large₂.sc.b) : AdmissibleBoundsFromSource.IntegralityFromMetric D large₂ C0 C' Cl Cg cb Cu cT CT ca := by
  intro hOk hG hH hA
  have hC' : 1 ≤ C' := by
    have h1 : 8 * large₂.CGam ≤ C' := hH.2.1.1
    have h2 : 0 ≤ ca.CE := hOk.2.2.2.2.2.2.1
    have h3 : ca.CE ≤ max ca.CE ca.CN := le_max_left _ _
    unfold AdmissibleBoundsFromSource.GamDef at hG
    linarith
  exact theorem_S_of_numerical_inequalities D large₂ C0 C' Cl Cg cb Cu cT CT ca hOk hC' hCl hH hA
    (assembly_numerics_of_large D large₂ C0 C' Cl Cg cb Cu cT CT ca hOk hCl hG hH hk1 hk2 hk3 hk4 hk5 hb)

theorem theorem_S_closed_form (𝒞 : Formalism.MainNotions.FamClass) : AdmissibleBoundsFromSource.ClosedFormWithDensityConstant 𝒞 := fun gc ca =>
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 3⟩, fun Fm _ _ hL =>
    theorem_S_family Fm gc ca (lt_of_lt_of_le (by norm_num) (le_sC'_sCl hL).2)⟩⟩

end Forms

end Formalism.MainNotions.BridgeLemma

end
