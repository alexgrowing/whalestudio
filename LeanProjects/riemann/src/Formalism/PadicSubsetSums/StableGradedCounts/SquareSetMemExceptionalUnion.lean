import Formalism.PadicSubsetSums.StableGradedCounts.CrossFactorCount

open Finset Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem primeToPart_eq_self_of_not_dvd {M : Type} [Monoid M] {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0)
    {x : M} (hx : x ^ n = 1) (hln : ¬ l ∣ n) : primeToPart l x = x := by
  have hdvd : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hx
  have hnd : ¬ l ∣ orderOf x := fun h => hln (h.trans hdvd)
  have h0 : (orderOf x).factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
  simp only [primeToPart, h0, pow_zero, one_pow, pow_one]

theorem sqWeight_irreducible {K : Type} [Field K] [Fintype K] (P : K[X]) (hP : Irreducible P)
    (hm : P.Monic) : sqWeight P = ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹ := by
  unfold sqWeight
  classical
  have h1 := UniqueFactorizationMonoid.normalizedFactors_irreducible hP
  rw [hm.normalize_eq_self] at h1
  have h2 : (Multiset.map (fun P : K[X] => ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹)
      (UniqueFactorizationMonoid.normalizedFactors P)).prod =
      ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹ := by
    rw [h1]; simp
  convert h2

section sets

variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]

open Classical in

noncomputable def e3A (δ l : ℕ) : Finset (Fin δ → K) :=
  (Finset.univ : Finset (Fin δ → K)).filter (fun c => Irreducible (monicOf c) ∧
      ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L))

open Classical in

noncomputable def e3I (δ : ℕ) : Finset (Fin δ → K) :=
  (Finset.univ : Finset (Fin δ → K)).filter
      (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)

open Classical in

noncomputable def e3C (δ l : ℕ) (P' : K[X]) : Finset (Fin δ → K) :=
  (Finset.univ : Finset (Fin δ → K)).filter (fun c => Irreducible (monicOf c) ∧
      (monicOf c).coeff 0 ≠ 0 ∧ ∃ x ∈ (monicOf c).rootSet L, ∃ y ∈ P'.rootSet L,
        primeToPart l x = primeToPart l y)

def e3D (N : ℕ) (h : K[X]) : Set (Fin N → K) := {c | c ∈ sqSet K N ∧ h ∣ monicOf c}

noncomputable def e3μ (N : ℕ) : (Fin N → K) → ℝ := fun c => sqWeight (monicOf c)

def e3PA (g δ : ℕ) : Finset ℕ :=
  (g ^ δ - 1).primeFactors.filter (fun l => l ^ (4 * padicValNat l (g ^ δ - 1)) ≤ g ^ δ)

def e3PB (g δ δ' : ℕ) : Finset ℕ :=
  ((g ^ δ - 1).primeFactors ∪ (g ^ δ' - 1).primeFactors).filter
    (fun l => l ^ (4 * padicValNat l (g ^ δ - 1)) ≤ g ^ δ)

def e3SA (N : ℕ) : Set (Fin N → K) :=
  ⋃ δ ∈ Finset.Icc 2 N, ⋃ l ∈ e3PA (Fintype.card K) δ, ⋃ c' ∈ e3A K L δ l, e3D K N (monicOf c')

def e3SB (N : ℕ) : Set (Fin N → K) :=
  ⋃ δ ∈ Finset.Icc 1 N, ⋃ δ' ∈ Finset.Icc 1 δ, ⋃ l ∈ e3PB (Fintype.card K) δ δ',
    ⋃ c'' ∈ e3I K δ', ⋃ c' ∈ e3C K L δ l (monicOf c''), e3D K N (monicOf c' * monicOf c'')

variable {K} in
theorem mem_e3A {δ l : ℕ} {c : Fin δ → K} : c ∈ e3A K L δ l ↔ Irreducible (monicOf c) ∧
    ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L) := by
  simp only [e3A, Finset.mem_filter, Finset.mem_univ, true_and]

variable {K} in
theorem mem_e3I {δ : ℕ} {c : Fin δ → K} : c ∈ e3I K δ ↔ Irreducible (monicOf c) ∧
    (monicOf c).coeff 0 ≠ 0 := by
  simp only [e3I, Finset.mem_filter, Finset.mem_univ, true_and]

variable {K} in
theorem mem_e3C {δ l : ℕ} {P' : K[X]} {c : Fin δ → K} : c ∈ e3C K L δ l P' ↔
    Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 ∧ ∃ x ∈ (monicOf c).rootSet L,
      ∃ y ∈ P'.rootSet L, primeToPart l x = primeToPart l y := by
  simp only [e3C, Finset.mem_filter, Finset.mem_univ, true_and]

theorem e3μ_nonneg (N : ℕ) (c : Fin N → K) : 0 ≤ e3μ K N c := by
  unfold e3μ
  exact sqWeight_nonneg _

theorem wt_e3D_le (N : ℕ) (h : K[X]) (hm : h.Monic) :
    wtOf (e3μ K N) (e3D K N h) ≤ sqWeight h := by
  classical
  unfold e3D
  rw [wtOf_eq_filter']
  by_cases hd : h.natDegree ≤ N
  · exact divisor_square_weight_sum_le square_mass_le_one K N h hm hd _ (fun c hc => by
      simpa only [Finset.mem_filter] using hc)
  · rw [Finset.filter_eq_empty_iff.mpr, Finset.sum_empty]
    · exact sqWeight_nonneg h
    · intro c _ hdiv
      apply hd
      have := natDegree_le_of_dvd hdiv (monicOf_monic c).ne_zero
      rwa [monicOf_natDegree] at this

theorem card_pow_sub_one_pos (δ : ℕ) (hδ : 1 ≤ δ) : (0 : ℝ) < (Fintype.card K : ℝ) ^ δ - 1 := by
  have h1 : (1 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have h2 : (1 : ℝ) < (Fintype.card K : ℝ) ^ δ := one_lt_pow₀ h1 (by omega)
  linarith

theorem wt_caseA (N δ l : ℕ) (hl : l.Prime) (hδ : 2 ≤ δ)
    (hBB : l ^ (4 * padicValNat l (Fintype.card K ^ δ - 1)) ≤ Fintype.card K ^ δ) :
    wtOf (e3μ K N) (⋃ c' ∈ e3A K L δ l, e3D K N (monicOf c')) ≤
      (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
  have hpos := card_pow_sub_one_pos K δ (by omega)
  calc wtOf (e3μ K N) (⋃ c' ∈ e3A K L δ l, e3D K N (monicOf c'))
      ≤ ∑ c' ∈ e3A K L δ l, wtOf (e3μ K N) (e3D K N (monicOf c')) :=
        wtOf_biUnion_le _ (e3μ_nonneg K N) _ _
    _ ≤ ∑ _c' ∈ e3A K L δ l, ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
        refine Finset.sum_le_sum (fun c' hc' => ?_)
        have hirr : Irreducible (monicOf c') := ((mem_e3A L).mp hc').1
        refine (wt_e3D_le K N _ (monicOf_monic c')).trans_eq ?_
        rw [sqWeight_irreducible _ hirr (monicOf_monic c'), monicOf_natDegree]
    _ = ((e3A K L δ l).card : ℝ) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (same_factor_count K L δ l hl hδ hBB)
        (inv_nonneg.mpr hpos.le)

theorem wt_caseB (N δ δ' l : ℕ) (hl : l.Prime) (hδ : 1 ≤ δ) (hδ' : 1 ≤ δ')
    (hBB : l ^ (4 * padicValNat l (Fintype.card K ^ δ - 1)) ≤ Fintype.card K ^ δ) :
    wtOf (e3μ K N) (⋃ c'' ∈ e3I K δ', ⋃ c' ∈ e3C K L δ l (monicOf c''),
        e3D K N (monicOf c' * monicOf c'')) ≤
      (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
  have hpos := card_pow_sub_one_pos K δ hδ
  have hpos' := card_pow_sub_one_pos K δ' hδ'
  set G : ℝ := (Fintype.card K : ℝ) with hG
  have hG0 : 0 ≤ G := by positivity
  have hinner : ∀ c'' ∈ e3I K δ', wtOf (e3μ K N) (⋃ c' ∈ e3C K L δ l (monicOf c''),
      e3D K N (monicOf c' * monicOf c'')) ≤ G ^ ((δ : ℝ) / 4) * ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹) := by
    intro c'' hc''
    obtain ⟨hirr'', h0''⟩ := mem_e3I.mp hc''
    calc wtOf (e3μ K N) (⋃ c' ∈ e3C K L δ l (monicOf c''), e3D K N (monicOf c' * monicOf c''))
        ≤ ∑ c' ∈ e3C K L δ l (monicOf c''), wtOf (e3μ K N) (e3D K N (monicOf c' * monicOf c'')) :=
          wtOf_biUnion_le _ (e3μ_nonneg K N) _ _
      _ ≤ ∑ _c' ∈ e3C K L δ l (monicOf c''), ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹) := by
          refine Finset.sum_le_sum (fun c' hc' => ?_)
          have hirr : Irreducible (monicOf c') := ((mem_e3C L).mp hc').1
          refine (wt_e3D_le K N _ ((monicOf_monic c').mul (monicOf_monic c''))).trans_eq ?_
          rw [sqWeight_mul _ _ (monicOf_monic c').ne_zero (monicOf_monic c'').ne_zero,
            sqWeight_irreducible _ hirr (monicOf_monic c'),
            sqWeight_irreducible _ hirr'' (monicOf_monic c''), monicOf_natDegree,
            monicOf_natDegree]
      _ = ((e3C K L δ l (monicOf c'')).card : ℝ) * ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (cross_factor_count K L δ l (monicOf c'') hl hδ hirr'' h0'' hBB)
          (mul_nonneg (inv_nonneg.mpr hpos.le) (inv_nonneg.mpr hpos'.le))
  have hI : ((e3I K δ').card : ℝ) ≤ G ^ δ' - 1 := by
    have h1 := irreducible_count_upper_unit K δ' hδ'
    have h2 : (e3I K δ').card ≤ Fintype.card K ^ δ' - 1 := by
      refine le_trans ?_ h1
      exact Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 1 ≤ Fintype.card K ^ δ' := Nat.one_le_pow _ _ Fintype.card_pos
    have h4 : ((e3I K δ').card : ℝ) ≤ ((Fintype.card K ^ δ' - 1 : ℕ) : ℝ) := by exact_mod_cast h2
    rw [Nat.cast_sub h3] at h4
    push_cast at h4
    exact h4
  have hr0 : 0 ≤ G ^ ((δ : ℝ) / 4) := Real.rpow_nonneg hG0 _
  calc wtOf (e3μ K N) (⋃ c'' ∈ e3I K δ', ⋃ c' ∈ e3C K L δ l (monicOf c''),
        e3D K N (monicOf c' * monicOf c''))
      ≤ ∑ c'' ∈ e3I K δ', wtOf (e3μ K N) (⋃ c' ∈ e3C K L δ l (monicOf c''),
        e3D K N (monicOf c' * monicOf c'')) := wtOf_biUnion_le _ (e3μ_nonneg K N) _ _
    _ ≤ ∑ _c'' ∈ e3I K δ', G ^ ((δ : ℝ) / 4) * ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹) :=
        Finset.sum_le_sum hinner
    _ = ((e3I K δ').card : ℝ) * (G ^ ((δ : ℝ) / 4) * ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (G ^ δ' - 1) * (G ^ ((δ : ℝ) / 4) * ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹)) :=
        mul_le_mul_of_nonneg_right hI (mul_nonneg hr0
          (mul_nonneg (inv_nonneg.mpr hpos.le) (inv_nonneg.mpr hpos'.le)))
    _ = G ^ ((δ : ℝ) / 4) * (G ^ δ - 1)⁻¹ := by
        field_simp

variable {K L}

private theorem monicOf_coeff_eq_of_monic {F : Type} [Field F] (P : F[X]) (hP : P.Monic) :
    monicOf (fun i : Fin P.natDegree => P.coeff (i : ℕ)) = P := by
  unfold monicOf
  rw [Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i) P.natDegree]
  exact hP.as_sum.symm

private theorem ne_zero_of_aeval_eq_zero_of_coeff_zero_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E] {f : F[X]}
    (h0 : f.coeff 0 ≠ 0) {x : E} (hx : aeval x f = 0) : x ≠ 0 := by
  rintro rfl
  apply h0
  rw [← coeff_zero_eq_aeval_zero'] at hx
  exact (algebraMap F E).injective (hx.trans (map_zero _).symm)

theorem exists_irr_factor {f : K[X]} (hf : f ≠ 0) (h0 : f.coeff 0 ≠ 0) {x : L}
    (hx : aeval x f = 0) :
    ∃ δ, 1 ≤ δ ∧ δ ≤ f.natDegree ∧ ∃ c' : Fin δ → K, Irreducible (monicOf c') ∧
      (monicOf c').coeff 0 ≠ 0 ∧ monicOf c' ∣ f ∧ aeval x (monicOf c') = 0 := by
  have hxne : x ≠ 0 := ne_zero_of_aeval_eq_zero_of_coeff_zero_ne_zero h0 hx
  have hint : IsIntegral K x := IsAlgebraic.isIntegral ⟨f, hf, hx⟩
  have hPm : (minpoly K x).Monic := minpoly.monic hint
  have hPd : minpoly K x ∣ f := minpoly.dvd K x hx
  refine ⟨(minpoly K x).natDegree, minpoly.natDegree_pos hint, natDegree_le_of_dvd hPd hf,
    fun i => (minpoly K x).coeff (i : ℕ), ?_⟩
  rw [monicOf_coeff_eq_of_monic _ hPm]
  exact ⟨minpoly.irreducible hint, minpoly.coeff_zero_ne_zero hint hxne, hPd, minpoly.aeval K x⟩

private theorem pow_card_pow_eq_self_of_aeval_monicOf_irreducible {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E]
    {δ : ℕ} {c : Fin δ → F} (hi : Irreducible (monicOf c)) {x : E}
    (hx : aeval x (monicOf c) = 0) : x ^ (Fintype.card F ^ δ) = x := by
  have hint : IsIntegral F x := ⟨monicOf c, monicOf_monic c, by rwa [← aeval_def]⟩
  have hmin : minpoly F x = monicOf c :=
    (minpoly.eq_of_irreducible_of_monic hi hx (monicOf_monic c)).symm
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({x} : Set E)) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hfr : Module.finrank F (IntermediateField.adjoin F ({x} : Set E)) = δ := by
    rw [IntermediateField.adjoin.finrank hint, hmin, monicOf_natDegree]
  haveI : Finite (IntermediateField.adjoin F ({x} : Set E)) := Module.finite_of_finite F
  letI : Fintype (IntermediateField.adjoin F ({x} : Set E)) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin F ({x} : Set E)) = Fintype.card F ^ δ := by
    rw [Module.card_eq_pow_finrank (K := F), hfr]
  have key := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : IntermediateField.adjoin F ({x} : Set E))
  rw [hcard] at key
  simpa using congrArg (fun y : IntermediateField.adjoin F ({x} : Set E) => (y : E)) key

private theorem pow_card_pow_sub_one_eq_one_of_aeval_monicOf {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E]
    {δ : ℕ} {c : Fin δ → F} (hi : Irreducible (monicOf c)) (h0 : (monicOf c).coeff 0 ≠ 0)
    {x : E} (hx : aeval x (monicOf c) = 0) : x ^ (Fintype.card F ^ δ - 1) = 1 := by
  have hx0 : x ≠ 0 := ne_zero_of_aeval_eq_zero_of_coeff_zero_ne_zero h0 hx
  have hq : 1 ≤ Fintype.card F ^ δ := Nat.one_le_pow _ _ Fintype.card_pos
  have h := pow_card_pow_eq_self_of_aeval_monicOf_irreducible hi hx
  rw [← Nat.sub_add_cancel hq, pow_succ] at h
  exact mul_right_cancel₀ hx0 (h.trans (one_mul x).symm)

theorem mem_e3SB {N : ℕ} {c : Fin N → K} (hc : c ∈ sqSet K N) {l : ℕ} (hl : l.Prime)
    (hcond : ∀ d ∈ Finset.Icc 1 N,
      l ^ (4 * padicValNat l (Fintype.card K ^ d - 1)) ≤ Fintype.card K ^ d)
    {δ δ' : ℕ} (hδ' : 1 ≤ δ') (hδδ' : δ' ≤ δ) (hδN : δ ≤ N) {c' : Fin δ → K} {c'' : Fin δ' → K}
    (hi' : Irreducible (monicOf c')) (hi'' : Irreducible (monicOf c''))
    (h0' : (monicOf c').coeff 0 ≠ 0) (h0'' : (monicOf c'').coeff 0 ≠ 0)
    (hd' : monicOf c' ∣ monicOf c) (hd'' : monicOf c'' ∣ monicOf c) {x y : L}
    (hx : aeval x (monicOf c') = 0) (hy : aeval y (monicOf c'') = 0)
    (hxy : primeToPart l x = primeToPart l y) (hne : x ≠ y)
    (hPne : monicOf c' ≠ monicOf c'') : c ∈ e3SB K L N := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hδ1 : 1 ≤ δ := hδ'.trans hδδ'
  have hn : ∀ d, 1 ≤ d → Fintype.card K ^ d - 1 ≠ 0 := fun d hd => by
    have : Fintype.card K ^ 1 ≤ Fintype.card K ^ d := Nat.pow_le_pow_right (by omega) hd
    rw [pow_one] at this
    omega
  have hxp := pow_card_pow_sub_one_eq_one_of_aeval_monicOf hi' h0' hx
  have hyp := pow_card_pow_sub_one_eq_one_of_aeval_monicOf hi'' h0'' hy
  have hldiv : l ∣ Fintype.card K ^ δ - 1 ∨ l ∣ Fintype.card K ^ δ' - 1 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    calc x = primeToPart l x := (primeToPart_eq_self_of_not_dvd hl (hn δ hδ1) hxp hcon.1).symm
      _ = primeToPart l y := hxy
      _ = y := primeToPart_eq_self_of_not_dvd hl (hn δ' hδ') hyp hcon.2
  have hcop : IsCoprime (monicOf c') (monicOf c'') := by
    rw [hi'.coprime_iff_not_dvd]
    intro hdvd
    exact hPne (eq_of_monic_of_associated (monicOf_monic _) (monicOf_monic _)
      (hi'.associated_of_dvd hi'' hdvd))
  simp only [e3SB, Set.mem_iUnion]
  refine ⟨δ, Finset.mem_Icc.2 ⟨hδ1, hδN⟩, δ', Finset.mem_Icc.2 ⟨hδ', hδδ'⟩, l, ?_, c'',
    mem_e3I.2 ⟨hi'', h0''⟩, c', (mem_e3C L).2 ⟨hi', h0', x,
      mem_rootSet.2 ⟨(monicOf_monic _).ne_zero, hx⟩, y,
      mem_rootSet.2 ⟨(monicOf_monic _).ne_zero, hy⟩, hxy⟩, hc, hcop.mul_dvd hd' hd''⟩
  rw [e3PB, Finset.mem_filter, Finset.mem_union, Nat.mem_primeFactors, Nat.mem_primeFactors]
  refine ⟨?_, hcond δ (Finset.mem_Icc.2 ⟨hδ1, hδN⟩)⟩
  rcases hldiv with h | h
  · exact Or.inl ⟨hl, h, hn δ hδ1⟩
  · exact Or.inr ⟨hl, h, hn δ' hδ'⟩

theorem square_set_mem_exceptional_union {N : ℕ} {c : Fin N → K} (hc : c ∈ sqSet K N) {l : ℕ} (hl : l.Prime)
    (hlBB : l ∉ BB (Fintype.card K) N)
    (hninj : ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)) :
    c ∈ e3SA K L N ∪ e3SB K L N := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hcs : Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 := by
    simpa [sqSet] using hc
  have hf0 : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
  have hcond : ∀ d ∈ Finset.Icc 1 N,
      l ^ (4 * padicValNat l (Fintype.card K ^ d - 1)) ≤ Fintype.card K ^ d := by
    intro d hd
    have hd' := Finset.mem_Icc.1 hd
    by_contra hlt
    push_neg at hlt
    have hqd : 1 ≤ Fintype.card K ^ d := Nat.one_le_pow _ _ (by omega)
    have hv : padicValNat l (Fintype.card K ^ d - 1) ≠ 0 := by
      intro hv
      rw [hv, mul_zero, pow_zero] at hlt
      omega
    have hpos : Fintype.card K ^ d - 1 ≠ 0 := by
      intro h
      rw [h, padicValNat.zero] at hv
      exact hv rfl
    have hldvd : l ∣ Fintype.card K ^ d - 1 := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.2 hv)
    have hle : l ≤ Fintype.card K ^ d - 1 := Nat.le_of_dvd (by omega) hldvd
    have hdN : Fintype.card K ^ d ≤ Fintype.card K ^ N := Nat.pow_le_pow_right (by omega) hd'.2
    apply hlBB
    apply Finset.mem_insert_of_mem
    have hmem : l ∈ (Finset.range (Fintype.card K ^ N + 1)).filter (fun l => l.Prime ∧
        ∃ d ∈ Finset.Icc 1 N, Fintype.card K ^ d < l ^ (4 * padicValNat l (Fintype.card K ^ d - 1))) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hl, d, hd, hlt⟩
    convert hmem
  simp only [Set.InjOn] at hninj
  push_neg at hninj
  obtain ⟨x, hxr, y, hyr, hxy, hne⟩ := hninj
  have hxa : aeval x (monicOf c) = 0 := (mem_rootSet.1 hxr).2
  have hya : aeval y (monicOf c) = 0 := (mem_rootSet.1 hyr).2
  obtain ⟨δ1, h1δ1, hδ1N, c1, hi1, h01, hd1, hx1⟩ := exists_irr_factor hf0 hcs.2 hxa
  obtain ⟨δ2, h1δ2, hδ2N, c2, hi2, h02, hd2, hy2⟩ := exists_irr_factor hf0 hcs.2 hya
  rw [monicOf_natDegree] at hδ1N hδ2N
  by_cases heq : monicOf c1 = monicOf c2
  · left
    have hy1 : aeval y (monicOf c1) = 0 := by rw [heq]; exact hy2
    have hn : Fintype.card K ^ δ1 - 1 ≠ 0 := by
      have : Fintype.card K ^ 1 ≤ Fintype.card K ^ δ1 := Nat.pow_le_pow_right (by omega) h1δ1
      rw [pow_one] at this
      omega
    have hldvd : l ∣ Fintype.card K ^ δ1 - 1 := by
      by_contra hcon
      apply hne
      calc x = primeToPart l x :=
            (primeToPart_eq_self_of_not_dvd hl hn (pow_card_pow_sub_one_eq_one_of_aeval_monicOf hi1 h01 hx1) hcon).symm
        _ = primeToPart l y := hxy
        _ = y := primeToPart_eq_self_of_not_dvd hl hn (pow_card_pow_sub_one_eq_one_of_aeval_monicOf hi1 h01 hy1) hcon
    have h2δ1 : 2 ≤ δ1 := by
      by_contra hlt
      obtain rfl : δ1 = 1 := by omega
      apply hne
      simp [monicOf] at hx1 hy1
      linear_combination hx1 - hy1
    simp only [e3SA, Set.mem_iUnion]
    refine ⟨δ1, Finset.mem_Icc.2 ⟨h2δ1, hδ1N⟩, l, ?_, c1, (mem_e3A L).2 ⟨hi1, ?_⟩, hc, hd1⟩
    · rw [e3PA, Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hl, hldvd, hn⟩, hcond δ1 (Finset.mem_Icc.2 ⟨h1δ1, hδ1N⟩)⟩
    · intro hinj
      exact hne (hinj (mem_rootSet.2 ⟨(monicOf_monic _).ne_zero, hx1⟩)
        (mem_rootSet.2 ⟨(monicOf_monic _).ne_zero, hy1⟩) hxy)
  · right
    rcases le_total δ2 δ1 with h21 | h12
    · exact mem_e3SB hc hl hcond h1δ2 h21 hδ1N hi1 hi2 h01 h02 hd1 hd2 hx1 hy2 hxy hne heq
    · exact mem_e3SB hc hl hcond h1δ1 h12 hδ2N hi2 hi1 h02 h01 hd2 hd1 hy2 hx1 hxy.symm
        (Ne.symm hne) (Ne.symm heq)

end sets

theorem cube_div_fourth_sub_one_le (s : ℝ) (hs : 2 ≤ s) : s ^ 3 * (s ^ 4 - 1)⁻¹ ≤ 2 * (1 / s) := by
  have hs0 : 0 < s := by linarith
  have h2 : 4 ≤ s ^ 2 := by nlinarith
  have h44 : s ^ 4 = s ^ 2 * s ^ 2 := by ring
  have h16 : 16 ≤ s ^ 4 := by nlinarith
  have h4 : 0 < s ^ 4 - 1 := by linarith
  rw [← div_eq_mul_inv, div_le_iff₀ h4,
    show 2 * (1 / s) * (s ^ 4 - 1) = 2 * (s ^ 4 - 1) / s by ring, le_div_iff₀ hs0]
  have : s ^ 3 * s = s ^ 4 := by ring
  linarith

theorem div_fourth_sub_one_le (s : ℝ) (hs : 2 ≤ s) : s * (s ^ 4 - 1)⁻¹ ≤ 2 * (1 / s ^ 3) := by
  have hs0 : 0 < s := by linarith
  have h2 : 4 ≤ s ^ 2 := by nlinarith
  have h44 : s ^ 4 = s ^ 2 * s ^ 2 := by ring
  have h16 : 16 ≤ s ^ 4 := by nlinarith
  have h4 : 0 < s ^ 4 - 1 := by linarith
  rw [← div_eq_mul_inv, div_le_iff₀ h4,
    show 2 * (1 / s ^ 3) * (s ^ 4 - 1) = 2 * (s ^ 4 - 1) / s ^ 3 by ring,
    le_div_iff₀ (by positivity)]
  have : s * s ^ 3 = s ^ 4 := by ring
  linarith

private theorem two_pow_card_primeFactors_le_add_one (n : ℕ) : 2 ^ n.primeFactors.card ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · calc 2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ n.primeFactors, p :=
          Finset.prod_le_prod (fun _ _ => by positivity)
            (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
      _ ≤ n + 1 := Nat.le_succ n

private theorem sum_le_wtOf_of_subset {α : Type} [Fintype α] (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (T : Finset α) (S : Set α) (hT : ∀ x ∈ T, x ∈ S) : ∑ x ∈ T, μ x ≤ wtOf μ S := by
  unfold wtOf
  rw [← Finset.sum_indicator_subset μ (Finset.subset_univ T)]
  exact Finset.sum_le_sum fun x _ =>
    Set.indicator_le_indicator_of_subset (fun y hy => hT y hy) hμ x

private theorem sum_Icc_two_mul_pow_le_sixteen_thirds_mul_sq (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 8) (N : ℕ) :
    ∑ δ ∈ Finset.Icc 2 N, (δ : ℝ) * x ^ δ ≤ 16 / 3 * x ^ 2 := by
  have h2x0 : 0 ≤ 2 * x := by linarith
  have h2x1 : 2 * x < 1 := by linarith
  calc ∑ δ ∈ Finset.Icc 2 N, (δ : ℝ) * x ^ δ ≤ ∑ δ ∈ Finset.Ico 2 (N + 1), (2 * x) ^ δ := by
        rw [show Finset.Icc 2 N = Finset.Ico 2 (N + 1) by
          ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
        apply Finset.sum_le_sum
        intro δ _
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx0 _)
        exact_mod_cast (Nat.lt_two_pow_self).le
    _ ≤ (2 * x) ^ 2 / (1 - 2 * x) := geom_sum_Ico_le_of_lt_one h2x0 h2x1
    _ ≤ 16 / 3 * x ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 / 8 - x)]

private theorem sum_Icc_one_sq_mul_pow_le_five_mul (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 512) (N : ℕ) :
    ∑ δ ∈ Finset.Icc 1 N, (δ : ℝ) ^ 2 * y ^ δ ≤ 5 * y := by
  have h4y0 : 0 ≤ 4 * y := by linarith
  have h4y1 : 4 * y < 1 := by linarith
  calc ∑ δ ∈ Finset.Icc 1 N, (δ : ℝ) ^ 2 * y ^ δ ≤ ∑ δ ∈ Finset.Ico 1 (N + 1), (4 * y) ^ δ := by
        rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by
          ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
        apply Finset.sum_le_sum
        intro δ _
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hy0 _)
        have h : δ ≤ 2 ^ δ := (Nat.lt_two_pow_self).le
        have h' : δ ^ 2 ≤ 4 ^ δ := by
          calc δ ^ 2 ≤ (2 ^ δ) ^ 2 := Nat.pow_le_pow_left h 2
            _ = 4 ^ δ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        exact_mod_cast h'
    _ ≤ (4 * y) ^ 1 / (1 - 4 * y) := geom_sum_Ico_le_of_lt_one h4y0 h4y1
    _ ≤ 5 * y := by
        rw [pow_one, div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg hy0 (by linarith : (0 : ℝ) ≤ 1 - 20 * y)]

theorem local_estimate_second : LocalEstimateII := by
  unfold LocalEstimateII
  intro K L _ _ _ _ _ N hq
  classical
  have hq' : 4096 ≤ Fintype.card K := by norm_num at hq; exact hq
  have hQ : (4096 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast hq'
  have hQ0 : (0 : ℝ) ≤ (Fintype.card K : ℝ) := by linarith
  have hLQ : 0 ≤ Real.log (Fintype.card K : ℝ) := Real.log_nonneg (by linarith)
  have hμ : ∀ c, 0 ≤ e3μ K N c := e3μ_nonneg K N
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (Fintype.card K : ℝ) ^ (4 : ℝ)⁻¹ := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hs4 : s ^ 4 = (Fintype.card K : ℝ) := by
    rw [hsdef, show (4 : ℝ)⁻¹ = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hQ0 (by norm_num)
  have hs8 : 8 ≤ s := by
    by_contra h
    push_neg at h
    have h2 : s ^ 2 < 64 := by nlinarith
    have h4 : s ^ 4 < 4096 := by
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 64 - s ^ 2) (by positivity : (0 : ℝ) < 64 + s ^ 2)]
    linarith
  have hsδ : ∀ δ : ℕ, 1 ≤ δ → 2 ≤ s ^ δ := fun δ hδ => by
    calc (2 : ℝ) ≤ s ^ 1 := by rw [pow_one]; linarith
      _ ≤ s ^ δ := pow_le_pow_right₀ (by linarith) hδ
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = s⁻¹ := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; exact inv_nonneg.2 hs0
  have hxs : x * s = 1 := by rw [hxdef, inv_mul_cancel₀ (ne_of_gt (by linarith))]
  have hx8 : x ≤ 1 / 8 := by nlinarith [mul_le_mul_of_nonneg_left hs8 hx0]
  have hx512 : x ^ 3 ≤ 1 / 512 := by
    calc x ^ 3 ≤ (1 / 8) ^ 3 := pow_le_pow_left₀ hx0 hx8 3
      _ = 1 / 512 := by norm_num
  have hpowA : ∀ δ : ℕ, (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) = (s ^ δ) ^ 3 := fun δ => by
    rw [show 3 * (δ : ℝ) / 4 = (4 : ℝ)⁻¹ * ((3 * δ : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul hQ0, ← hsdef, Real.rpow_natCast]
    ring
  have hpowB : ∀ δ : ℕ, (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) = s ^ δ := fun δ => by
    rw [show (δ : ℝ) / 4 = (4 : ℝ)⁻¹ * ((δ : ℕ) : ℝ) by ring,
      Real.rpow_mul hQ0, ← hsdef, Real.rpow_natCast]
  have hpowQ : ∀ δ : ℕ, (Fintype.card K : ℝ) ^ δ = (s ^ δ) ^ 4 := fun δ => by
    rw [← hs4]; ring
  have hQδ : ∀ δ : ℕ, (1 : ℝ) ≤ (Fintype.card K : ℝ) ^ δ := fun δ => one_le_pow₀ (by linarith)
  have htA : ∀ δ : ℕ, 2 ≤ δ →
      (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ ≤ 2 * x ^ δ := fun δ hδ => by
    rw [hpowA δ, hpowQ δ]
    calc (s ^ δ) ^ 3 * ((s ^ δ) ^ 4 - 1)⁻¹ ≤ 2 * (1 / s ^ δ) := cube_div_fourth_sub_one_le (s ^ δ) (hsδ δ (by omega))
      _ = 2 * x ^ δ := by rw [hxdef]; ring
  have htB : ∀ δ : ℕ, 1 ≤ δ →
      (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ ≤ 2 * (x ^ 3) ^ δ := fun δ hδ => by
    rw [hpowB δ, hpowQ δ]
    calc s ^ δ * ((s ^ δ) ^ 4 - 1)⁻¹ ≤ 2 * (1 / (s ^ δ) ^ 3) := div_fourth_sub_one_le (s ^ δ) (hsδ δ hδ)
      _ = 2 * (x ^ 3) ^ δ := by rw [hxdef]; ring
  have hfA0 : ∀ δ : ℕ, 0 ≤ (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := fun δ =>
    mul_nonneg (by positivity) (inv_nonneg.2 (by linarith [hQδ δ]))
  have hfB0 : ∀ δ : ℕ, 0 ≤ (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := fun δ =>
    mul_nonneg (by positivity) (inv_nonneg.2 (by linarith [hQδ δ]))
  have hω : ∀ d : ℕ, ((Fintype.card K ^ d - 1).primeFactors.card : ℝ) ≤ 3 / 2 * d * Real.log (Fintype.card K : ℝ) := by
    intro d
    have hpos : 1 ≤ Fintype.card K ^ d := Nat.one_le_pow _ _ Fintype.card_pos
    have h1 : 2 ^ (Fintype.card K ^ d - 1).primeFactors.card ≤ Fintype.card K ^ d :=
      (two_pow_card_primeFactors_le_add_one _).trans (Nat.sub_add_cancel hpos).le
    have h2 : (2 : ℝ) ^ (Fintype.card K ^ d - 1).primeFactors.card ≤ (Fintype.card K : ℝ) ^ d := by
      exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow, Real.log_pow] at h3
    have hl2 := Real.log_two_gt_d9
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card K ^ d - 1).primeFactors.card)
      (by linarith : (0 : ℝ) ≤ Real.log 2 - 2 / 3)]
  refine le_trans (sum_le_wtOf_of_subset (e3μ K N) hμ _ (e3SA K L N ∪ e3SB K L N) ?_) ?_
  · intro c hc
    obtain ⟨hc1, l, hl, hlBB, hninj⟩ := Finset.mem_filter.1 hc
    exact square_set_mem_exceptional_union hc1 hl hlBB hninj
  refine (wtOf_union_le _ hμ _ _).trans ?_
  have hA : wtOf (e3μ K N) (e3SA K L N) ≤ 3 * Real.log (Fintype.card K : ℝ) * (16 / 3 * x ^ 2) := by
    unfold e3SA
    refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc _ ≤ ∑ δ ∈ Finset.Icc 2 N, 3 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) * x ^ δ) := by
          apply Finset.sum_le_sum
          intro δ hδ
          have hδ2 := (Finset.mem_Icc.1 hδ).1
          refine (wtOf_biUnion_le _ hμ _ _).trans ?_
          calc _ ≤ ∑ l ∈ e3PA (Fintype.card K) δ,
                (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
                apply Finset.sum_le_sum
                intro l hl
                rw [e3PA, Finset.mem_filter, Nat.mem_primeFactors] at hl
                exact wt_caseA K L N δ l hl.1.1 hδ2 hl.2
            _ = ((e3PA (Fintype.card K) δ).card : ℝ) *
                ((Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (3 / 2 * δ * Real.log (Fintype.card K : ℝ)) * (2 * x ^ δ) := by
                apply mul_le_mul _ (htA δ hδ2) (hfA0 δ) (mul_nonneg (by positivity) hLQ)
                calc ((e3PA (Fintype.card K) δ).card : ℝ)
                    ≤ ((Fintype.card K ^ δ - 1).primeFactors.card : ℝ) := by
                      exact_mod_cast Finset.card_filter_le _ _
                  _ ≤ 3 / 2 * δ * Real.log (Fintype.card K : ℝ) := hω δ
            _ = 3 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) * x ^ δ) := by ring
      _ = 3 * Real.log (Fintype.card K : ℝ) * ∑ δ ∈ Finset.Icc 2 N, (δ : ℝ) * x ^ δ := by rw [Finset.mul_sum]
      _ ≤ 3 * Real.log (Fintype.card K : ℝ) * (16 / 3 * x ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_Icc_two_mul_pow_le_sixteen_thirds_mul_sq x hx0 hx8 N) (mul_nonneg (by norm_num) hLQ)
  have hB : wtOf (e3μ K N) (e3SB K L N) ≤ 6 * Real.log (Fintype.card K : ℝ) * (5 * x ^ 3) := by
    unfold e3SB
    refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc _ ≤ ∑ δ ∈ Finset.Icc 1 N, 6 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) ^ 2 * (x ^ 3) ^ δ) := by
          apply Finset.sum_le_sum
          intro δ hδ
          have hδ1 := (Finset.mem_Icc.1 hδ).1
          refine (wtOf_biUnion_le _ hμ _ _).trans ?_
          calc _ ≤ ∑ δ' ∈ Finset.Icc 1 δ, 6 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) * (x ^ 3) ^ δ) := by
                apply Finset.sum_le_sum
                intro δ' hδ'
                have hδ'1 := (Finset.mem_Icc.1 hδ').1
                have hδ'δ := (Finset.mem_Icc.1 hδ').2
                refine (wtOf_biUnion_le _ hμ _ _).trans ?_
                calc _ ≤ ∑ l ∈ e3PB (Fintype.card K) δ δ',
                      (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
                      apply Finset.sum_le_sum
                      intro l hl
                      rw [e3PB, Finset.mem_filter, Finset.mem_union, Nat.mem_primeFactors,
                        Nat.mem_primeFactors] at hl
                      have hlp : l.Prime := by
                        rcases hl.1 with h | h
                        · exact h.1
                        · exact h.1
                      exact wt_caseB K L N δ δ' l hlp hδ1 hδ'1 hl.2
                  _ = ((e3PB (Fintype.card K) δ δ').card : ℝ) *
                      ((Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹) := by
                      rw [Finset.sum_const, nsmul_eq_mul]
                  _ ≤ (3 * δ * Real.log (Fintype.card K : ℝ)) * (2 * (x ^ 3) ^ δ) := by
                      apply mul_le_mul _ (htB δ hδ1) (hfB0 δ) (mul_nonneg (by positivity) hLQ)
                      calc ((e3PB (Fintype.card K) δ δ').card : ℝ)
                          ≤ ((Fintype.card K ^ δ - 1).primeFactors.card : ℝ) +
                            ((Fintype.card K ^ δ' - 1).primeFactors.card : ℝ) := by
                            exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_union_le _ _)
                        _ ≤ 3 / 2 * δ * Real.log (Fintype.card K : ℝ) + 3 / 2 * δ' * Real.log (Fintype.card K : ℝ) := add_le_add (hω δ) (hω δ')
                        _ ≤ 3 * δ * Real.log (Fintype.card K : ℝ) := by
                            have : (δ' : ℝ) ≤ δ := by exact_mod_cast hδ'δ
                            nlinarith [mul_nonneg (sub_nonneg.2 this) hLQ]
                  _ = 6 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) * (x ^ 3) ^ δ) := by ring
            _ = 6 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) ^ 2 * (x ^ 3) ^ δ) := by
                rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
                ring
      _ = 6 * Real.log (Fintype.card K : ℝ) * ∑ δ ∈ Finset.Icc 1 N, (δ : ℝ) ^ 2 * (x ^ 3) ^ δ := by rw [Finset.mul_sum]
      _ ≤ 6 * Real.log (Fintype.card K : ℝ) * (5 * x ^ 3) :=
          mul_le_mul_of_nonneg_left (sum_Icc_one_sq_mul_pow_le_five_mul (x ^ 3) (by positivity) hx512 N)
            (mul_nonneg (by norm_num) hLQ)
  have hsq : Real.sqrt (Fintype.card K : ℝ) = s ^ 2 := by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hx2 : x ^ 2 = 1 / s ^ 2 := by rw [hxdef, inv_pow, one_div]
  have hx3 : x ^ 3 ≤ x ^ 2 / 8 := by nlinarith [mul_le_mul_of_nonneg_left hx8 (sq_nonneg x)]
  rw [hsq]
  calc wtOf (e3μ K N) (e3SA K L N) + wtOf (e3μ K N) (e3SB K L N)
      ≤ 3 * Real.log (Fintype.card K : ℝ) * (16 / 3 * x ^ 2) + 6 * Real.log (Fintype.card K : ℝ) * (5 * x ^ 3) := add_le_add hA hB
    _ ≤ 23 * Real.log (Fintype.card K : ℝ) * x ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hx3 hLQ, mul_nonneg hLQ (sq_nonneg x)]
    _ = 23 * Real.log (Fintype.card K : ℝ) / s ^ 2 := by rw [hx2]; ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
