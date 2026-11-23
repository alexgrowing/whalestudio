import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Forms

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem RowSub.isMultiHomog_mul {f g : MRingOver S ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

omit [Fintype K] in

theorem RowSub.isMultiHomog_C (r : S) : IsMultiHomog (C r : MRingOver S ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm

omit [Fintype K] in

theorem RowSub.isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver S ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X'] at hm
  split_ifs at hm with h
  · subst h
    by_cases hk : k' = k
    · subst hk
      simp [Finsupp.single_apply]
    · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => hk (congrArg Sigma.fst e).symm
      simp [hk]
  · exact absurd rfl hm

omit [Fintype K] in

theorem RowSub.isMultiHomog_pow {f : MRingOver S ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using RowSub.isMultiHomog_C (ι := ι) (1 : S)
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact RowSub.isMultiHomog_mul ih hf

omit [Fintype K] in

theorem RowSub.isMultiHomog_prod {β : Type} (s : Finset β) (f : β → MRingOver S ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RowSub.isMultiHomog_C (ι := ι) (1 : S)
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact RowSub.isMultiHomog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem RowSub.isMultiHomog_coordProd (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ d k) d := by
  classical
  have h := RowSub.isMultiHomog_prod (S := S) (ι := ι) Finset.univ (fun k => (X ⟨k, c k⟩ : MRingOver S ι) ^ d k)
    (fun k => d k • Pi.single k 1) fun k _ => RowSub.isMultiHomog_pow (RowSub.isMultiHomog_X k (c k)) _
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rwa [e] at h

variable {Ω : Type} [Field Ω] [Algebra S Ω]

theorem RowSub.exists_form_of_mem_chartRingOver (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {z : Ω} (hz : z ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.chartRingOver S y c) :
    ∃ (m : K → ℕ) (h : MRingOver S ι), IsMultiHomog h m ∧ z = aeval y h / ∏ k, y ⟨k, c k⟩ ^ m k := by
  classical
  have hP : ∀ m : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hPadd : ∀ m m' : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ (m + m') k) =
      (∏ k, y ⟨k, c k⟩ ^ m k) * ∏ k, y ⟨k, c k⟩ ^ m' k := fun m m' => by
    simp [pow_add, Finset.prod_mul_distrib]
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨Pi.single p.1 1, X p, RowSub.isMultiHomog_X p.1 p.2, ?_⟩
    rw [aeval_X]
    rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [hk]) (by simp)]
    simp
  | algebraMap r =>
    exact ⟨0, C r, RowSub.isMultiHomog_C r, by simp⟩
  | add x x' _ _ ih ih' =>
    obtain ⟨m, h, hh, rfl⟩ := ih
    obtain ⟨m', h', hh', rfl⟩ := ih'
    refine ⟨m + m', h * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ m' k + h' * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ m k,
      ?_, ?_⟩
    · have h1 := RowSub.isMultiHomog_mul hh (RowSub.isMultiHomog_coordProd (S := S) c m')
      have h2 := RowSub.isMultiHomog_mul hh' (RowSub.isMultiHomog_coordProd (S := S) c m)
      rw [add_comm m' m] at h2
      intro d hd k
      rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
      · exact h1 d hd k
      · exact h2 d hd k
    · rw [hPadd, div_add_div _ _ (hP m) (hP m')]
      simp only [map_add, map_mul, map_prod, map_pow, aeval_X]
      ring
  | mul x x' _ _ ih ih' =>
    obtain ⟨m, h, hh, rfl⟩ := ih
    obtain ⟨m', h', hh', rfl⟩ := ih'
    exact ⟨m + m', h * h', RowSub.isMultiHomog_mul hh hh', by rw [hPadd, map_mul, div_mul_div_comm]⟩

end Forms

theorem RowSub.proof : RowSub.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J I hne hI t ht
  obtain ⟨n, hn⟩ := ht
  choose c hc using hne
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hI k (c k) (hc k)
  set δ : K → ℤ := γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ with hδ
  have h1 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hn c) hyc
  rw [Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule] at h1
  obtain ⟨m, h, hh, heq⟩ := RowSub.exists_form_of_mem_chartRingOver y c hyc h1

  set p : K → ℕ := fun k => (-δ k).toNat with hp
  set q : K → ℕ := fun k => (δ k + p k).toNat with hq
  have hpk : ∀ k, -δ k ≤ (p k : ℤ) := fun k => Int.self_le_toNat _
  have hqk : ∀ k, (q k : ℤ) = δ k + p k := fun k => Int.toNat_of_nonneg (by have := hpk k; omega)

  set T : MRingOver S ι := (∏ j ∈ J.1, (X ⟨k₀, e.symm j⟩ : MRingOver S ι)) ^ n *
    ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ (m k + p k) with hT
  set G : MRingOver S ι := h * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ q k with hG
  set a : K → ℕ := n • (∑ j ∈ J.1, (Pi.single k₀ 1 : K → ℕ)) + (m + p) with ha
  have hTa : IsMultiHomog T a := by
    refine RowSub.isMultiHomog_mul (RowSub.isMultiHomog_pow (RowSub.isMultiHomog_prod _ _ _ fun j _ =>
      RowSub.isMultiHomog_X k₀ (e.symm j)) n) ?_
    exact RowSub.isMultiHomog_coordProd c (m + p)
  have hak : ∀ k, γ k + (a k : ℤ) = δ k + p k + m k := by
    intro k
    simp only [ha, hδ, Pi.add_apply, Pi.smul_apply, Finset.sum_const, smul_eq_mul,
      IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
    by_cases hk : k = k₀
    · subst hk; simp; ring
    · simp [hk]; ring
  have hGa : IsMultiHomog G (fun k => (γ k + a k).toNat) := by
    have e' : (fun k => (γ k + (a k : ℤ)).toNat) = m + q := by
      funext k
      rw [hak k, Pi.add_apply]
      have := hqk k
      have := hpk k
      omega
    rw [e']
    exact RowSub.isMultiHomog_mul hh (RowSub.isMultiHomog_coordProd c q)
  have hXmem : ∀ k (i : ι k), i ∈ baseCell k₀ e J.1 I k →
      (X ⟨k, i⟩ : MRingOver S ι) ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) :=
    fun k i hi => Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hTmem : T ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
    refine mul_mem (pow_mem (prod_mem fun j hj => hXmem k₀ (e.symm j) ?_) n)
      (prod_mem fun k _ => pow_mem (hXmem k (c k) ?_) _)
    · unfold baseCell
      rw [Function.update_self]
      exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hj)
    · unfold baseCell
      by_cases hk : k = k₀
      · subst hk; rw [Function.update_self]; exact Finset.mem_union_left _ (hc k)
      · rw [Function.update_of_ne hk]; exact hc k
  have hmeet : CellMeets y (baseCell k₀ e J.1 I) := by
    intro k i hi
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact hI k i hi
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact (Kleiman.mem_support _).mp (J.2.2 hj)
    · rw [Function.update_of_ne hk] at hi; exact hI k i hi

  have hx : Kleiman.xProd J ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => (Kleiman.mem_support _).mp (J.2.2 hj)
  have hPm : (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  have hPp : (∏ k, y ⟨k, c k⟩ ^ (m k + p k)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  have hTv : aeval y T = Kleiman.xProd J ^ n * ∏ k, y ⟨k, c k⟩ ^ (m k + p k) := by
    simp only [hT, map_mul, map_prod, map_pow, aeval_X]
    rfl
  have hGv : aeval y G = aeval y h * ∏ k, y ⟨k, c k⟩ ^ q k := by
    simp only [hG, map_mul, map_prod, map_pow, aeval_X]
  have hH : aeval y h = Kleiman.xProd J ^ n * t * (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * ∏ k, y ⟨k, c k⟩ ^ m k := by
    rw [eq_div_iff hPm] at heq
    exact heq.symm
  have e1 : (∏ k, y ⟨k, c k⟩ ^ (m k + p k)) = (∏ k, y ⟨k, c k⟩ ^ m k) * ∏ k, y ⟨k, c k⟩ ^ p k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => pow_add _ _ _
  have e2 : (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * ∏ k, y ⟨k, c k⟩ ^ q k = ∏ k, y ⟨k, c k⟩ ^ p k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), hqk k]
    congr 1
    ring
  have hval : t = aeval y G / aeval y T := by
    rw [hTv, hGv, eq_div_iff (mul_ne_zero (pow_ne_zero _ hx) hPp), hH, e1]
    linear_combination (-(Kleiman.xProd J ^ n * t * ∏ k, y ⟨k, c k⟩ ^ m k)) * e2
  show t ∈ cellSec S y γ (baseCell k₀ e J.1 I)
  unfold cellSec
  rw [if_pos hmeet]
  exact Submodule.subset_span ⟨G, T, a, hTmem, hTa, fun k => by rw [hak k]; have := hpk k; have := hqk k; omega,
    hGa, hval⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
