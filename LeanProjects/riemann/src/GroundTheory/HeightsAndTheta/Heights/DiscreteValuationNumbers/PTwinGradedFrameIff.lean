import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerBis
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueSat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)

universe u v w

namespace GradedFrameCharacterisation

section Triangular

variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem repr_sum_smul {τ : Type*} [Fintype τ] (w : Module.Basis (Fin N) Ω E) (a : τ → Ω) (bb : τ → E)
    (j : Fin N) :
    w.repr (∑ q, a q • bb q) j = ∑ q, a q * w.repr (bb q) j := by
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]

theorem coeff_eq_zero_of_tri (w : Module.Basis (Fin N) Ω E) (bb : Fin N → E)
    (hup : ∀ q j : Fin N, q < j → w.repr (bb q) j = 0) (hd : ∀ q, w.repr (bb q) q ≠ 0)
    (a : Fin N → Ω) (n : ℕ) (h : ∀ j : Fin N, n ≤ (j : ℕ) → w.repr (∑ q, a q • bb q) j = 0) :
    ∀ q : Fin N, n ≤ (q : ℕ) → a q = 0 := by
  classical
  by_contra hne
  push Not at hne
  set T := Finset.univ.filter (fun q : Fin N => n ≤ (q : ℕ) ∧ a q ≠ 0) with hT
  have hTne : T.Nonempty := by
    obtain ⟨q, hq, hq'⟩ := hne
    exact ⟨q, by simp [hT, hq, hq']⟩
  have hq0 : T.max' hTne ∈ T := T.max'_mem hTne
  have hq0' := hq0
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hq0'
  have hsum : w.repr (∑ q, a q • bb q) (T.max' hTne) =
      a (T.max' hTne) * w.repr (bb (T.max' hTne)) (T.max' hTne) := by
    rw [repr_sum_smul, Finset.sum_eq_single (T.max' hTne)]
    · intro q _ hq
      rcases lt_or_gt_of_ne hq with hlt | hgt
      · rw [hup q _ hlt, mul_zero]
      · have haq : a q = 0 := by
          by_contra haq
          have hmem : q ∈ T := by
            simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨le_trans hq0'.1 (le_of_lt (Fin.lt_def.mp hgt)), haq⟩
          exact absurd (T.le_max' q hmem) (not_le.mpr hgt)
        rw [haq, zero_mul]
    · simp
  have h0 := h _ hq0'.1
  rw [hsum] at h0
  exact mul_ne_zero hq0'.2 (hd _) h0

theorem repr_of_sub_mem (w : Module.Basis (Fin N) Ω E) {x : E} {i : Fin N} {t : Ω}
    (hx : x - t • w i ∈
      Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < ((Fin.castSucc i : Fin (N + 1)) : ℕ)})) :
    (∀ j, i < j → w.repr x j = 0) ∧ w.repr x i = t := by
  rw [Module.Basis.mem_span_image] at hx
  have key : ∀ j : Fin N, i ≤ j → w.repr x j - t * (Finsupp.single i (1 : Ω) j) = 0 := by
    intro j hj
    have hj' : j ∉ (w.repr (x - t • w i)).support := fun hm => by
      have hlt := hx (Finset.mem_coe.mpr hm)
      simp only [Set.mem_ofPred_eq, Fin.val_castSucc] at hlt
      exact absurd hj (not_le.mpr (Fin.lt_def.mpr hlt))
    rw [Finsupp.notMem_support_iff, map_sub, map_smul, Module.Basis.repr_self, Finsupp.sub_apply,
      Finsupp.smul_apply, smul_eq_mul] at hj'
    exact hj'
  refine ⟨fun j hj => ?_, ?_⟩
  · have h0 := key j hj.le
    rwa [Finsupp.single_eq_of_ne (ne_of_gt hj), mul_zero, sub_zero] at h0
  · have h0 := key i le_rfl
    rwa [Finsupp.single_eq_same, mul_one, sub_eq_zero] at h0

end Triangular

section Main

variable {o : Type u} [CommRing o] {Ω : Type v} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {N : ℕ} {E : Type w}
  [AddCommGroup E] [Module Ω E] {B : ChartBundle o (segreVec y) N E}
  {w : Module.Basis (Fin N) Ω E} {b : Fin N → K → ℤ}

omit [∀ k, Fintype (ι k)] in

theorem mon_ne_zero {c : ∀ k, ι k} (hc : segreVec y c ≠ 0) (a : K → ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c a ≠ 0 := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k =>
    (Finset.prod_ne_zero_iff.mp hc) k (Finset.mem_univ _)
  exact Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hy k)

omit [∀ k, Fintype (ι k)] in

theorem forward (h : IsFlagFrame y B w b) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsGradedFrame o y B
      (fun i => Submodule.span Ω (w '' {j | (j : ℕ) < i})) b w := by
  intro c hc
  have hm := mon_ne_zero (y := y) hc
  have hex : ∀ i, ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧
      w.repr v i = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i) := by
    intro i
    have hmem : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i) ∈ degLat o y (b i) c :=
      ⟨1, one_mem _, (one_mul _).symm⟩
    rw [← h.graded c hc i] at hmem
    exact hmem
  choose bb hbb hup hdiag using hex
  have hd : ∀ q, w.repr (bb q) q ≠ 0 := fun q => by rw [hdiag q]; exact hm _
  have hli : LinearIndependent Ω bb := Fintype.linearIndependent_iff.mpr fun g hg q =>
    coeff_eq_zero_of_tri w bb hup hd g 0 (fun j _ => by rw [hg]; simp) q (Nat.zero_le _)
  have : FiniteDimensional Ω E := Module.Finite.of_basis w
  have hsp : Submodule.span Ω (Set.range bb) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [Module.finrank_eq_card_basis w])

  have hgen : ∀ n : ℕ, ∀ e ∈ B.lat c, (∀ j : Fin N, n ≤ (j : ℕ) → w.repr e j = 0) →
      ∃ a : Fin N → Ω, (∀ q, a q ∈ chartRing o (segreVec y) c) ∧ e = ∑ q, a q • bb q := by
    intro n
    induction n with
    | zero =>
      intro e _ he
      refine ⟨0, fun _ => zero_mem _, ?_⟩
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
      exact w.repr.injective (Finsupp.ext fun j => by simpa using he j (Nat.zero_le _))
    | succ n ih =>
      intro e he hz
      by_cases hn : n < N
      · have hmem : w.repr e ⟨n, hn⟩ ∈ degLat o y (b ⟨n, hn⟩) c := by
          rw [← h.graded c hc ⟨n, hn⟩]
          exact ⟨e, he, fun j hj => hz j (by rw [Fin.lt_def] at hj; simp at hj; omega), rfl⟩
        obtain ⟨a, ha, hae⟩ := hmem
        obtain ⟨a', ha', he'⟩ := ih (e - a • bb ⟨n, hn⟩)
          (sub_mem he (B.stable c a ha _ (hbb _))) (fun j hj => by
            rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
            rcases Nat.lt_or_ge n (j : ℕ) with hlt | hge
            · rw [hz j hlt, hup _ j (Fin.lt_def.mpr hlt), mul_zero, sub_zero]
            · have hj : j = ⟨n, hn⟩ := Fin.ext (le_antisymm hge hj)
              subst hj
              rw [hdiag, hae]
              simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon])
        refine ⟨a' + Pi.single ⟨n, hn⟩ a, fun q => add_mem (ha' q) ?_, ?_⟩
        · by_cases hq : q = ⟨n, hn⟩
          · subst hq; simpa using ha
          · simp [hq]
        · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
          rw [← he', Finset.sum_eq_single (⟨n, hn⟩ : Fin N)]
          · simp
          · intro q _ hq; simp [hq]
          · simp
      · exact ih e he fun j hj => absurd j.isLt (by omega)
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
  refine ⟨bb, hli, hsp, fun e => ⟨fun ⟨n, hn⟩ => ?_, fun ⟨a, ha, hae⟩ => ⟨0, ?_⟩⟩, fun i => ⟨1, ?_, ?_⟩⟩
  · rw [one_pow, one_smul] at hn
    obtain ⟨a, ha, hae⟩ := hgen N e hn (fun j hj => absurd j.isLt (by omega))
    exact ⟨a, fun q => ⟨0, by rw [pow_zero, one_mul]; exact ha q⟩, hae⟩
  · rw [pow_zero, one_smul, hae]
    refine AddSubgroup.sum_mem _ fun q _ => B.stable c _ ?_ _ (hbb q)
    obtain ⟨n, hn⟩ := ha q
    rwa [one_pow, one_mul] at hn
  · exact ⟨one_ne_zero, ⟨0, by rw [pow_zero, one_mul]; exact one_mem _⟩,
      ⟨0, by rw [pow_zero, one_mul, inv_one]; exact one_mem _⟩⟩
  · rw [Module.Basis.mem_span_image]
    intro j hj
    simp only [Set.mem_ofPred_eq, Fin.val_castSucc]
    rw [Finset.mem_coe, Finsupp.mem_support_iff, map_sub, map_smul, Module.Basis.repr_self,
      Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, one_mul] at hj
    by_contra hji
    rcases (not_lt.mp hji).lt_or_eq with hlt | heq
    · apply hj
      rw [hup i j (Fin.lt_def.mpr hlt), Finsupp.single_eq_of_ne (ne_of_gt (Fin.lt_def.mpr hlt)),
        mul_zero, sub_zero]
    · have hji' : j = i := Fin.ext heq.symm
      subst hji'
      apply hj
      rw [hdiag, Finsupp.single_eq_same, mul_one, sub_self]

omit [∀ k, Fintype (ι k)] in

theorem backward (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsGradedFrame o y B
      (fun i => Submodule.span Ω (w '' {j | (j : ℕ) < i})) b w) :
    IsFlagFrame y B w b := by
  refine ⟨fun c hc i => ?_⟩
  have hm := mon_ne_zero (y := y) hc
  obtain ⟨k, f, cc, hf, hcc, h1, hfr⟩ := h c hc
  choose bb hli hsp hlat hunit using hfr
  choose u hu hbu using hunit
  have htri : ∀ l q, (∀ j, q < j → w.repr (bb l q) j = 0) ∧
      w.repr (bb l q) q = u l q * IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b q) :=
    fun l q => repr_of_sub_mem w (hbu l q)
  have hA := Model.exists_sum_mul_pow_eq_one (chartRing o (segreVec y) c) f cc hf hcc h1
  ext s
  constructor
  · rintro ⟨v, hv, hvz, rfl⟩
    have hloc : ∀ l, ∃ n : ℕ, f l ^ n * (w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i)) ∈
        chartRing o (segreVec y) c := by
      intro l
      obtain ⟨a, ha, hva⟩ := (hlat l v).1 ⟨0, by rw [pow_zero, one_smul]; exact hv⟩
      have hz := coeff_eq_zero_of_tri w (bb l) (fun q j hqj => (htri l q).1 j hqj)
        (fun q => by rw [(htri l q).2]; exact mul_ne_zero (hu l q).1 (hm _)) a (i + 1)
        (fun j hj => by rw [← hva]; exact hvz j (Fin.lt_def.mpr (by omega)))
      have hvi : w.repr v i = a i * (u l i * IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i)) := by
        rw [hva, repr_sum_smul, Finset.sum_eq_single i, (htri l i).2]
        · intro q _ hq
          rcases lt_or_gt_of_ne hq with hlt | hgt
          · rw [(htri l q).1 i hlt, mul_zero]
          · rw [hz q (Fin.lt_def.mp hgt), zero_mul]
        · simp
      obtain ⟨n1, hn1⟩ := ha i
      obtain ⟨n2, hn2⟩ := (hu l i).2.1
      refine ⟨n1 + n2, ?_⟩
      have hq : w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i) = a i * u l i := by
        rw [hvi]; field_simp [hm (b i)]
      rw [hq, show f l ^ (n1 + n2) * (a i * u l i) = (f l ^ n1 * a i) * (f l ^ n2 * u l i) by ring]
      exact mul_mem hn1 hn2
    choose nl hnl using hloc
    obtain ⟨d, hd, hd1⟩ := hA (∑ l, nl l)
    have hmul : ∀ l, f l ^ (∑ l, nl l) *
        (w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i)) ∈ chartRing o (segreVec y) c := by
      intro l
      have hle : nl l ≤ ∑ l, nl l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
      exact mul_mem (pow_mem (hf l) _) (hnl l)
    have ht : w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i) ∈ chartRing o (segreVec y) c := by
      have he : w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i) =
          ∑ l, d l * (f l ^ (∑ l, nl l) * (w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i))) := by
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul, hd1, one_mul]
      rw [he]
      exact Subalgebra.sum_mem _ fun l _ => mul_mem (hd l) (hmul l)
    exact ⟨_, ht, (div_mul_cancel₀ _ (hm (b i))).symm⟩
  · rintro ⟨a, ha, rfl⟩
    have hloc : ∀ l, ∃ n : ℕ, ∃ v : E, f l ^ n • v ∈ B.lat c ∧ (∀ j, i < j → w.repr v j = 0) ∧
        w.repr v i = a * ∏ k, y ⟨k, c k⟩ ^ b i k := by
      intro l
      have hcoef : ∀ q, ∃ n : ℕ, f l ^ n * (Pi.single i (a * (u l i)⁻¹) : Fin N → Ω) q ∈
          chartRing o (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg y) c := by
        intro q
        by_cases hq : q = i
        · subst hq
          obtain ⟨n2, hn2⟩ := (hu l q).2.2
          refine ⟨n2, ?_⟩
          rw [Pi.single_eq_same, show f l ^ n2 * (a * (u l q)⁻¹) = a * (f l ^ n2 * (u l q)⁻¹) by ring]
          exact mul_mem ha hn2
        · exact ⟨0, by rw [Pi.single_eq_of_ne hq, mul_zero]; exact zero_mem _⟩
      have hsum : (a * (u l i)⁻¹) • bb l i = ∑ q, (Pi.single i (a * (u l i)⁻¹) : Fin N → Ω) q • bb l q := by
        rw [Finset.sum_eq_single i]
        · rw [Pi.single_eq_same]
        · intro q _ hq; rw [Pi.single_eq_of_ne hq, zero_smul]
        · simp
      obtain ⟨n, hn⟩ := (hlat l ((a * (u l i)⁻¹) • bb l i)).2 ⟨_, hcoef, hsum⟩
      refine ⟨n, _, hn, fun j hj => ?_, ?_⟩
      · rw [map_smul, Finsupp.smul_apply, (htri l i).1 j hj, smul_zero]
      · rw [map_smul, Finsupp.smul_apply, (htri l i).2, smul_eq_mul]
        have hu0 := (hu l i).1
        simp only [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon]
        field_simp
    choose nl v hvl hvz hvi using hloc
    obtain ⟨d, hd, hd1⟩ := hA (∑ l, nl l)
    refine ⟨∑ l, (d l * f l ^ (∑ l, nl l)) • v l, ?_, fun j hj => ?_, ?_⟩
    · refine AddSubgroup.sum_mem _ fun l _ => ?_
      have hle : nl l ≤ ∑ l, nl l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      rw [← Nat.sub_add_cancel hle, pow_add, ← mul_assoc, mul_smul]
      exact B.stable c _ (mul_mem (hd l) (pow_mem (hf l) _)) _ (hvl l)
    · rw [repr_sum_smul]
      exact Finset.sum_eq_zero fun l _ => by rw [hvz l j hj, mul_zero]
    · rw [repr_sum_smul]
      simp_rw [hvi]
      rw [← Finset.sum_mul, hd1, one_mul]

end Main

theorem proof : Statement.{u, v, w} := by
  intro o _ Ω _ _ K _ ι _ y N E _ _ B w b
  exact ⟨forward, backward⟩

end GradedFrameCharacterisation

end GroundTheory.Heights₂.Heights.NumbersDVR
