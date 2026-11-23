import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerRest
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing exists_pow_mul_mem_chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart IsPull SameGeneric)

namespace JoinPullbackAlt

section Charts

variable {Ω : Type*} [Field Ω] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def zChart (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k, ι' k :=
  fun k => s (.inr k)

def combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => u k

theorem restrictChart_combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) :
    restrictChart (combChart t u) = t :=
  rfl

theorem zChart_combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) : zChart (combChart t u) = u :=
  rfl

theorem mseg_joinCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (zChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

variable (O : Type*) [CommRing O] [Algebra O Ω]

theorem chartRing_le_join (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (joinCoord x z) s ≠ 0) :
    chartRing O (mseg x) (restrictChart s) ≤ chartRing O (mseg (joinCoord x z)) s := by
  have hz : mseg z (zChart s) ≠ 0 := by
    rw [mseg_joinCoord] at hs
    exact right_ne_zero_of_mul hs
  unfold chartRing
  apply Algebra.adjoin_le
  rintro _ ⟨t', rfl⟩
  have h : mseg x t' / mseg x (restrictChart s) =
      mseg (joinCoord x z) (combChart t' (zChart s)) / mseg (joinCoord x z) s := by
    rw [mseg_joinCoord x z (combChart t' (zChart s)), mseg_joinCoord x z s, restrictChart_combChart,
      zChart_combChart, mul_div_mul_right _ _ hz]
  simp only
  rw [h]
  exact div_mem_chartRing (o := O) _ _ _

theorem zRatio_mem (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (s s' : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs' : mseg (joinCoord x z) s' ≠ 0) :
    mseg z (zChart s) / mseg z (zChart s') ∈ chartRing O (mseg (joinCoord x z)) s' := by
  have hx : mseg x (restrictChart s') ≠ 0 := by
    rw [mseg_joinCoord] at hs'
    exact left_ne_zero_of_mul hs'
  have h : mseg z (zChart s) / mseg z (zChart s') =
      mseg (joinCoord x z) (combChart (restrictChart s') (zChart s)) / mseg (joinCoord x z) s' := by
    rw [mseg_joinCoord x z (combChart (restrictChart s') (zChart s)), mseg_joinCoord x z s',
      restrictChart_combChart, zChart_combChart, mul_div_mul_left _ _ hx]
  rw [h]
  exact div_mem_chartRing (o := O) _ _ _

end Charts

section Pull

variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

def pullLat (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (E : ChartBundle O (mseg x) N V)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : AddSubgroup V :=
  AddSubgroup.closure
    {v | ∃ a ∈ chartRing O (mseg (joinCoord x z)) s, ∃ e ∈ E.lat (restrictChart s), v = a • e}

theorem pullLat_stable (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (E : ChartBundle O (mseg x) N V)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (a : Ω) (ha : a ∈ chartRing O (mseg (joinCoord x z)) s)
    (v : V) (hv : v ∈ pullLat O x z E s) : a • v ∈ pullLat O x z E s := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨b, hb, e, he, rfl⟩ := hv
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨a * b, mul_mem ha hb, e, he, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
  | neg v _ hv => rw [smul_neg]; exact neg_mem hv

theorem pullLat_coords (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (E : ChartBundle O (mseg x) N V)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0) (f : Ω)
    (hf : f ∈ chartRing O (mseg x) (restrictChart s)) (b : Fin N → V)
    (hiff : ∀ e, (∃ n : ℕ, f ^ n • e ∈ E.lat (restrictChart s)) ↔
        ∃ a : Fin N → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ chartRing O (mseg x) (restrictChart s)) ∧
          e = ∑ q, a q • b q)
    (v : V) (hv : v ∈ pullLat O x z E s) :
    ∃ a : Fin N → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ chartRing O (mseg (joinCoord x z)) s) ∧
      v = ∑ q, a q • b q := by
  have hle := chartRing_le_join O x z s hs
  have hf' : f ∈ chartRing O (mseg (joinCoord x z)) s := hle hf
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, e', he', rfl⟩ := hv
    obtain ⟨α, hα, rfl⟩ := (hiff e').1 ⟨0, by simpa using he'⟩
    refine ⟨fun q => a * α q, fun q => ?_, ?_⟩
    · obtain ⟨m, hm⟩ := hα q
      refine ⟨m, ?_⟩
      rw [mul_left_comm]
      exact mul_mem ha (hle hm)
    · rw [Finset.smul_sum]
      simp only [smul_smul]
  | zero => exact ⟨0, fun q => ⟨0, by simp⟩, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨a, ha, rfl⟩ := hv
    obtain ⟨a', ha', rfl⟩ := hw
    refine ⟨a + a', fun q => ?_, by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
    obtain ⟨m, hm⟩ := ha q
    obtain ⟨m', hm'⟩ := ha' q
    refine ⟨m + m', ?_⟩
    have h : f ^ (m + m') * (a + a') q = f ^ m' * (f ^ m * a q) + f ^ m * (f ^ m' * a' q) := by
      simp only [Pi.add_apply]
      ring
    rw [h]
    exact add_mem (mul_mem (pow_mem hf' _) hm) (mul_mem (pow_mem hf' _) hm')
  | neg v _ hv =>
    obtain ⟨a, ha, rfl⟩ := hv
    refine ⟨-a, fun q => ?_, by simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]⟩
    obtain ⟨m, hm⟩ := ha q
    refine ⟨m, ?_⟩
    simp only [Pi.neg_apply, mul_neg]
    exact neg_mem hm

theorem pullLat_frame (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (E : ChartBundle O (mseg x) N V)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing O (mseg (joinCoord x z)) s) ∧
      (∀ l, c l ∈ chartRing O (mseg (joinCoord x z)) s) ∧ ∑ l, c l * f l = 1 ∧
      ∀ l, ∃ b : Fin N → V, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
        ∀ e, (∃ n : ℕ, f l ^ n • e ∈ pullLat O x z E s) ↔
          ∃ a : Fin N → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O (mseg (joinCoord x z)) s) ∧
            e = ∑ q, a q • b q := by
  have ht : mseg x (restrictChart s) ≠ 0 := by
    have hs' := hs
    rw [mseg_joinCoord] at hs'
    exact left_ne_zero_of_mul hs'
  have hle := chartRing_le_join O x z s hs
  obtain ⟨k, f, c, hf, hc, hsum, hl⟩ := E.frame _ ht
  refine ⟨k, f, c, fun l => hle (hf l), fun l => hle (hc l), hsum, fun l => ?_⟩
  obtain ⟨b, hli, hspan, hiff⟩ := hl l
  refine ⟨b, hli, hspan, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨a, ha, hfe⟩ := pullLat_coords O x z E s hs (f l) (hf l) b hiff _ hn
    have he : e ∈ Submodule.span Ω (Set.range b) := by rw [hspan]; exact Submodule.mem_top
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
    have hcoef : ∀ q, f l ^ n * cc q = a q := by
      have h0 : ∑ q, (f l ^ n * cc q - a q) • b q = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hcc, ← hfe, sub_self]
      intro q
      exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 q)
    refine ⟨cc, fun q => ?_, hcc.symm⟩
    obtain ⟨m, hm⟩ := ha q
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_assoc, hcoef]
    exact hm
  · rintro ⟨a, ha, rfl⟩
    have hb : ∀ q, ∃ m : ℕ, f l ^ m • b q ∈ E.lat (restrictChart s) := fun q =>
      (hiff (b q)).2 ⟨fun q' => if q' = q then 1 else 0, fun q' => ⟨0, by
        simp only [pow_zero, one_mul]
        split_ifs
        · exact one_mem _
        · exact zero_mem _⟩, by simp [ite_smul]⟩
    choose m hm using hb
    choose n hn using ha
    refine ⟨∑ q, (n q + m q), ?_⟩
    rw [Finset.smul_sum]
    refine sum_mem fun q _ => ?_
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (f := fun q => n q + m q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q))
    have h : f l ^ (∑ q, (n q + m q)) • (a q • b q) =
        (f l ^ d * (f l ^ n q * a q)) • (f l ^ m q • b q) := by
      rw [hd, smul_smul, smul_smul]
      congr 1
      ring
    rw [h]
    exact AddSubgroup.subset_closure
      ⟨_, mul_mem (pow_mem (hle (hf l)) _) (hn q), _, hm q, rfl⟩

theorem pullLat_overlap (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (E : ChartBundle O (mseg x) N V)
    (s s' : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0)
    (hs' : mseg (joinCoord x z) s' ≠ 0) (v : V) (hv : v ∈ pullLat O x z E s) :
    ∃ m : ℕ, (mseg (joinCoord x z) s / mseg (joinCoord x z) s') ^ m • v ∈ pullLat O x z E s' := by
  have hρ : mseg (joinCoord x z) s / mseg (joinCoord x z) s' ∈ chartRing O (mseg (joinCoord x z)) s' :=
    div_mem_chartRing (o := O) _ _ _
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, e, he, rfl⟩ := hv
    have ht : mseg x (restrictChart s) ≠ 0 := by
      have h := hs
      rw [mseg_joinCoord] at h
      exact left_ne_zero_of_mul h
    have ht' : mseg x (restrictChart s') ≠ 0 := by
      have h := hs'
      rw [mseg_joinCoord] at h
      exact left_ne_zero_of_mul h
    obtain ⟨m₁, hm₁⟩ := E.overlap _ _ ht ht' e he
    obtain ⟨m₂, hm₂⟩ := exists_pow_mul_mem_chartRing (o := O) (mseg (joinCoord x z)) s s' hs ha
    have hμ := zRatio_mem O x z s s' hs'
    refine ⟨m₁ + m₂, ?_⟩
    have h : (mseg (joinCoord x z) s / mseg (joinCoord x z) s') ^ (m₁ + m₂) • (a • e) =
        ((mseg (joinCoord x z) s / mseg (joinCoord x z) s') ^ m₂ * a *
          (mseg z (zChart s) / mseg z (zChart s')) ^ m₁) •
          ((mseg x (restrictChart s) / mseg x (restrictChart s')) ^ m₁ • e) := by
      rw [smul_smul, smul_smul]
      congr 1
      rw [mseg_joinCoord x z s, mseg_joinCoord x z s']
      ring
    rw [h]
    exact AddSubgroup.subset_closure ⟨_, mul_mem hm₂ (pow_mem hμ _), _, hm₁, rfl⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
  | add v w _ _ hv hw =>
    obtain ⟨m, hm⟩ := hv
    obtain ⟨n, hn⟩ := hw
    refine ⟨m + n, ?_⟩
    rw [smul_add]
    have h₁ : (mseg (joinCoord x z) s / mseg (joinCoord x z) s') ^ (m + n) • v =
        (mseg (joinCoord x z) s / mseg (joinCoord x z) s') ^ n •
          ((mseg (joinCoord x z) s / mseg (joinCoord x z) s') ^ m • v) := by
      rw [smul_smul, ← pow_add, add_comm n m]
    have h₂ : (mseg (joinCoord x z) s / mseg (joinCoord x z) s') ^ (m + n) • w =
        (mseg (joinCoord x z) s / mseg (joinCoord x z) s') ^ m •
          ((mseg (joinCoord x z) s / mseg (joinCoord x z) s') ^ n • w) := by
      rw [smul_smul, ← pow_add]
    rw [h₁, h₂]
    exact add_mem (pullLat_stable O x z E s' _ (pow_mem hρ _) _ hm)
      (pullLat_stable O x z E s' _ (pow_mem hρ _) _ hn)
  | neg v _ hv =>
    obtain ⟨m, hm⟩ := hv
    exact ⟨m, by rw [smul_neg]; exact neg_mem hm⟩

def pullBundle (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (E : ChartBundle O (mseg x) N V) :
    ChartBundle O (mseg (joinCoord x z)) N V where
  lat := pullLat O x z E
  stable := pullLat_stable O x z E
  frame := pullLat_frame O x z E
  overlap := pullLat_overlap O x z E

theorem isPull_pullBundle (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (E : ChartBundle O (mseg x) N V) :
    IsPull O x z E (pullBundle O x z E) :=
  fun _ _ => rfl

theorem pullLat_const [IsDomain O] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (E E' : ChartBundle O (mseg x) N V) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (h : ∀ v ∈ E.lat (restrictChart s), ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ E'.lat (restrictChart s))
    (v : V) (hv : v ∈ pullLat O x z E s) :
    ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ pullLat O x z E' s := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, e, he, rfl⟩ := hv
    obtain ⟨c, hc, hce⟩ := h e he
    refine ⟨c, hc, ?_⟩
    rw [smul_comm]
    exact AddSubgroup.subset_closure ⟨a, ha, _, hce, rfl⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add v w _ _ hv hw =>
    obtain ⟨c₁, hc₁, h₁⟩ := hv
    obtain ⟨c₂, hc₂, h₂⟩ := hw
    refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
    have e : algebraMap O Ω (c₁ * c₂) • (v + w) =
        algebraMap O Ω c₂ • (algebraMap O Ω c₁ • v) + algebraMap O Ω c₁ • (algebraMap O Ω c₂ • w) := by
      rw [smul_add, smul_smul, smul_smul, map_mul, mul_comm (algebraMap O Ω c₂)]
    rw [e]
    exact add_mem (pullLat_stable O x z E' s _ (Subalgebra.algebraMap_mem _ _) _ h₁)
      (pullLat_stable O x z E' s _ (Subalgebra.algebraMap_mem _ _) _ h₂)
  | neg v _ hv =>
    obtain ⟨c, hc, h⟩ := hv
    exact ⟨c, hc, by rw [smul_neg]; exact neg_mem h⟩

theorem sameGeneric_pullBundle [IsDomain O] [IsDiscreteValuationRing O] (x : (Σ k, ι k) → Ω)
    (z : (Σ k, ι' k) → Ω) (E E' : ChartBundle O (mseg x) N V) (h : SameGeneric O x E E') :
    SameGeneric O (joinCoord x z) (pullBundle O x z E) (pullBundle O x z E') := by
  intro s hs
  have ht : mseg x (restrictChart s) ≠ 0 := by
    have h' := hs
    rw [mseg_joinCoord] at h'
    exact left_ne_zero_of_mul h'
  exact ⟨pullLat_const O x z E E' s (h _ ht).1, pullLat_const O x z E' E s (h _ ht).2⟩

end Pull

end JoinPullbackAlt

open JoinPullbackAlt in

theorem JoinPullbackAlt.proof : JoinPullbackAlt.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z N V _ _ E E' hE
  exact ⟨pullBundle O x z E, pullBundle O x z E', isPull_pullBundle O x z E, isPull_pullBundle O x z E',
    sameGeneric_pullBundle O x z E E' hE⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
