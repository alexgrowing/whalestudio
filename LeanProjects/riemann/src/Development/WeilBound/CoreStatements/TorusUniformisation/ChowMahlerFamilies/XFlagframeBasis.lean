import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinGradedFrameIff

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_flagframe_basis

variable {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V] {N : ℕ}

theorem repr_expand (w u : Module.Basis (Fin N) Ω V) (v : V) (j : Fin N) :
    w.repr v j = ∑ q, u.repr v q * w.repr (u q) j := by
  conv_lhs => rw [← u.sum_repr v]
  exact GradedFrameCharacterisation.repr_sum_smul w _ _ j

theorem top_coord (w u : Module.Basis (Fin N) Ω V) (hup : ∀ i j, i < j → w.repr (u i) j = 0)
    (v : V) (i : Fin N) (hv : ∀ j, i < j → u.repr v j = 0) :
    (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = u.repr v i * w.repr (u i) i := by
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [repr_expand w u]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : i < q
    · rw [hv q hq, zero_mul]
    · rw [hup q j (lt_of_le_of_lt (not_lt.mp hq) hj), mul_zero]
  · rw [repr_expand w u]
    refine Finset.sum_eq_single i (fun q _ hq => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hq with h | h
    · rw [hup q i h, mul_zero]
    · rw [hv q h, zero_mul]

theorem vanish_above (w u : Module.Basis (Fin N) Ω V) (hup : ∀ i j, i < j → w.repr (u i) j = 0)
    (hd : ∀ i, w.repr (u i) i ≠ 0) (v : V) (i : Fin N) (hv : ∀ j, i < j → w.repr v j = 0) :
    ∀ j, i < j → u.repr v j = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hne : (Finset.univ.filter (fun j => i < j ∧ u.repr v j ≠ 0)).Nonempty := by
    obtain ⟨j, hj, hj'⟩ := hcon
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hj'⟩⟩
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image _ id hne
  have hm := (Finset.mem_filter.mp hmS).2
  have habove : ∀ j, m < j → u.repr v j = 0 := by
    intro j hj
    by_contra h0
    have hjS := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hm.1 hj, h0⟩)
    exact absurd hjS (not_le.mpr hj)
  have ht := top_coord w u hup v m habove
  have h0 := hv m hm.1
  rw [ht.2] at h0
  exact mul_ne_zero hm.2 (hd m) h0

theorem exists_basis (w : Module.Basis (Fin N) Ω V) (f : Fin N → V)
    (hup : ∀ i j, i < j → w.repr (f i) j = 0) (hd : ∀ i, w.repr (f i) i ≠ 0) :
    ∃ u : Module.Basis (Fin N) Ω V, ∀ i, u i = f i := by
  classical
  rcases isEmpty_or_nonempty (Fin N) with hN | hN
  · exact ⟨w, fun i => isEmptyElim i⟩
  · have hli : LinearIndependent Ω f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      by_contra hcon
      push_neg at hcon
      have hne : (Finset.univ.filter (fun j => g j ≠ 0)).Nonempty := by
        obtain ⟨j, hj⟩ := hcon
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image _ id hne
      have hm := (Finset.mem_filter.mp hmS).2
      have h0 := congrArg (fun v => w.repr v m) hg
      simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero,
        Finsupp.coe_zero, Pi.zero_apply] at h0
      rw [Finset.sum_eq_single m] at h0
      · exact mul_ne_zero hm (hd m) h0
      · intro q _ hqm
        rcases lt_or_gt_of_ne hqm with h | h
        · rw [hup q m h, mul_zero]
        · have hgq : g q = 0 := by
            by_contra hq
            exact absurd (hmax q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩)) (not_le.mpr h)
          rw [hgq, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ m) h
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hli ?_, fun i => ?_⟩
    · rw [Module.finrank_eq_card_basis w]
    · rw [coe_basisOfLinearIndependentOfCardEqFinrank]

theorem coords_mem {O : Type*} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) (L : AddSubgroup V)
    (u : Module.Basis (Fin N) Ω V) (hst : ∀ a ∈ R, ∀ i, a • u i ∈ L)
    (htop : ∀ v ∈ L, ∀ i, (∀ j, i < j → u.repr v j = 0) → u.repr v i ∈ R) :
    ∀ v ∈ L, ∀ i, u.repr v i ∈ R := by
  classical
  have main : ∀ k : ℕ, ∀ v ∈ L, (∀ j : Fin N, k ≤ j.val → u.repr v j = 0) → ∀ i, u.repr v i ∈ R := by
    intro k
    induction k with
    | zero =>
      intro v _ hv i
      rw [hv i (Nat.zero_le _)]
      exact R.zero_mem
    | succ k ih =>
      intro v hvL hv
      by_cases hk : k < N
      · have ha : u.repr v ⟨k, hk⟩ ∈ R :=
          htop v hvL ⟨k, hk⟩ (fun j hj => hv j (Nat.succ_le_of_lt (Fin.lt_def.mp hj)))
        have hv'L : v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩ ∈ L := L.sub_mem hvL (hst _ ha _)
        have hrep : ∀ j, u.repr (v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩) j =
            u.repr v j - u.repr v ⟨k, hk⟩ * (if (⟨k, hk⟩ : Fin N) = j then 1 else 0) := by
          intro j
          rw [map_sub, map_smul, Module.Basis.repr_self, Finsupp.coe_sub, Pi.sub_apply, Finsupp.smul_apply,
            Finsupp.single_apply, smul_eq_mul]
        have hv' : ∀ j : Fin N, k ≤ j.val → u.repr (v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩) j = 0 := by
          intro j hj
          rw [hrep j]
          rcases Nat.lt_or_eq_of_le hj with h | h
          · have hne : (⟨k, hk⟩ : Fin N) ≠ j := fun e => by
              rw [← e] at h
              exact lt_irrefl _ h
            rw [hv j h, if_neg hne, mul_zero, sub_zero]
          · have he : (⟨k, hk⟩ : Fin N) = j := Fin.ext h
            subst he
            rw [if_pos rfl, mul_one, sub_self]
        intro i
        have hi := ih _ hv'L hv' i
        rw [hrep i] at hi
        have h2 : u.repr v ⟨k, hk⟩ * (if (⟨k, hk⟩ : Fin N) = i then (1 : Ω) else 0) ∈ R := by
          split_ifs
          · rw [mul_one]
            exact ha
          · rw [mul_zero]
            exact R.zero_mem
        have h3 := R.add_mem hi h2
        rwa [sub_add_cancel] at h3
      · intro i
        exact ih v hvL (fun j hj => hv j (by have := j.isLt; omega)) i
  intro v hv i
  exact main N v hv (fun j hj => absurd j.isLt (not_lt.mpr hj)) i

end PositivityTheory.Xgn.A_flagframe_basis

open PositivityTheory.Xgn.A_flagframe_basis in
theorem PositivityTheory.Xgn.t_flagframe_basis : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b ↔ ∀ s, mseg x s ≠ 0 → ∃ u : Module.Basis (Fin N) Ω V, (∀ i j, i < j → w.repr (u i) j = 0) ∧ (∀ i, w.repr (u i) i = chartMon x s (b i)) ∧ ∀ v, v ∈ E.lat s ↔ ∀ i, u.repr v i ∈ chartRing O (mseg x) s := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ E w b
  have hmon : ∀ s, mseg x s ≠ 0 → ∀ d : K → ℤ, chartMon x s d ≠ 0 := by
    intro s hs d
    have hs' : ∏ k : K, x ⟨k, s k⟩ ≠ 0 := hs
    show ∏ k : K, x ⟨k, s k⟩ ^ d k ≠ 0
    exact Finset.prod_ne_zero_iff.mpr fun k _ =>
      zpow_ne_zero _ (Finset.prod_ne_zero_iff.mp hs' k (Finset.mem_univ _))
  constructor
  · intro hF s hs
    have hdeg : ∀ i, ∃ f ∈ E.lat s, (∀ j, i < j → w.repr f j = 0) ∧ w.repr f i = chartMon x s (b i) := by
      intro i
      have hmem : chartMon x s (b i) ∈ degLat O x (b i) s := ⟨1, Subalgebra.one_mem _, (one_mul _).symm⟩
      rw [← hF.graded s hs i] at hmem
      exact hmem
    choose f hfL hfup hfd using hdeg
    obtain ⟨u, hu⟩ := exists_basis w f hfup (fun i => by rw [hfd i]; exact hmon s hs (b i))
    have hup_u : ∀ i j, i < j → w.repr (u i) j = 0 := fun i j hij => by
      rw [hu i]
      exact hfup i j hij
    refine ⟨u, hup_u, fun i => by rw [hu i]; exact hfd i, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · refine coords_mem (chartRing O (mseg x) s) (E.lat s) u
        (fun a ha i => by rw [hu i]; exact E.stable s a ha _ (hfL i)) ?_ v hv
      intro v' hv' i hup'
      have ht := top_coord w u hup_u v' i hup'
      have hin : w.repr v' i ∈ degLat O x (b i) s := by
        rw [← hF.graded s hs i]
        exact ⟨v', hv', ht.1, rfl⟩
      obtain ⟨a, ha, hae⟩ := hin
      rw [ht.2, hu i, hfd i] at hae
      have hc := mul_right_cancel₀ (hmon s hs (b i)) hae
      rw [hc]
      exact ha
    · rw [← u.sum_repr v]
      exact AddSubgroup.sum_mem _ fun q _ => by
        rw [hu q]
        exact E.stable s _ (hv q) _ (hfL q)
  · intro hR
    refine ⟨fun s hs i => ?_⟩
    obtain ⟨u, hup, hdiag, hmem⟩ := hR s hs
    ext t
    constructor
    · rintro ⟨v, hv, habove, rfl⟩
      have hd : ∀ i, w.repr (u i) i ≠ 0 := fun i => by
        rw [hdiag i]
        exact hmon s hs (b i)
      have hu_above := vanish_above w u hup hd v i habove
      have ht := top_coord w u hup v i hu_above
      exact ⟨u.repr v i, (hmem v).mp hv i, by rw [ht.2, hdiag i]; rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a • u i, (hmem _).mpr fun j => ?_, fun j hj => ?_, ?_⟩
      · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        split_ifs
        · rw [mul_one]
          exact ha
        · rw [mul_zero]
          exact Subalgebra.zero_mem _
      · rw [map_smul, Finsupp.smul_apply, hup i j hj, smul_zero]
      · rw [map_smul, Finsupp.smul_apply, hdiag i, smul_eq_mul]
        rfl
