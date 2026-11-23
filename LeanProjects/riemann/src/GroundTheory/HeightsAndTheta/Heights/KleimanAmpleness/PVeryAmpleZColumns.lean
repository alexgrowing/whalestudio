import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZColumnsSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZColumnsCechPartition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace VeryAmpleZColumns

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ}

omit [Module S E] [IsScalarTower S Ω E] in
theorem chart_smul {I : Chart x} (a : chartRing S x I) (e : E) : a • e = (a : Ω) • e := rfl

theorem prod_mem_pow {I : Chart x} (Q : Submodule (chartRing S x I) Ω) (h : Fin (r + 1) → Ω)
    (hh : ∀ j, h j ∈ Q) (T : Finset (Fin (r + 1))) : ∏ j ∈ T, h j ∈ Q ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.card_empty, pow_zero]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact Submodule.mul_mem_mul (hh a) ih

omit [Module S E] [IsScalarTower S Ω E] in

theorem smul_mem_twist_pow {G : SubSystem S x E} {H : SubSystem S x Ω} {I : Chart x} {n c : ℕ}
    {q : Ω} (hq : q ∈ H.sub I ^ c) {z : E} (hz : z ∈ (G.twist (H.pow n)).sub I) :
    q • z ∈ (G.twist (H.pow (n + c))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q', hq', y, hy, rfl⟩ := hy
    refine Submodule.subset_span ⟨q' * q, ?_, y, hy, by rw [mul_comm q' q, mul_smul]⟩
    rw [SubSystem.pow_sub] at hq' ⊢
    rw [pow_add]
    exact Submodule.mul_mem_mul hq' hq
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [smul_add]; exact add_mem hy hy'
  | smul a y _ hy =>
    have e1 : q • (a • y) = a • (q • y) := by
      rw [chart_smul, chart_smul, smul_smul, smul_smul, mul_comm]
    rw [e1]
    exact Submodule.smul_mem _ a hy

omit [Module S E] [IsScalarTower S Ω E] in

theorem smul_mem_twist_of_inv {G : SubSystem S x E} {H : SubSystem S x Ω} {I : Chart x} {m c : ℕ}
    {w : Ω} (hw : ∀ q ∈ H.sub I ^ m, w * q ∈ chartRing S x I) {z : E}
    (hz : z ∈ (G.twist (H.pow (c + m))).sub I) : w • z ∈ (G.twist (H.pow c)).sub I := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, hq, y, hy, rfl⟩ := hy
    rw [SubSystem.pow_sub, pow_add] at hq
    refine Submodule.subset_span ⟨w * q, ?_, y, hy, by rw [smul_smul]⟩
    rw [SubSystem.pow_sub]
    refine Submodule.mul_induction_on hq (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · have e1 : w * (a * b) = (⟨w * b, hw b hb⟩ : chartRing S x I) • a := by
        rw [chartRing_smul_def]; ring
      rw [e1]
      exact Submodule.smul_mem _ _ ha
    · rw [mul_add]; exact add_mem ha hb
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [smul_add]; exact add_mem hy hy'
  | smul a y _ hy =>
    have e1 : w • (a • y) = a • (w • y) := by
      rw [chart_smul, chart_smul, smul_smul, smul_smul, mul_comm]
    rw [e1]
    exact Submodule.smul_mem _ a hy

variable {G : SubSystem S x E} {H : SubSystem S x Ω} {h : Fin (r + 1) → Ω} {I : Chart x}

omit [Module S E] [IsScalarTower S Ω E] in

theorem pow_mono (hH : ∀ j, h j ∈ H.sub I) {J : Chart h} {e : E} {n : ℕ}
    (he : xProd J ^ n • e ∈ (G.twist (H.pow (J.1.card * n))).sub I) (k : ℕ) :
    xProd J ^ (n + k) • e ∈ (G.twist (H.pow (J.1.card * (n + k)))).sub I := by
  have hq : xProd J ^ k ∈ H.sub I ^ (J.1.card * k) := by
    rw [pow_mul]; exact Submodule.pow_mem_pow _ (prod_mem_pow _ h hH J.1) k
  have := smul_mem_twist_pow hq he
  rwa [show J.1.card * (n + k) = J.1.card * n + J.1.card * k by ring, pow_add,
    mul_comm (xProd J ^ n), mul_smul]

theorem exists_pow_of_mem (hH : ∀ j, h j ∈ H.sub I) {J : Chart h} {e : E}
    (he : e ∈ secsOnZChart G H h I J) :
    ∃ n, ∀ m, n ≤ m → xProd J ^ m • e ∈ (G.twist (H.pow (J.1.card * m))).sub I := by
  suffices h0 : ∃ n, xProd J ^ n • e ∈ (G.twist (H.pow (J.1.card * n))).sub I by
    obtain ⟨n, hn⟩ := h0
    refine ⟨n, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact pow_mono hH hn k
  induction he using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨n1, h1⟩ := hy
    obtain ⟨n2, h2⟩ := hy'
    refine ⟨n1 + n2, ?_⟩
    rw [smul_add]
    refine add_mem (pow_mono hH h1 n2) ?_
    have := pow_mono hH h2 n1
    rwa [add_comm n2 n1] at this
  | smul s y _ hy =>
    obtain ⟨n, hn⟩ := hy
    refine ⟨n, ?_⟩
    rw [smul_comm]
    exact Submodule.smul_of_tower_mem _ s hn

omit [IsScalarTower S Ω E] in

theorem mono (hH : ∀ j, h j ∈ H.sub I) {J J' : Chart h} (hJJ' : J.1 ⊆ J'.1) :
    secsOnZChart G H h I J ≤ secsOnZChart G H h I J' := by
  classical
  refine Submodule.span_le.mpr ?_
  rintro e ⟨n, hn⟩
  refine Submodule.subset_span ⟨n, ?_⟩
  have hq : (∏ j ∈ J'.1 \ J.1, h j) ^ n ∈ H.sub I ^ ((J'.1 \ J.1).card * n) := by
    rw [pow_mul]; exact Submodule.pow_mem_pow _ (prod_mem_pow _ h hH _) n
  have := smul_mem_twist_pow hq hn
  have hx : xProd J' = (∏ j ∈ J'.1 \ J.1, h j) * xProd J := (Finset.prod_sdiff hJJ').symm
  have hc : J'.1.card = J.1.card + (J'.1 \ J.1).card := by
    rw [Finset.card_sdiff_of_subset hJJ']; have := Finset.card_le_card hJJ'; omega
  rw [hx, mul_pow, mul_smul, hc, add_mul]
  exact this

theorem exists_partition {H : LineBundle S x} (hV : IsVeryAmpleBy H.toSubSystem h) (I : Chart x)
    (m : ℕ) : ∃ w : Fin (r + 1) → Ω, ∑ k, w k * h k ^ m = 1 ∧
      ∀ k, ∀ q ∈ H.sub I ^ m, w k * q ∈ chartRing S x I := by
  have hH : ∀ j, h j ∈ H.sub I := fun j => (Submodule.mem_iInf _).mp (hV.mem_secs j) I
  obtain ⟨Q', hQ'⟩ := H.invertible I
  have h1 : (1 : Ω) ∈ H.sub I * Q' := by
    rw [hQ']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have key : ∀ z ∈ H.sub I * Q', ∃ u : Fin (r + 1) → Ω, (∀ k, u k ∈ Q') ∧ ∑ k, h k * u k = z := by
    intro z hz
    refine Submodule.mul_induction_on hz (fun c hc q hq => ?_) ?_
    · rw [← hV.generates I] at hc
      obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hc
      refine ⟨fun k => f k • q, fun k => Submodule.smul_mem _ _ hq, ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [chartRing_smul_def]; ring
    · rintro a b ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
      exact ⟨u + u', fun k => add_mem (hu k) (hu' k), by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]⟩
  obtain ⟨u, hu, hsum⟩ := key 1 h1
  have hinv : ∀ k, ∀ q ∈ H.sub I, u k * q ∈ chartRing S x I := fun k q hq => by
    have := Submodule.mul_mem_mul hq (hu k)
    rw [hQ', Submodule.mem_one] at this
    obtain ⟨y, hy⟩ := this
    rw [mul_comm, ← hy]; exact y.2
  have hinvm : ∀ k, ∀ (m : ℕ), ∀ q ∈ H.sub I ^ m, u k ^ m * q ∈ chartRing S x I := by
    intro k m
    induction m with
    | zero =>
      intro q hq
      rw [pow_zero, Submodule.mem_one] at hq
      obtain ⟨y, rfl⟩ := hq
      rw [pow_zero, one_mul]; exact y.2
    | succ m ih =>
      intro q hq
      rw [pow_succ] at hq
      refine Submodule.mul_induction_on hq (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · rw [show u k ^ (m + 1) * (a * b) = (u k ^ m * a) * (u k * b) by ring]
        exact mul_mem (ih a ha) (hinv k b hb)
      · rw [mul_add]; exact add_mem ha hb
  let b : Fin (r + 1) → chartRing S x I := fun k => ⟨h k * u k, by
    rw [mul_comm]; exact hinv k _ (hH k)⟩
  have htop : Ideal.span (Set.range b) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun _ => 1, Subtype.ext ?_⟩
    simp only [one_mul, b, AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
    exact hsum
  have htop' := Ideal.span_pow_eq_top _ htop m
  rw [← Set.range_comp] at htop'
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (htop' ▸ Submodule.mem_top : (1 : chartRing S x I) ∈ Ideal.span (Set.range ((fun y => y ^ m) ∘ b)))
  refine ⟨fun k => (c k : Ω) * u k ^ m, ?_, fun k q hq => ?_⟩
  · have := congrArg (fun y : chartRing S x I => (y : Ω)) hc
    simp only [Function.comp_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      SubmonoidClass.coe_pow, OneMemClass.coe_one, b] at this
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [mul_assoc]; exact mul_mem (c k).2 (hinvm k m q hq)

end VeryAmpleZColumns

open VeryAmpleZColumns in

theorem VeryAmpleZColumns.proof : VeryAmpleZColumns.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hV I
  have hH : ∀ j, h j ∈ H.sub I := fun j => (Submodule.mem_iInf _).mp (hV.mem_secs j) I

  have hne : ∃ k, h k ≠ 0 := by
    obtain ⟨w, hw, -⟩ := exists_partition hV I 1
    by_contra hall
    simp only [not_exists, not_not] at hall
    simp [hall] at hw
  obtain ⟨k0, hk0⟩ := hne
  let J0 : Cech.Idx (support h) 0 :=
    ⟨⟨{k0}, Finset.singleton_nonempty k0, Finset.singleton_subset_iff.mpr ((mem_support h).mpr hk0)⟩,
      Finset.card_singleton k0⟩
  refine ⟨fun J J' hJJ' => mono hH hJJ', fun J e he => ?_, fun b _ hb => hb J0, ?_, ?_⟩
  ·
    refine Submodule.subset_span ⟨0, ?_⟩
    rw [pow_zero, one_smul, mul_zero]
    change e ∈ (G.toSubSystem.twist (twistSys S x 0)).sub I
    rw [SubSystem.twist_twistSys_zero]
    exact he
  ·
    intro s hs hds
    have hconst := Cech.Partition.const hds
    refine ⟨s J0, ?_, fun J => hconst J J0⟩
    have hex : ∀ J : Cech.Idx (support h) 0, ∃ n, ∀ m, n ≤ m →
        xProd J.1 ^ m • s J0 ∈ (G.toSubSystem.twist (H.toSubSystem.pow (J.1.1.card * m))).sub I :=
      fun J => by
        have := exists_pow_of_mem (G := G.toSubSystem) hH (hs J (Set.mem_univ _))
        rwa [hconst J J0] at this
    choose f hf using hex
    obtain ⟨m, hm1, hfm⟩ : ∃ m, 1 ≤ m ∧ ∀ J, f J ≤ m :=
      ⟨Finset.univ.sup f + 1, by omega, fun J => (Finset.le_sup (Finset.mem_univ J)).trans (Nat.le_succ _)⟩
    obtain ⟨w, hw, hwinv⟩ := exists_partition hV I m
    have hb : s J0 = ∑ k, w k • (h k ^ m • s J0) := by
      simp_rw [smul_smul]
      rw [← Finset.sum_smul, hw, one_smul]
    rw [hb]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : h k = 0
    · rw [hk, zero_pow (by omega), zero_smul, smul_zero]; exact zero_mem _
    · let Jk : Cech.Idx (support h) 0 :=
        ⟨⟨{k}, Finset.singleton_nonempty k, Finset.singleton_subset_iff.mpr ((mem_support h).mpr hk)⟩,
          Finset.card_singleton k⟩
      have h1 := hf Jk m (hfm Jk)
      have hx : xProd Jk.1 = h k := Finset.prod_singleton _ _
      have hc : Jk.1.1.card * m = 0 + m := by
        show ({k} : Finset (Fin (r + 1))).card * m = 0 + m
        rw [Finset.card_singleton]; ring
      rw [hx, hc] at h1
      have h2 := smul_mem_twist_of_inv (hwinv k) h1
      change _ ∈ (G.toSubSystem.twist (twistSys S x 0)).sub I at h2
      rw [SubSystem.twist_twistSys_zero] at h2
      exact h2
  ·
    intro p s hs hds
    have hex : ∀ J : Cech.Idx (support h) (p + 1), ∃ n, ∀ m, n ≤ m →
        xProd J.1 ^ m • s J ∈ (G.toSubSystem.twist (H.toSubSystem.pow (J.1.1.card * m))).sub I :=
      fun J => exists_pow_of_mem (G := G.toSubSystem) hH (hs J (Set.mem_univ _))
    choose f hf using hex
    obtain ⟨m, hm1, hfm⟩ : ∃ m, 1 ≤ m ∧ ∀ J, f J ≤ m :=
      ⟨Finset.univ.sup f + 1, by omega, fun J => (Finset.le_sup (Finset.mem_univ J)).trans (Nat.le_succ _)⟩
    obtain ⟨w, hw, hwinv⟩ := exists_partition hV I m
    refine Cech.Partition.exact_of_partition (A := Ω) _ s hds (fun k => w k * h k ^ m) ?_ ?_
    · rw [← hw]
      refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
      have : h k = 0 := by
        by_contra hne
        exact hk ((mem_support h).mpr hne)
      rw [this, zero_pow (by omega), mul_zero]
    · intro K k hk hkK
      let L : Cech.Idx (support h) (p + 1) :=
        ⟨⟨insert k K.1.1, Finset.insert_nonempty _ _, Finset.insert_subset hk K.1.2.2⟩, by
          rw [Finset.card_insert_of_notMem hkK, K.2]⟩
      rw [show Cech.Partition.onSet s (insert k K.1.1) = s L from Cech.Partition.onSet_idx s L]
      have h1 := hf L m (hfm L)
      have hx : xProd L.1 = h k * xProd K.1 := Finset.prod_insert hkK
      have hc : L.1.1.card * m = K.1.1.card * m + m := by
        show (insert k K.1.1).card * m = _
        rw [Finset.card_insert_of_notMem hkK]; ring
      rw [hx, hc] at h1
      have h2 := smul_mem_twist_of_inv (hwinv k) h1
      refine Submodule.subset_span ⟨m, ?_⟩
      have e : xProd K.1 ^ m • (w k * h k ^ m) • s L = w k • (h k * xProd K.1) ^ m • s L := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring
      rw [e]
      exact h2

end

end GroundTheory.Heights₂.Heights.Kleiman
