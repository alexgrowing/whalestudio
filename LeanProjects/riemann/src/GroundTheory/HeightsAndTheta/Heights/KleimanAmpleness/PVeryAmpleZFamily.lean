import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZFamilySt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace VeryAmpleZFamily

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ} {h : Fin (r + 1) → Ω}

theorem aeval_mem_pow {I : Chart x} {Q : Submodule (chartRing S x I) Ω} (hQ : ∀ l, h l ∈ Q)
    {f : MvPolynomial (Fin (r + 1)) S} {e : ℕ} (hf : f.IsHomogeneous e) : aeval h f ∈ Q ^ e := by
  have hmon : ∀ (d : Fin (r + 1) →₀ ℕ) (t : Finset (Fin (r + 1))),
      ∏ j ∈ t, h j ^ d j ∈ Q ^ (∑ j ∈ t, d j) := by
    intro d t
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, pow_add]
      exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hQ j) _) ih
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [aeval_monomial]
  have hdeg : ∑ j ∈ d.support, d j = e := by
    have := hf (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have hm := hmon d d.support
  rw [hdeg] at hm
  have := Submodule.smul_mem (Q ^ e)
    (⟨algebraMap S Ω (coeff d f), Subalgebra.algebraMap_mem _ _⟩ : chartRing S x I) hm
  rw [chartRing_smul_def] at this
  exact this

omit [Module S E] [IsScalarTower S Ω E] in

theorem smul_mem_twist_pow (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {z : E}
    {q : Ω} (hz : z ∈ (F.twist (H.pow c)).sub I) (hq : q ∈ (H.pow d).sub I) :
    q • z ∈ (F.twist (H.pow (c + d))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => q • z ∈ (F.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨p, hp, y, hy, rfl⟩
    exact Submodule.subset_span ⟨p * q, AmpleTwistLocal.mul_mem_pow H I hp d hq, y, hy, by
      rw [smul_smul, mul_comm]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    rw [Subalgebra.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ a hz

theorem mem_sub_of_mem_secs {H : SubSystem S x Ω} {z : Ω} (hz : z ∈ H.secs) (I : Chart x) : z ∈ H.sub I :=
  (Submodule.restrictScalars_mem S _ _).mp ((Submodule.mem_iInf _).mp hz I)

theorem prod_pow_mem (H : SubSystem S x Ω) (I : Chart x) (hh : ∀ l, h l ∈ H.sub I)
    (T : Finset (Fin (r + 1))) (n : ℕ) : (∏ l ∈ T, h l) ^ n ∈ (H.pow (T.card * n)).sub I := by
  refine AmpleTwistLocal.pow_mem_pow H I ?_ n
  rw [SubSystem.pow_sub, ← AmpleAffineGen.aeval_monoProd (S := S)]
  exact aeval_mem_pow hh (AmpleAffineGen.monoProd_isHomogeneous T)

theorem mem_secsOnZChart (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x)
    (hh : ∀ l, h l ∈ H.sub I) (J : Chart h) (e : E) :
    e ∈ secsOnZChart F H h I J ↔
      ∃ n : ℕ, xProd J ^ n • e ∈ (F.twist (H.pow (J.1.card * n))).sub I := by
  refine ⟨fun he => ?_, fun he => Submodule.subset_span he⟩
  refine Submodule.span_induction (p := fun e _ =>
    ∃ n : ℕ, xProd J ^ n • e ∈ (F.twist (H.pow (J.1.card * n))).sub I) (fun _ h => h) ?_ ?_ ?_ he
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro a b _ _ ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have e1 : xProd J ^ (n + m) • (a + b) =
        xProd J ^ m • (xProd J ^ n • a) + xProd J ^ n • (xProd J ^ m • b) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm m n]
    rw [e1]
    refine Submodule.add_mem _ ?_ ?_
    · have := smul_mem_twist_pow F H I hn (prod_pow_mem H I hh J.1 m)
      rwa [← Nat.mul_add] at this
    · have := smul_mem_twist_pow F H I hm (prod_pow_mem H I hh J.1 n)
      rwa [← Nat.mul_add, Nat.add_comm m n] at this
  · rintro c a _ ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have e1 : xProd J ^ n • c • a =
        (⟨algebraMap S Ω c, Subalgebra.algebraMap_mem _ _⟩ : chartRing S x I) • (xProd J ^ n • a) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul Ω c a, smul_smul, smul_smul, mul_comm]
    rw [e1]
    exact Submodule.smul_mem _ _ hn

theorem exists_mul_eq_monoProd_pow {T : Finset (Fin (r + 1))} {s : Poly S r} (hs : s ∈ monos T) :
    ∃ (k : ℕ) (t : Poly S r), t ∈ monos T ∧ s * t = AmpleAffineGen.monoProd T ^ k := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨1, AmpleAffineGen.monoProd (T.erase i),
      AmpleAffineGen.monoProd_mem_monos (Finset.erase_subset _ _), by
        rw [pow_one, AmpleAffineGen.monoProd, AmpleAffineGen.monoProd,
          Finset.mul_prod_erase _ _ (by exact_mod_cast hi)]⟩
  | one => exact ⟨0, 1, one_mem _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k, t, ht, e⟩ := ha
    obtain ⟨k', t', ht', e'⟩ := hb
    exact ⟨k + k', t * t', mul_mem ht ht', by
      rw [pow_add, ← e, ← e']; ring⟩

theorem exists_mul_xProd_pow_mem (H : SubSystem S x Ω) (I : Chart x) (hh : ∀ l, h l ∈ H.sub I)
    (J : Chart h) {a : Ω} (ha : a ∈ chartRing S h J) :
    ∃ k : ℕ, a * xProd J ^ k ∈ (H.pow (J.1.card * k)).sub I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  obtain ⟨k, t, ht, hst⟩ := exists_mul_eq_monoProd_pow hs
  obtain ⟨d, htd⟩ := monos_isHomogeneous ht
  have hval : aeval h s * aeval h t = xProd J ^ k := by
    rw [← map_mul, hst, map_pow, AmpleAffineGen.aeval_monoProd]; rfl
  have hne : AmpleAffineGen.monoProd (S := S) J.1 ^ k ≠ 0 := by
    intro h0
    have := congrArg (aeval h) h0
    rw [map_pow, AmpleAffineGen.aeval_monoProd, map_zero] at this
    exact pow_ne_zero _ (AmpleAffineGen.xProd_ne_zero J) this
  have hdeg : e + d = J.1.card * k := by
    have h1 := hse.mul htd
    rw [hst] at h1
    exact h1.inj_right ((AmpleAffineGen.monoProd_isHomogeneous J.1).pow k) hne
  refine ⟨k, ?_⟩
  have hs0 : aeval h s ≠ 0 := eval_ne_zero_of_mem_monos J hs
  have e1 : aeval h f / aeval h s * xProd J ^ k = aeval h (f * t) := by
    rw [← hval, map_mul]; field_simp
  rw [e1, SubSystem.pow_sub, ← hdeg]
  exact aeval_mem_pow hh (hf.mul htd)

theorem secsOnZChart_mono (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x)
    (hh : ∀ l, h l ∈ H.sub I) {J J' : Chart h} (hJ : J.1 ⊆ J'.1) {e : E}
    (he : e ∈ secsOnZChart F H h I J) : e ∈ secsOnZChart F H h I J' := by
  classical
  rw [mem_secsOnZChart F H I hh] at he ⊢
  obtain ⟨n, hn⟩ := he
  refine ⟨n, ?_⟩
  have e1 : xProd J' ^ n • e = (∏ l ∈ J'.1 \ J.1, h l) ^ n • (xProd J ^ n • e) := by
    rw [smul_smul, ← mul_pow]
    unfold xProd
    rw [Finset.prod_sdiff hJ]
  rw [e1]
  have := smul_mem_twist_pow F H I hn (prod_pow_mem H I hh (J'.1 \ J.1) n)
  rwa [← Nat.add_mul, Nat.add_comm, Finset.card_sdiff_add_card_eq_card hJ] at this

theorem proof : VeryAmpleZFamily.Statement := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hv
  have hh : ∀ I l, h l ∈ H.toSubSystem.sub I := fun I l => mem_sub_of_mem_secs (hv.mem_secs l) I
  have mem : ∀ (J : Chart h) (e : E), e ∈ secsOnZ F.toSubSystem H.toSubSystem h J ↔
      ∀ I, ∃ n : ℕ, xProd J ^ n • e ∈
        (F.toSubSystem.twist (H.toSubSystem.pow (J.1.card * n))).sub I := by
    intro J e
    rw [secsOnZ, Submodule.mem_iInf]
    exact forall_congr' fun I => mem_secsOnZChart F.toSubSystem H.toSubSystem I (hh I) J e
  have smul : ∀ (J : Chart h) (a : chartRing S h J) (e : E),
      e ∈ secsOnZ F.toSubSystem H.toSubSystem h J → (a : Ω) • e ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
    intro J a e he
    rw [mem] at he ⊢
    intro I
    obtain ⟨n, hn⟩ := he I
    obtain ⟨k, hk⟩ := exists_mul_xProd_pow_mem H.toSubSystem I (hh I) J a.2
    refine ⟨n + k, ?_⟩
    have e1 : xProd J ^ (n + k) • (a : Ω) • e = ((a : Ω) * xProd J ^ k) • (xProd J ^ n • e) := by
      rw [smul_smul, smul_smul]; ring_nf
    rw [e1, Nat.mul_add]
    exact smul_mem_twist_pow F.toSubSystem H.toSubSystem I hn hk
  have mono : ∀ J J' : Chart h, J.1 ⊆ J'.1 → ∀ e, e ∈ secsOnZ F.toSubSystem H.toSubSystem h J →
      e ∈ secsOnZ F.toSubSystem H.toSubSystem h J' := by
    intro J J' hJ e he
    rw [secsOnZ, Submodule.mem_iInf] at he ⊢
    exact fun I => secsOnZChart_mono F.toSubSystem H.toSubSystem I (hh I) hJ (he I)
  let sub : ∀ J : Chart h, Submodule (chartRing S h J) E := fun J =>
    { carrier := secsOnZ F.toSubSystem H.toSubSystem h J
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun a e he => smul J a e he }
  refine ⟨{ sub := sub, mono := fun J J' hJ e he => mono J J' hJ e he, mem_iff := ?_ }, fun J => ?_⟩
  · intro J J' hJ y
    constructor
    · intro hy
      change y ∈ secsOnZ F.toSubSystem H.toSubSystem h J' at hy
      rw [mem] at hy
      choose n hn using hy
      obtain ⟨M, hM⟩ := Finite.bddAbove_range n
      have hM' : ∀ I, n I ≤ M := fun I => hM ⟨I, rfl⟩
      refine ⟨⟨AmpleAffineGen.chartRatio J J' ^ M, pow_mem (AmpleAffineGen.chartRatio_mem J J') M⟩, ?_, ?_⟩
      · refine IsUnit.of_mul_eq_one
          ⟨AmpleAffineGen.chartRatio J' J ^ M, pow_mem (AmpleAffineGen.chartRatio_mem J' J) M⟩
          (Subtype.ext ?_)
        change AmpleAffineGen.chartRatio J J' ^ M * AmpleAffineGen.chartRatio J' J ^ M = 1
        rw [← mul_pow, AmpleAffineGen.chartRatio_mul_chartRatio, one_pow]
      · change AmpleAffineGen.chartRatio J J' ^ M • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J
        rw [mem]
        intro I
        refine ⟨J'.1.card * M, ?_⟩
        have hJpos : 0 < J.1.card := Finset.card_pos.mpr J.2.1
        have hnK : n I ≤ J.1.card * M := (hM' I).trans (Nat.le_mul_of_pos_left M hJpos)
        have e1 : xProd J ^ (J'.1.card * M) • (AmpleAffineGen.chartRatio J J' ^ M • y) =
            xProd J' ^ (J.1.card * M - n I) • (xProd J' ^ n I • y) := by
          rw [smul_smul, smul_smul, ← pow_add, Nat.sub_add_cancel hnK, AmpleAffineGen.chartRatio, div_pow,
            ← pow_mul, ← pow_mul, ← mul_div_assoc,
            mul_div_cancel_left₀ _ (pow_ne_zero _ (AmpleAffineGen.xProd_ne_zero J))]
        rw [e1]
        have := smul_mem_twist_pow F.toSubSystem H.toSubSystem I (hn I)
          (prod_pow_mem H.toSubSystem I (hh I) J'.1 (J.1.card * M - n I))
        have e2 : J'.1.card * n I + J'.1.card * (J.1.card * M - n I) = J.1.card * (J'.1.card * M) := by
          rw [← Nat.mul_add, Nat.add_sub_cancel' hnK]; ring
        rw [e2] at this
        exact this
    · rintro ⟨a, ha, hay⟩
      change y ∈ secsOnZ F.toSubSystem H.toSubSystem h J'
      have h1 : (a : Ω) • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J' := mono J J' hJ _ hay
      obtain ⟨u, hu⟩ := ha
      have h2 := smul J' (↑u⁻¹) _ h1
      have hinv : ((↑u⁻¹ : chartRing S h J') : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val u.inv_mul
        rw [hu] at this
        exact this
      rwa [smul_smul, hinv, one_smul] at h2
  · ext e
    exact Iff.rfl

end VeryAmpleZFamily

end

end GroundTheory.Heights₂.Heights.Kleiman
