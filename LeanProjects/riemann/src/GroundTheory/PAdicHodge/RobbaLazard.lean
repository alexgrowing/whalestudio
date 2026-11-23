import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.RobbaBounded
import GroundTheory.PAdicHodge.RobbaNewton
import GroundTheory.PAdicHodge.RobbaClosed
import GroundTheory.PAdicHodge.RobbaDivision
import GroundTheory.PAdicHodge.RobbaUnitApprox
import GroundTheory.PAdicHodge.RobbaMittagLeffler
import GroundTheory.PAdicHodge.RobbaPreparation
import GroundTheory.PAdicHodge.RobbaAnnulusBezout
import GroundTheory.PAdicHodge.RobbaDivisor
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent Polynomial

set_option linter.unusedSectionVars false

theorem exists_next_radius {q : ℝ} (hq : 0 < q) (hq1 : q < 1) {a b ε : ℝ} (ha : 0 < a)
    (ha1 : a < 1) (hb1 : b < 1) (hε : 0 < ε) :
    ∃ s : ℝ, ∃ n : ℕ, max a b ≤ s ∧ s < 1 ∧ q ≤ s ^ n ∧ (a / s) ^ n ≤ ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hq) ha1
  have hlim : Tendsto (fun s : ℝ => s ^ n) (𝓝[<] 1) (𝓝 1) := by
    simpa using ((continuous_pow n).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hmax : max a b < 1 := max_lt ha1 hb1
  have hI : ∀ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Set.Ioo (max a b) 1 := Ioo_mem_nhdsLT hmax
  obtain ⟨s, hs1, hs2⟩ := (hI.and (hlim.eventually (lt_mem_nhds hq1))).exists
  have hs0 : 0 < s := ha.trans_le ((le_max_left _ _).trans hs1.1.le)
  refine ⟨s, n, hs1.1.le, hs1.2, hs2.le, ?_⟩
  rw [div_pow, div_le_iff₀ (pow_pos hs0 n)]
  calc a ^ n ≤ ε * q := hn.le
    _ ≤ ε * s ^ n := mul_le_mul_of_nonneg_left hs2.le hε.le

theorem exists_radii {q : ℝ} (hq : 0 < q) (hq1 : q < 1) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ (t : ℕ → ℝ) (n₀ : ℕ → ℕ), t 0 = r ∧ Monotone t ∧ (∀ k, 0 < t k ∧ t k < 1) ∧
      (∀ ρ < 1, ∃ k, ρ ≤ t k) ∧ (∀ k, q ≤ t (k + 1) ^ n₀ k) ∧
      ∀ k, (t k / t (k + 1)) ^ n₀ k ≤ (1 / 2) ^ (k + 1) := by
  have next : ∀ (k : ℕ) (x : {x : ℝ // 0 < x ∧ x < 1}), ∃ y : {x : ℝ // 0 < x ∧ x < 1},
      ∃ n : ℕ, max x.1 (1 - 1 / ((k : ℝ) + 2)) ≤ y.1 ∧ q ≤ y.1 ^ n ∧
        (x.1 / y.1) ^ n ≤ (1 / 2) ^ (k + 1) := by
    intro k x
    have hb : 1 - 1 / ((k : ℝ) + 2) < 1 := by
      have : 0 < 1 / ((k : ℝ) + 2) := by positivity
      linarith
    obtain ⟨s, n, h1, h2, h3, h4⟩ := exists_next_radius hq hq1 x.2.1 x.2.2 hb
      (by positivity : (0 : ℝ) < (1 / 2) ^ (k + 1))
    exact ⟨⟨s, x.2.1.trans_le ((le_max_left _ _).trans h1), h2⟩, n, h1, h3, h4⟩
  choose y n hy using next
  let T : ℕ → {x : ℝ // 0 < x ∧ x < 1} := fun k => Nat.rec ⟨r, hr, hr1⟩ (fun k x => y k x) k
  have hT : ∀ k, T (k + 1) = y k (T k) := fun k => rfl
  refine ⟨fun k => (T k).1, fun k => n k (T k), rfl, ?_, fun k => (T k).2, ?_, fun k => ?_,
    fun k => ?_⟩
  · refine monotone_nat_of_le_succ fun k => ?_
    rw [hT]; exact (le_max_left _ _).trans (hy k (T k)).1
  · intro ρ hρ
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - ρ))
    refine ⟨k + 1, ?_⟩
    have h1 := (le_max_right _ _).trans (hy k (T k)).1
    rw [← hT] at h1
    have hpos : 0 < 1 - ρ := by linarith
    have : 1 / ((k : ℝ) + 2) < 1 - ρ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hk
      nlinarith
    linarith
  · show q ≤ (T (k + 1)).1 ^ n k (T k)
    rw [hT]; exact (hy k (T k)).2.1
  · show ((T k).1 / (T (k + 1)).1) ^ n k (T k) ≤ _
    rw [hT]; exact (hy k (T k)).2.2

namespace AnnulusRing

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem convergesAt_polySeq (p : K[X]) (ρ : ℝ) : ConvergesAt (polySeq p) ρ := by
  refine convergesAt_of_support (A := 0) (B := p.natDegree) (fun n hn => ?_) ρ
  simp only [polySeq]
  rcases hn with hn | hn
  · rw [if_neg (by omega)]
  · rw [if_pos (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem polySeq_ne_zero {p : K[X]} (hp : p ≠ 0) : polySeq p ≠ 0 := by
  intro h
  apply hp
  ext i
  have := congrFun h (i : ℤ)
  simpa [polySeq] using this

theorem restrict_aeval_T {I J : Set ℝ} [Fact (∃ ρ ∈ I, 0 < ρ)] [Fact (∃ ρ ∈ J, 0 < ρ)]
    (hJ : J ⊆ I) (p : K[X]) :
    restrict hJ (aeval (T : AnnulusRing K I) p) = aeval (T : AnnulusRing K J) p := by
  rw [← Polynomial.aeval_algHom_apply]; rfl

end AnnulusRing

namespace AnnulusRing

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

set_option maxHeartbeats 2000000 in

theorem span_pair_isPrincipal_Ico [IsDiscreteValuationRing (normInteger K)]
    (hloc : ∀ (α β : ℝ) [Fact (∃ ρ ∈ Set.Icc α β, 0 < ρ)], 0 < α → α ≤ β →
      ∀ f g : AnnulusRing K (Set.Icc α β), ∃ p : K[X],
        Ideal.span ({f, g} : Set (AnnulusRing K (Set.Icc α β))) = Ideal.span {aeval T p})
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) [Fact (∃ ρ ∈ Set.Ico r 1, 0 < ρ)]
    (f g : AnnulusRing K (Set.Ico r 1)) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ D : AnnulusRing K (Set.Ico r 1),
      Ideal.span ({f, g} : Set (AnnulusRing K (Set.Ico r 1))) = Ideal.span {D} := by
  obtain ⟨q, hq, hq1, hbig⟩ := exists_q_of_isDiscreteValuationRing (K := K)
  obtain ⟨t, n₀, ht0, hmono, ht01, htlim, hn₀, hβ⟩ := exists_radii hq hq1 hr hr1
  have hrt : ∀ k, r ≤ t k := fun k => ht0 ▸ hmono (Nat.zero_le k)
  have ht1 : ∀ k, t k < 1 := fun k => (ht01 k).2
  haveI hinst : ∀ k, Fact (∃ ρ ∈ Set.Icc r (t (k + 1)), 0 < ρ) := fun k =>
    ⟨⟨r, ⟨le_rfl, hrt _⟩, hr⟩⟩
  have hsub : ∀ k, Set.Icc r (t (k + 1)) ⊆ Set.Ico r 1 := fun k ρ hρ =>
    ⟨hρ.1, hρ.2.trans_lt (ht1 _)⟩

  have hgen := fun k => hloc r (t (k + 1)) hr (hrt _) (restrict (hsub k) f) (restrict (hsub k) g)
  choose p hp using hgen
  have hf0 : f.coeff ≠ 0 := fun e => hf (AnnulusRing.ext e)
  have hg0 : g.coeff ≠ 0 := fun e => hg (AnnulusRing.ext e)
  have hp0 : ∀ k, p k ≠ 0 := by
    intro k hpk
    have h1 : restrict (hsub k) f ∈ Ideal.span ({restrict (hsub k) f, restrict (hsub k) g} :
        Set (AnnulusRing K (Set.Icc r (t (k + 1))))) := Ideal.subset_span (by simp)
    rw [hp k, hpk, map_zero, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at h1
    exact hf0 (congrArg AnnulusRing.coeff h1)

  have hv : ∀ k, ∃ v, IsUnitOn v r (t (k + 1)) ∧ cmul (polySeq (p k)) v = polySeq (p (k + 1)) := by
    intro k
    have hJ : Set.Icc r (t (k + 1)) ⊆ Set.Icc r (t (k + 1 + 1)) :=
      Set.Icc_subset_Icc le_rfl (hmono (Nat.le_succ _))
    have e1 := hp (k + 1)
    have e2 := congrArg (Ideal.map (restrict hJ)) e1
    rw [Ideal.map_span, Ideal.map_span, Set.image_pair, Set.image_singleton,
      restrict_aeval_T] at e2
    have e3 : restrict hJ (restrict (hsub (k + 1)) f) = restrict (hsub k) f := rfl
    have e4 : restrict hJ (restrict (hsub (k + 1)) g) = restrict (hsub k) g := rfl
    rw [e3, e4, hp k, Ideal.span_singleton_eq_span_singleton] at e2
    obtain ⟨u, hu⟩ := e2
    refine ⟨(u : AnnulusRing K (Set.Icc r (t (k + 1)))).coeff, ⟨fun ρ hρ =>
      (u : AnnulusRing K _).convergesAt hρ (hr.trans_le hρ.1), fun h0 => ?_,
      lowIndex_eq_highIndex_of_isUnit hr u.isUnit⟩, ?_⟩
    · exact u.ne_zero (AnnulusRing.ext h0)
    · have := congrArg AnnulusRing.coeff hu
      rw [coeff_mul, coeff_aeval_alt, coeff_aeval_alt] at this
      exact this
  obtain ⟨D, hDc, hDu⟩ := exists_divisor hr ht0 hmono ht1 htlim hq hbig hn₀ hβ
    (fun k ρ _ => convergesAt_polySeq (p k) ρ) (fun k => polySeq_ne_zero (hp0 k)) hv
  let eD : AnnulusRing K (Set.Ico r 1) := ⟨D, fun ρ hρ _ => hDc ρ hρ.1 hρ.2⟩
  have hD0 : D ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hDu'⟩ := hDu 0
    exact cmul_ne_zero hr (convergesAt_polySeq _ r) (hu.1 r ⟨le_rfl, hrt _⟩)
      (polySeq_ne_zero (hp0 0)) hu.2.1 (hDu'.symm.trans h0)

  have hunit : ∀ m, ∃ w : AnnulusRing K (Set.Icc r (t (m + 1))), IsUnit w ∧
      restrict (hsub m) eD = aeval T (p m) * w := by
    intro m
    obtain ⟨u, hu, hDu'⟩ := hDu m
    refine ⟨⟨u, fun ρ hρ _ => hu.1 ρ hρ⟩, isUnit_of_lowIndex_eq_highIndex hr _
      (fun h0 => hu.2.1 (congrArg AnnulusRing.coeff h0)) hu.2.2, ?_⟩
    ext n
    rw [coeff_mul, coeff_aeval_alt]
    exact congrFun hDu' n

  have hdiv : ∀ x : AnnulusRing K (Set.Ico r 1),
      (∀ m, restrict (hsub m) x ∈ Ideal.span ({aeval T (p m)} :
        Set (AnnulusRing K (Set.Icc r (t (m + 1)))))) →
      ∃ y : AnnulusRing K (Set.Ico r 1), x = eD * y := by
    intro x hx
    have loc : ∀ m, ∃ h : ℤ → K, (∀ ρ ∈ Set.Icc r (t (m + 1)), ConvergesAt h ρ) ∧
        cmul D h = x.coeff := by
      intro m
      obtain ⟨w, hw, hwD⟩ := hunit m
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (hx m)
      obtain ⟨wi, hwi⟩ := hw.exists_right_inv
      refine ⟨(wi * z).coeff, fun ρ hρ => (wi * z).convergesAt hρ (hr.trans_le hρ.1), ?_⟩
      have : restrict (hsub m) eD * (wi * z) = restrict (hsub m) x := by
        rw [hwD, ← hz]; linear_combination (aeval T (p m) * z) * hwi
      exact congrArg AnnulusRing.coeff this
    choose h hh hhD using loc
    have hall : ∀ m, h m = h 0 := by
      intro m
      have hc : ∀ ρ ∈ Set.Icc r (t 1), ConvergesAt (h m) ρ := fun ρ hρ =>
        hh m ρ ⟨hρ.1, hρ.2.trans (hmono (by omega))⟩
      by_contra hne
      have hsub0 : h m - h 0 ≠ 0 := sub_ne_zero.2 hne
      have hzero : cmul D (h m - h 0) = 0 := by
        haveI : Fact (∃ ρ ∈ Set.Icc r (t 1), 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrt _⟩, hr⟩⟩
        have e := cmul_add hr (hDc r le_rfl hr1) (hc r ⟨le_rfl, hrt _⟩)
          ((hh 0 r ⟨le_rfl, hrt _⟩).neg)
        rw [← sub_eq_add_neg, cmul_neg, hhD m, hhD 0, ← sub_eq_add_neg, sub_self] at e
        exact e
      exact cmul_ne_zero hr (hDc r le_rfl hr1) ((hc r ⟨le_rfl, hrt _⟩).sub hr
        (hh 0 r ⟨le_rfl, hrt _⟩)) hD0 hsub0 hzero
    refine ⟨⟨h 0, fun ρ hρ hρ0 => ?_⟩, AnnulusRing.ext ?_⟩
    · obtain ⟨k, hk⟩ := htlim ρ hρ.2
      rw [← hall k]
      exact hh k ρ ⟨hρ.1, hk.trans (hmono (Nat.le_succ k))⟩
    · exact (hhD 0).symm
  have memf : ∀ m, restrict (hsub m) f ∈ Ideal.span ({aeval T (p m)} :
      Set (AnnulusRing K (Set.Icc r (t (m + 1))))) := fun m => by
    rw [← hp m]; exact Ideal.subset_span (by simp)
  have memg : ∀ m, restrict (hsub m) g ∈ Ideal.span ({aeval T (p m)} :
      Set (AnnulusRing K (Set.Icc r (t (m + 1))))) := fun m => by
    rw [← hp m]; exact Ideal.subset_span (by simp)
  obtain ⟨f', hf'⟩ := hdiv f memf
  obtain ⟨g', hg'⟩ := hdiv g memg

  have hloc' : ∀ k, ∃ a b : ℤ → K, (∀ ρ, r ≤ ρ → ρ ≤ t (k + 1) → ConvergesAt a ρ ∧
      ConvergesAt b ρ) ∧ cmul a f'.coeff + cmul b g'.coeff = Pi.single 0 1 := by
    intro k
    have hmem : aeval T (p k) ∈ Ideal.span ({restrict (hsub k) f, restrict (hsub k) g} :
        Set (AnnulusRing K (Set.Icc r (t (k + 1))))) := by
      rw [hp k]; exact Ideal.subset_span rfl
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 hmem
    obtain ⟨w, hw, hwD⟩ := hunit k
    have hDne : restrict (hsub k) eD ≠ 0 := fun h0 => hD0 (congrArg AnnulusRing.coeff h0)
    have key : restrict (hsub k) eD * (w * α * restrict (hsub k) f' +
        w * β * restrict (hsub k) g' - 1) = 0 := by
      have e1 : restrict (hsub k) f = restrict (hsub k) eD * restrict (hsub k) f' := by
        rw [hf', map_mul]
      have e2 : restrict (hsub k) g = restrict (hsub k) eD * restrict (hsub k) g' := by
        rw [hg', map_mul]
      rw [e1, e2] at hαβ
      linear_combination w * hαβ - hwD
    rcases mul_eq_zero.1 key with h0 | h0
    · exact absurd h0 hDne
    refine ⟨(w * α).coeff, (w * β).coeff, fun ρ h1 h2 => ⟨(w * α).convergesAt ⟨h1, h2⟩
      (hr.trans_le h1), (w * β).convergesAt ⟨h1, h2⟩ (hr.trans_le h1)⟩, ?_⟩
    have := congrArg AnnulusRing.coeff (sub_eq_zero.1 h0)
    rw [coeff_add, coeff_mul, coeff_mul] at this
    exact this
  obtain ⟨a, b, hab, hid⟩ := mittag_leffler (s := fun k => t (k + 1)) hr (hrt 1)
    (fun i j hij => hmono (Nat.add_le_add_right hij 1))
    (fun k => ht1 _) (fun ρ hρ => let ⟨k, hk⟩ := htlim ρ hρ; ⟨k, hk.trans (hmono (Nat.le_succ k))⟩)
    (fun ρ h1 h2 => f'.convergesAt ⟨h1, h2⟩ (hr.trans_le h1))
    (fun ρ h1 h2 => g'.convergesAt ⟨h1, h2⟩ (hr.trans_le h1)) hloc'
  let ea : AnnulusRing K (Set.Ico r 1) := ⟨a, fun ρ hρ _ => (hab ρ hρ.1 hρ.2).1⟩
  let eb : AnnulusRing K (Set.Ico r 1) := ⟨b, fun ρ hρ _ => (hab ρ hρ.1 hρ.2).2⟩
  have hone : ea * f' + eb * g' = 1 := AnnulusRing.ext hid
  refine ⟨eD, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.mem_span_singleton'.2 ⟨f', by rw [hf', mul_comm]⟩
    · exact Ideal.mem_span_singleton'.2 ⟨g', by rw [hg', mul_comm]⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    refine Ideal.mem_span_pair.2 ⟨ea, eb, ?_⟩
    rw [hf', hg']
    linear_combination eD * hone

end AnnulusRing

namespace AnnulusRing

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem isBezout_halfOpen [IsDiscreteValuationRing (normInteger K)] {r : ℝ} [Fact (r < 1)]
    (hr : 0 < r) : IsBezout (AnnulusRing.halfOpen K r) := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro f g
  by_cases hf : f = 0
  · subst hf
    rw [show ({0, g} : Set (AnnulusRing.halfOpen K r)) = insert 0 {g} from rfl,
      Ideal.span_insert_zero]
    exact ⟨g, rfl⟩
  by_cases hg : g = 0
  · subst hg
    rw [Set.pair_comm, show ({0, f} : Set (AnnulusRing.halfOpen K r)) = insert 0 {f} from rfl,
      Ideal.span_insert_zero]
    exact ⟨f, rfl⟩
  obtain ⟨D, hD⟩ := span_pair_isPrincipal_Ico
    (fun α β _ hα _ f g => exists_span_eq_aeval hα f g) hr Fact.out f g hf hg
  exact ⟨D, hD⟩

end AnnulusRing

namespace Robba

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

instance isBezout [IsDiscreteValuationRing (normInteger K)] : IsBezout (Robba K) := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro f g
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f g
  haveI : Fact (r < 1) := ⟨hr1⟩
  let f₀ : AnnulusRing.halfOpen K r := ⟨f.coeff, fun ρ hρ _ => (hc ρ hρ.1 hρ.2).1⟩
  let g₀ : AnnulusRing.halfOpen K r := ⟨g.coeff, fun ρ hρ _ => (hc ρ hρ.1 hρ.2).2⟩
  obtain ⟨D, hD⟩ := (IsBezout.iff_span_pair_isPrincipal.1
    (AnnulusRing.isBezout_halfOpen (K := K) hr0)) f₀ g₀
  refine ⟨AnnulusRing.toRobba D, ?_⟩
  have e := congrArg (Ideal.map (AnnulusRing.toRobba : AnnulusRing.halfOpen K r →ₐ[K] Robba K)) hD
  rw [Ideal.map_span, Ideal.map_span, Set.image_pair, Set.image_singleton] at e
  have ef : AnnulusRing.toRobba f₀ = f := rfl
  have eg : AnnulusRing.toRobba g₀ = g := rfl
  rw [ef, eg] at e
  exact e

end Robba

end GroundTheory.PAdicHodge
