import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AEConst
import Mathlib

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace PositivityTheory.KB.SpectralGap.UnfoldB

open PositivityTheory.KB.SpectralGap

def rep {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (B K : Subgroup Λ)
    (c : Quotient (QuotientGroup.rightRel (B.subgroupOf K))) : S :=
  j ((c.out : K) : Λ)

theorem card_quot {Λ : Type} [Group Λ] (B K : Subgroup Λ) :
    Nat.card (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) = (B.subgroupOf K).index := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (B.subgroupOf K))]
  rfl

theorem countable_map {Λ S : Type} [Group Λ] [Countable Λ] [Group S] (j : Λ →* S) (K : Subgroup Λ) :
    Countable (K.map j) := by
  have : ((K.map j : Subgroup S) : Set S).Countable := by
    rw [Subgroup.coe_map]
    exact (Set.to_countable _).image _
  exact this.to_subtype

theorem rep_ex {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (B K : Subgroup Λ) :
    ∀ g ∈ K.map j, ∃ h ∈ B.map j, ∃ c, g = h * rep j B K c := by
  rintro g ⟨k, hk, rfl⟩
  let c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)) := Quotient.mk _ ⟨k, hk⟩
  have hr : QuotientGroup.rightRel (B.subgroupOf K) c.out ⟨k, hk⟩ := Quotient.mk_out _
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at hr
  refine ⟨j (k * ((c.out : K) : Λ)⁻¹), ⟨_, ?_, rfl⟩, c, ?_⟩
  · simpa using hr
  · simp [rep]

theorem rep_inj {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (hj : Function.Injective j)
    (B K : Subgroup Λ) :
    ∀ h ∈ B.map j, ∀ h' ∈ B.map j, ∀ c c', h * rep j B K c = h' * rep j B K c' → c = c' := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩ c c' heq
  rw [rep, rep, ← map_mul, ← map_mul] at heq
  have e := hj heq
  rw [← Quotient.out_equiv_out]
  show QuotientGroup.rightRel (B.subgroupOf K) c.out c'.out
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  have key : ((c'.out : K) : Λ) * ((c.out : K) : Λ)⁻¹ = b'⁻¹ * b := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← e]
    group
  simpa [key] using B.mul_mem (B.inv_mem hb') hb

theorem unfold_fd (Λ S : Type) [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S]
    [MeasurableMul S] (μ : Measure S) [μ.IsMulLeftInvariant] (j : Λ →* S) (hj : Function.Injective j)
    (B K : Subgroup Λ) (hBK : B ≤ K) (hi : (B.subgroupOf K).index ≠ 0) :
    ∀ D : Set S, IsFundamentalDomain (K.map j) D μ →
    (∃ D' : Set S, IsFundamentalDomain (B.map j) D' μ) ∧
    ∀ D' : Set S, IsFundamentalDomain (B.map j) D' μ → μ D' = (B.subgroupOf K).index * μ D ∧
      ∀ u : S → ℝ, Measurable u → LInv j B u →
        (IntegrableOn u D' μ ↔ IntegrableOn (avg j B K fun y => |u y|) D μ) ∧
        (IntegrableOn u D' μ → IntegrableOn (avg j B K u) D μ ∧
          ∫ x in D', u x ∂μ = (B.subgroupOf K).index * ∫ x in D, avg j B K u x ∂μ) := by
  intro D hD
  haveI : Countable (K.map j) := countable_map j K
  haveI : Countable (B.map j) := countable_map j B
  haveI : Finite (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) :=
    Nat.finite_of_card_ne_zero (by rw [card_quot]; exact hi)
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  have hrepΓ : ∀ c, rep j B K c ∈ K.map j := fun c => ⟨((c.out : K) : Λ), c.out.2, rfl⟩
  have hBK' : B.map j ≤ K.map j := Subgroup.map_mono hBK
  have hn : ((B.subgroupOf K).index : ℝ) ≠ 0 := by exact_mod_cast hi
  have hcard : (Finset.univ : Finset (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))).card
      = (B.subgroupOf K).index := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_quot]
  have hmp : ∀ a : S, MeasurePreserving (fun x => a • x) μ μ := fun a => measurePreserving_smul a μ
  have hemb : ∀ a : S, MeasurableEmbedding (fun x : S => a • x) :=
    fun a => measurableEmbedding_const_smul a
  have havg : ∀ (f : S → ℝ) (x : S), avg j B K f x
      = ((B.subgroupOf K).index : ℝ)⁻¹ * ∑ c, f (rep j B K c * x) := by
    intro f x
    simp only [avg, finsum_eq_sum_of_fintype]
    rfl
  set D0 : Set S := ⋃ c, rep j B K c • D with hD0def
  have hmeasc : ∀ c, NullMeasurableSet (rep j B K c • D) μ := fun c =>
    hD.nullMeasurableSet_smul (⟨rep j B K c, hrepΓ c⟩ : K.map j)
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) fun c => rep j B K c • D) := by
    intro c c' hcc'
    have hne : (⟨rep j B K c, hrepΓ c⟩ : K.map j) ≠ ⟨rep j B K c', hrepΓ c'⟩ := by
      intro h
      apply hcc'
      have e := congrArg Subtype.val h
      exact rep_inj j hj B K 1 (one_mem _) 1 (one_mem _) c c' (by simpa using e)
    exact hD.aedisjoint hne
  have hD0 : IsFundamentalDomain (B.map j) D0 μ := by
    refine ⟨NullMeasurableSet.iUnion hmeasc, ?_, ?_⟩
    · filter_upwards [hD.ae_covers] with x hx
      obtain ⟨g, hg⟩ := hx
      obtain ⟨h, hh, c, hgc⟩ := rep_ex j B K ((g : S)⁻¹) (inv_mem g.2)
      refine ⟨⟨h⁻¹, inv_mem hh⟩, Set.mem_iUnion.2 ⟨c, ?_⟩⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      have e : (rep j B K c)⁻¹ * h⁻¹ = (g : S) := by
        rw [← mul_inv_rev, ← hgc, inv_inv]
      convert hg using 1
      show (rep j B K c)⁻¹ * (h⁻¹ * x) = (g : S) * x
      rw [← mul_assoc, e]
    · intro δ δ' hδ
      show AEDisjoint μ ((δ : S) • D0) ((δ' : S) • D0)
      rw [hD0def, Set.smul_set_iUnion, Set.smul_set_iUnion, AEDisjoint.iUnion_left_iff]
      intro c
      rw [AEDisjoint.iUnion_right_iff]
      intro c'
      rw [smul_smul, smul_smul]
      have h1 : (δ : S) * rep j B K c ∈ K.map j := mul_mem (hBK' δ.2) (hrepΓ c)
      have h2 : (δ' : S) * rep j B K c' ∈ K.map j := mul_mem (hBK' δ'.2) (hrepΓ c')
      have hne : (⟨_, h1⟩ : K.map j) ≠ ⟨_, h2⟩ := by
        intro h
        have e := congrArg Subtype.val h
        have hc := rep_inj j hj B K _ δ.2 _ δ'.2 c c' e
        subst hc
        exact hδ (Subtype.ext (mul_right_cancel e))
      exact hD.aedisjoint hne
  refine ⟨⟨D0, hD0⟩, fun D' hD' => ⟨?_, fun u hu hinv => ?_⟩⟩
  · rw [hD'.measure_eq hD0, ← setLIntegral_one, hD0def, lintegral_iUnion₀ hmeasc hdisj, tsum_fintype]
    simp only [setLIntegral_one]
    have hmc : ∀ c, μ (rep j B K c • D) = μ D := fun c => measure_smul μ (rep j B K c) D
    simp only [hmc, Finset.sum_const, hcard, nsmul_eq_mul]
  · have hinvΔ : ∀ (δ : B.map j) (x : S), u (δ • x) = u x := by
      rintro ⟨_, b, hb, rfl⟩ x
      exact hinv b hb x
    have hI : IntegrableOn u D' μ ↔ IntegrableOn u D0 μ := hD'.integrableOn_iff hD0 hinvΔ
    have hIc : IntegrableOn u D0 μ ↔ ∀ c, IntegrableOn (fun x => u (rep j B K c * x)) D μ := by
      rw [hD0def, integrableOn_finite_iUnion]
      exact forall_congr' fun c => (hmp _).integrableOn_image (hemb _)
    have hm : ∀ c, Measurable (fun x => u (rep j B K c * x)) := fun c =>
      hu.comp (measurable_const_mul _)
    have hAbs : IntegrableOn (avg j B K fun y => |u y|) D μ ↔
        ∀ c, IntegrableOn (fun x => u (rep j B K c * x)) D μ := by
      constructor
      · intro h c
        have h2 : IntegrableOn (fun x => ((B.subgroupOf K).index : ℝ) *
            avg j B K (fun y => |u y|) x) D μ := h.const_mul _
        refine Integrable.mono' h2 (hm c).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
        rw [havg, Real.norm_eq_abs, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
        exact Finset.single_le_sum (f := fun c => |u (rep j B K c * x)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ c)
      · intro h
        have e : (avg j B K fun y => |u y|)
            = fun x => ((B.subgroupOf K).index : ℝ)⁻¹ * ∑ c, |u (rep j B K c * x)| :=
          funext fun x => havg _ x
        rw [e]
        exact (integrable_finset_sum _ fun c _ => (h c).abs).const_mul _
    refine ⟨hI.trans (hIc.trans hAbs.symm), fun hint => ?_⟩
    have hcs := hIc.1 (hI.1 hint)
    have havgInt : IntegrableOn (avg j B K u) D μ := by
      have e : avg j B K u = fun x => ((B.subgroupOf K).index : ℝ)⁻¹ * ∑ c, u (rep j B K c * x) :=
        funext fun x => havg _ x
      rw [e]
      exact (integrable_finset_sum _ fun c _ => hcs c).const_mul _
    refine ⟨havgInt, ?_⟩
    have hint0 : IntegrableOn u (⋃ c, rep j B K c • D) μ := by
      rw [← hD0def]
      exact hI.1 hint
    rw [hD'.setIntegral_eq hD0 hinvΔ, hD0def, integral_iUnion_ae hmeasc hdisj hint0, tsum_fintype]
    have hterm : ∀ c, ∫ x in rep j B K c • D, u x ∂μ = ∫ x in D, u (rep j B K c * x) ∂μ :=
      fun c => (hmp _).setIntegral_image_emb (hemb _) u D
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← integral_finset_sum _ fun c _ => hcs c,
      ← integral_const_mul]
    congr 1
    ext x
    rw [havg, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

end PositivityTheory.KB.SpectralGap.UnfoldB

end
