import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PGapAvg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.MeasurableLift

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap.PGap

theorem idx_ne {Λ : Type} [Group Λ] {B E K : Subgroup Λ} (hBE : B ≤ E) (hEK : E ≤ K)
    (h : (B.subgroupOf K).index ≠ 0) : (B.subgroupOf E).index ≠ 0 ∧ (E.subgroupOf K).index ≠ 0 := by
  have h' : (B.subgroupOf E).index * (E.subgroupOf K).index = (B.subgroupOf K).index :=
    Subgroup.relIndex_mul_relIndex B E K hBE hEK
  rw [← h'] at h
  exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

theorem exists_not_mem {Λ : Type} [Group Λ] {B E : Subgroup Λ} (h : 25 ≤ (B.subgroupOf E).index) :
    ∃ g ∈ E, g ∉ B := by
  by_contra hc
  push_neg at hc
  have htop : B.subgroupOf E = ⊤ := Subgroup.subgroupOf_eq_top.mpr (fun g hg => hc g hg)
  rw [htop, Subgroup.index_top] at h
  omega

theorem twoTr_le {Λ : Type} [Group Λ] {E K G : Subgroup Λ} (htwo : TwoTr E K) (hEG : E ≤ G)
    {g : Λ} (hgK : g ∈ K) (hgE : g ∉ E) (hgG : g ∈ G) : K ≤ G := by
  intro g' hg'
  by_cases h : g' ∈ E
  · exact hEG h
  · obtain ⟨e, he, e', he', rfl⟩ := htwo g hgK hgE g' hg' h
    exact G.mul_mem (G.mul_mem (hEG he) hgG) (hEG he')

theorem t_trick {I X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : ∀ t : ℝ, 0 < t → |I| ≤ (t * X + Y / t) / 10) :
    |I| ≤ 1 / 5 * (Real.sqrt X * Real.sqrt Y) := by
  set s := Real.sqrt X with hs_def
  set r := Real.sqrt Y with hr_def
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hXs : X = s ^ 2 := (Real.sq_sqrt hX).symm
  have hYr : Y = r ^ 2 := (Real.sq_sqrt hY).symm
  have key : ∀ δ : ℝ, 0 < δ → 10 * |I| ≤ 2 * (s * r) + δ * (r + s) := by
    intro δ hδ
    have ha : 0 < r + δ := by linarith
    have hb : 0 < s + δ := by linarith
    have ht : 0 < (r + δ) / (s + δ) := div_pos ha hb
    have h1 := h _ ht
    have e1 : (r + δ) / (s + δ) * X ≤ (r + δ) * s := by
      rw [hXs, div_mul_eq_mul_div, div_le_iff₀ hb]
      nlinarith [mul_nonneg ha.le hs, mul_nonneg (mul_nonneg ha.le hs) hδ.le]
    have e2 : Y / ((r + δ) / (s + δ)) ≤ r * (s + δ) := by
      rw [hYr, div_div_eq_mul_div, div_le_iff₀ ha]
      nlinarith [mul_nonneg hb.le hr, mul_nonneg (mul_nonneg hb.le hr) hδ.le]
    nlinarith
  by_contra hc
  push_neg at hc
  set δ := (|I| - 1 / 5 * (s * r)) * 10 / (r + s + 1) with hδ_def
  have hpos : 0 < r + s + 1 := by linarith
  have hδ : 0 < δ := by
    apply div_pos _ hpos
    linarith
  have hδ' : δ * (r + s + 1) = (|I| - 1 / 5 * (s * r)) * 10 := by
    rw [hδ_def]
    field_simp
  nlinarith [key δ hδ]

section Unf

variable {Λ S : Type} [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S] [MeasurableMul S]
  (μ : Measure S) [μ.IsMulLeftInvariant] {j : Λ →* S}
  (hU : Unfold) (hj : Function.Injective j) {B K : Subgroup Λ} (hBK : B ≤ K)
  (hi : (B.subgroupOf K).index ≠ 0)

include μ hU hj hBK hi

theorem u_inv {u : S → ℝ} (hu : LInv j B u) : LInv j K (avg j B K u) :=
  (hU Λ S μ j hj B K hBK hi).1 u hu

theorem u_id {u : S → ℝ} (hu : LInv j K u) : avg j B K u = u :=
  (hU Λ S μ j hj B K hBK hi).2.1 u hu

theorem u_meas {u : S → ℝ} (hu : Measurable u) : Measurable (avg j B K u) :=
  (hU Λ S μ j hj B K hBK hi).2.2.1 u hu

theorem u_trans {E : Subgroup Λ} (hBE : B ≤ E) (hEK : E ≤ K) {u : S → ℝ} (hu : LInv j B u) :
    avg j E K (avg j B E u) = avg j B K u :=
  (hU Λ S μ j hj B K hBK hi).2.2.2.1 E hBE hEK u hu

theorem u_dom {D : Set S} (hD : IsFundamentalDomain (K.map j) D μ) :
    ∃ D' : Set S, IsFundamentalDomain (B.map j) D' μ :=
  ((hU Λ S μ j hj B K hBK hi).2.2.2.2 D hD).1

theorem u_measure {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) : μ D' = (B.subgroupOf K).index * μ D :=
  (((hU Λ S μ j hj B K hBK hi).2.2.2.2 D hD).2 D' hD').1

theorem u_int_iff {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u) :
    IntegrableOn u D' μ ↔ IntegrableOn (avg j B K fun y => |u y|) D μ :=
  ((((hU Λ S μ j hj B K hBK hi).2.2.2.2 D hD).2 D' hD').2 u hm hu).1

theorem u_int_eq {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u)
    (hint : IntegrableOn u D' μ) :
    ∫ x in D', u x ∂μ = (B.subgroupOf K).index * ∫ x in D, avg j B K u x ∂μ :=
  (((((hU Λ S μ j hj B K hBK hi).2.2.2.2 D hD).2 D' hD').2 u hm hu).2 hint).2

theorem u_int_avg {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u)
    (hint : IntegrableOn u D' μ) : IntegrableOn (avg j B K u) D μ :=
  (((((hU Λ S μ j hj B K hBK hi).2.2.2.2 D hD).2 D' hD').2 u hm hu).2 hint).1

theorem int_iff_inv {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) {u : S → ℝ} (hm : Measurable u) (hu : LInv j K u) :
    IntegrableOn u D' μ ↔ IntegrableOn u D μ := by
  have hB : LInv j B u := fun γ hγ x => hu γ (hBK hγ) x
  have habs : LInv j K (fun y => |u y|) := by
    intro γ hγ x
    simp only [hu γ hγ x]
  rw [u_int_iff μ hU hj hBK hi hD hD' hm hB, u_id μ hU hj hBK hi habs]
  unfold IntegrableOn
  simp_rw [← Real.norm_eq_abs]
  exact integrable_norm_iff hm.aestronglyMeasurable

theorem int_eq_inv {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) {u : S → ℝ} (hm : Measurable u) (hu : LInv j K u)
    (hint : IntegrableOn u D' μ) :
    ∫ x in D', u x ∂μ = (B.subgroupOf K).index * ∫ x in D, u x ∂μ := by
  have hB : LInv j B u := fun γ hγ x => hu γ (hBK hγ) x
  rw [u_int_eq μ hU hj hBK hi hD hD' hm hB hint, u_id μ hU hj hBK hi hu]

end Unf

section Sub

variable {Λ S : Type} [Group Λ] [Group S] [MeasurableSpace S] (j : Λ →* S) (B : Subgroup Λ)
  (μ : Measure S) (DB : Set S)

def R (E : Subgroup Λ) : Set (HL j B μ DB) :=
  {f | ∃ u, Good j B μ DB u ∧ Good j B μ DB (avg j B E u) ∧
    f = cls j B μ DB (fun x => u x - avg j B E u x)}

def W (E : Subgroup Λ) : Submodule ℝ (HL j B μ DB) := (Submodule.span ℝ (R j B μ DB E))ᗮ

theorem W_closed (E : Subgroup Λ) : IsClosed (W j B μ DB E : Set (HL j B μ DB)) :=
  Submodule.isClosed_orthogonal _

end Sub

theorem integrableOn_mul {S : Type} [MeasurableSpace S] {μ : Measure S} {D : Set S} {u v : S → ℝ}
    (hu : MemLp u 2 (μ.restrict D)) (hv : MemLp v 2 (μ.restrict D)) :
    IntegrableOn (fun x => u x * v x) D μ :=
  MemLp.integrable_mul (p := 2) (q := 2) hu hv

section W

variable {Λ S : Type} [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S] [MeasurableMul S]
  {μ : Measure S} [μ.IsMulLeftInvariant] {j : Λ →* S}
  (hU : Unfold) (hj : Function.Injective j) {B : Subgroup Λ} {DB : Set S}
  (hDB : IsFundamentalDomain (B.map j) DB μ)

include hU hj hDB

theorem good_avg {E : Subgroup Λ} (hBE : B ≤ E) (hi : (B.subgroupOf E).index ≠ 0) {DE : Set S}
    (hDE : IsFundamentalDomain (E.map j) DE μ) {u : S → ℝ} (hu : Good j B μ DB u) :
    Good j B μ DB (avg j B E u) := by
  obtain ⟨hm, hinv, hL⟩ := hu
  have hmA : Measurable (avg j B E u) := u_meas μ hU hj hBE hi hm
  have hEinv : LInv j E (avg j B E u) := u_inv μ hU hj hBE hi hinv
  have hBinv : LInv j B (avg j B E u) := fun γ hγ x => hEinv γ (hBE hγ) x
  refine ⟨hmA, hBinv, ?_⟩
  have hsq : IntegrableOn (fun y => u y ^ 2) DB μ := hL.integrable_sq
  have hsqinv : LInv j B (fun y => u y ^ 2) := by
    intro γ hγ x
    simp only [hinv γ hγ x]
  have hsqm : Measurable (fun y => u y ^ 2) := hm.pow_const 2
  have h1 : IntegrableOn (avg j B E fun y => |u y ^ 2|) DE μ :=
    (u_int_iff μ hU hj hBE hi hDE hDB hsqm hsqinv).1 hsq
  have habs : (fun y => |u y ^ 2|) = fun y => u y ^ 2 := funext fun y => abs_of_nonneg (sq_nonneg _)
  rw [habs] at h1
  have h2 : IntegrableOn (fun x => avg j B E u x ^ 2) DE μ := by
    refine Integrable.mono' h1 (hmA.pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact avg_sq_le j hi u x
  have hsqE : LInv j E (fun x => avg j B E u x ^ 2) := by
    intro γ hγ x
    simp only [hEinv γ hγ x]
  have h3 : IntegrableOn (fun x => avg j B E u x ^ 2) DB μ :=
    (int_iff_inv μ hU hj hBE hi hDE hDB (hmA.pow_const 2) hsqE).2 h2
  exact (memLp_two_iff_integrable_sq hmA.aestronglyMeasurable).2 h3

theorem ip_zero {E : Subgroup Λ} (hBE : B ≤ E) (hi : (B.subgroupOf E).index ≠ 0) {DE : Set S}
    (hDE : IsFundamentalDomain (E.map j) DE μ) {a r : S → ℝ} (ha : Good j B μ DB a) (haE : LInv j E a)
    (hr : Good j B μ DB r) (hr' : Good j B μ DB (avg j B E r)) :
    ∫ x in DB, a x * (r x - avg j B E r x) ∂μ = 0 := by
  obtain ⟨ham, hainv, haL⟩ := ha
  obtain ⟨hrm, hrinv, hrL⟩ := hr
  obtain ⟨hsm, hsinv, hsL⟩ := hr'
  have haB : LInv j B a := fun γ hγ x => haE γ (hBE hγ) x
  have hint1 : IntegrableOn (fun x => a x * r x) DB μ := integrableOn_mul haL hrL
  have hint2 : IntegrableOn (fun x => a x * avg j B E r x) DB μ := integrableOn_mul haL hsL
  have hsE : LInv j E (avg j B E r) := u_inv μ hU hj hBE hi hrinv
  have harB : LInv j B (fun x => a x * r x) := by
    intro γ hγ x
    simp only [haB γ hγ x, hrinv γ hγ x]
  have haE2 : LInv j E (fun x => a x * avg j B E r x) := by
    intro γ hγ x
    simp only [haE γ hγ x, hsE γ hγ x]
  have e1 : ∫ x in DB, a x * r x ∂μ =
      (B.subgroupOf E).index * ∫ x in DE, avg j B E (fun y => a y * r y) x ∂μ :=
    u_int_eq μ hU hj hBE hi hDE hDB (ham.mul hrm) harB hint1
  have e2 : ∫ x in DB, a x * avg j B E r x ∂μ =
      (B.subgroupOf E).index * ∫ x in DE, a x * avg j B E r x ∂μ :=
    int_eq_inv μ hU hj hBE hi hDE hDB (ham.mul hsm) haE2 hint2
  simp only [avg_mul_left j haE r] at e1
  simp_rw [mul_sub]
  rw [integral_sub hint1 hint2, e1, e2, sub_self]

theorem mem_W_of_inv {E : Subgroup Λ} (hBE : B ≤ E) (hi : (B.subgroupOf E).index ≠ 0) {DE : Set S}
    (hDE : IsFundamentalDomain (E.map j) DE μ) {u : S → ℝ} (hu : Good j B μ DB u) (huE : LInv j E u) :
    cls j B μ DB u ∈ W j B μ DB E := by
  unfold W
  rw [Submodule.mem_orthogonal]
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, hr', rfl⟩ := hx
    have hd : Good j B μ DB (fun x => r x - avg j B E r x) :=
      ⟨hr.1.sub hr'.1, fun γ hγ x => by simp only [hr.2.1 γ hγ x, hr'.2.1 γ hγ x], hr.2.2.sub hr'.2.2⟩
    rw [cls_inner hd hu]
    calc ∫ x in DB, (r x - avg j B E r x) * u x ∂μ = ∫ x in DB, u x * (r x - avg j B E r x) ∂μ := by
          congr 1
          funext x
          ring
      _ = 0 := ip_zero hU hj hDB hBE hi hDE hu huE hr hr'
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

theorem ae_eq_cosetAvg_of_mem_invariantSubspace {E : Subgroup Λ} (hBE : B ≤ E) (hi : (B.subgroupOf E).index ≠ 0) {DE : Set S}
    (hDE : IsFundamentalDomain (E.map j) DE μ) {u : S → ℝ} (hu : Good j B μ DB u)
    (hW : cls j B μ DB u ∈ W j B μ DB E) : u =ᵐ[μ.restrict DB] avg j B E u := by
  have hA : Good j B μ DB (avg j B E u) := good_avg hU hj hDB hBE hi hDE hu
  have hAE : LInv j E (avg j B E u) := u_inv μ hU hj hBE hi hu.2.1
  have hd : Good j B μ DB (fun x => u x - avg j B E u x) :=
    ⟨hu.1.sub hA.1, fun γ hγ x => by simp only [hu.2.1 γ hγ x, hA.2.1 γ hγ x], hu.2.2.sub hA.2.2⟩
  have hR : cls j B μ DB (fun x => u x - avg j B E u x) ∈ R j B μ DB E := ⟨u, hu, hA, rfl⟩
  have h1 : ⟪cls j B μ DB (fun x => u x - avg j B E u x), cls j B μ DB u⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).1 hW _ (Submodule.subset_span hR)
  have h2 : ⟪cls j B μ DB (fun x => u x - avg j B E u x), cls j B μ DB (avg j B E u)⟫_ℝ = 0 := by
    rw [cls_inner hd hA]
    calc ∫ x in DB, (u x - avg j B E u x) * avg j B E u x ∂μ =
          ∫ x in DB, avg j B E u x * (u x - avg j B E u x) ∂μ := by
          congr 1
          funext x
          ring
      _ = 0 := ip_zero hU hj hDB hBE hi hDE hA hAE hu hA
  have hdd : cls j B μ DB (fun x => u x - avg j B E u x) =
      cls j B μ DB u - cls j B μ DB (avg j B E u) := cls_sub hu hA
  have h3 : ⟪cls j B μ DB (fun x => u x - avg j B E u x),
      cls j B μ DB (fun x => u x - avg j B E u x)⟫_ℝ = 0 := by
    nth_rewrite 2 [hdd]
    rw [inner_sub_right, h1, h2, sub_self]
  rw [inner_self_eq_zero, hdd, sub_eq_zero] at h3
  exact (cls_eq_iff hu hA).1 h3

theorem W_anti {E K : Subgroup Λ} (hBE : B ≤ E) (hEK : E ≤ K) (hiK : (B.subgroupOf K).index ≠ 0)
    {DE DK : Set S} (hDE : IsFundamentalDomain (E.map j) DE μ)
    (hDK : IsFundamentalDomain (K.map j) DK μ) : W j B μ DB K ≤ W j B μ DB E := by
  have hiE : (B.subgroupOf E).index ≠ 0 := (idx_ne hBE hEK hiK).1
  have hBK : B ≤ K := hBE.trans hEK
  unfold W
  apply Submodule.orthogonal_le
  rw [Submodule.span_le]
  rintro f ⟨r, hr, hr', rfl⟩
  have hK1 : Good j B μ DB (avg j B K r) := good_avg hU hj hDB hBK hiK hDK hr
  have hK2 : Good j B μ DB (avg j B K (avg j B E r)) := good_avg hU hj hDB hBK hiK hDK hr'
  have htow : avg j B K (avg j B E r) = avg j B K r := by
    rw [← u_trans μ hU hj hBK hiK hBE hEK hr'.2.1,
      u_id μ hU hj hBE hiE (u_inv μ hU hj hBE hiE hr.2.1),
      u_trans μ hU hj hBK hiK hBE hEK hr.2.1]
  have hd1 : Good j B μ DB (fun x => r x - avg j B K r x) :=
    ⟨hr.1.sub hK1.1, fun γ hγ x => by simp only [hr.2.1 γ hγ x, hK1.2.1 γ hγ x], hr.2.2.sub hK1.2.2⟩
  have hd2 : Good j B μ DB (fun x => avg j B E r x - avg j B K (avg j B E r) x) :=
    ⟨hr'.1.sub hK2.1, fun γ hγ x => by simp only [hr'.2.1 γ hγ x, hK2.2.1 γ hγ x], hr'.2.2.sub hK2.2.2⟩
  have heq : cls j B μ DB (fun x => r x - avg j B E r x) =
      cls j B μ DB (fun x => r x - avg j B K r x) -
        cls j B μ DB (fun x => avg j B E r x - avg j B K (avg j B E r) x) := by
    rw [← cls_sub hd1 hd2]
    congr 1
    funext x
    rw [htow]
    ring
  show _ ∈ Submodule.span ℝ (R j B μ DB K)
  rw [heq]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨r, hr, hK1, rfl⟩)
    (Submodule.subset_span ⟨avg j B E r, hr', hK2, rfl⟩)

end W

end PositivityTheory.KB.SpectralGap.PGap

end
