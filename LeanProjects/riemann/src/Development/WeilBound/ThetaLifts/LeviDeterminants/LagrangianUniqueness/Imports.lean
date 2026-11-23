import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

open GlobalTheory.WeilM Filter Topology
open scoped Classical

noncomputable section

namespace PositivityTheory.ThKF0.FinLine

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]

def ind (U : OpenAddSubgroup G) (a : G) : G → ℂ := fun x => if x - a ∈ U then 1 else 0

theorem ind_mem {U₀ U : OpenAddSubgroup G} (h₀ : IsCompact (U₀ : Set G)) (hU : U ≤ U₀) (a : G) : ind U a ∈ SB G := by
  have hc : IsClopen ((fun x => x - a) ⁻¹' (U : Set G)) := U.isClopen.preimage (continuous_sub_right a)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_, ?_⟩
  · by_cases hx : x - a ∈ U
    · filter_upwards [hc.isOpen.mem_nhds hx] with z hz
      exact (if_pos hz).trans (if_pos hx).symm
    · filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with z hz
      exact (if_neg hz).trans (if_neg hx).symm
  · refine HasCompactSupport.intro (h₀.image (continuous_add_right a)) fun y hy => if_neg fun h => hy ?_
    exact ⟨y - a, hU h, sub_add_cancel y a⟩

theorem uniform {φ : G → ℂ} (hφ : φ ∈ SB G) : ∃ U : OpenAddSubgroup G, ∀ u ∈ U, ∀ x, φ (x + u) = φ x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : G), ∀ z ∈ tsupport φ, φ (z + t) = φ z := by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : G × G => (φ (q.2 + q.1), φ q.2) :=
      (hφ.1.comp_continuous (by fun_prop)).prodMk (hφ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h1
  refine ⟨U, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport φ
  · exact hU hu z hz
  by_cases hz' : z + u ∈ tsupport φ
  · have := hU (U.neg_mem hu) _ hz'
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

theorem decomp {φ : G → ℂ} (hφ : φ ∈ SB G) (U : OpenAddSubgroup G) (hU : ∀ u ∈ U, ∀ x, φ (x + u) = φ x) :
    ∃ t : Finset (G ⧸ U.toAddSubgroup), (∀ q, q ∈ t ↔ φ q.out ≠ 0) ∧ φ = ∑ q ∈ t, φ q.out • ind U q.out := by
  have := QuotientAddGroup.discreteTopology (N := U.toAddSubgroup) U.isOpen
  have hfin : ((QuotientAddGroup.mk : G → G ⧸ U.toAddSubgroup) '' tsupport φ).Finite :=
    (IsCompact.image hφ.2 QuotientAddGroup.continuous_mk).finite_of_discrete
  have hf : {q : G ⧸ U.toAddSubgroup | φ q.out ≠ 0}.Finite :=
    hfin.subset fun q hq => ⟨q.out, subset_tsupport _ hq, QuotientAddGroup.out_eq' q⟩
  refine ⟨hf.toFinset, fun q => hf.mem_toFinset, funext fun y => ?_⟩
  have hind : ∀ q : G ⧸ U.toAddSubgroup, ind U q.out y = if (y : G ⧸ U.toAddSubgroup) = q then 1 else 0 := by
    intro q
    have : (y : G ⧸ U.toAddSubgroup) = q ↔ y - q.out ∈ U := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      exact QuotientAddGroup.eq_iff_sub_mem
    simp only [ind, this]
  have h2 : -y + (y : G ⧸ U.toAddSubgroup).out ∈ U := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
  have h3 := hU _ h2 y
  rw [add_neg_cancel_left] at h3
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  split_ifs with h
  · exact h3.symm
  · rw [← h3]
    by_contra hne
    exact h (hf.mem_toFinset.2 hne)

variable {U₀ : OpenAddSubgroup G} (h₀ : IsCompact (U₀ : Set G)) {P : Set G} {l : (G → ℂ) →ₗ[ℂ] ℂ}

include h₀ in
theorem off (h2 : ∀ a ∉ P, ∃ χ : G → ℂ, IsLocallyConstant χ ∧ χ a ≠ 1 ∧ ∀ φ ∈ SB G, l (fun x => χ x * φ x) = l φ)
    {φ : G → ℂ} (hφ : φ ∈ SB G) (hP : ∀ a, φ a ≠ 0 → a ∉ P) : l φ = 0 := by
  choose! χ hχ hne hl using h2
  have hV : ∀ a, ∃ V : OpenAddSubgroup G, a ∉ P → ∀ u ∈ V, χ a (a + u) = χ a a := by
    intro a
    by_cases ha : a ∈ P
    · exact ⟨⊤, fun h => absurd ha h⟩
    have : ∀ᶠ u in 𝓝 (0 : G), χ a (a + u) = χ a a := by
      simpa using (((hχ a ha).comp_continuous (continuous_add_left a)).eventually_eq 0)
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ this
    exact ⟨V, fun _ u hu => hV hu⟩
  choose V hV using hV
  have hcl : IsClosed (Function.support φ) := (hφ.1.isClopen_fiber 0).compl.isClosed
  have hK : IsCompact (Function.support φ) := IsCompact.of_isClosed_subset hφ.2 hcl (subset_tsupport _)
  obtain ⟨s, hs, hcov⟩ := hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (V a : Set G))
    (fun a _ => (continuous_sub_right a).continuousAt.preimage_mem_nhds (by
      show (V a : Set G) ∈ 𝓝 (a - a); rw [sub_self]; exact (V a).mem_nhds_zero))
  obtain ⟨U₁, hU₁⟩ := uniform hφ
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean ((U₀ : Set G) ∩ U₁ ∩ ⋂ a ∈ s, (V a : Set G))
    (inter_mem (inter_mem U₀.mem_nhds_zero U₁.mem_nhds_zero) ((biInter_finset_mem s).2 fun a _ => (V a).mem_nhds_zero))
  obtain ⟨t, ht, e⟩ := decomp hφ U fun u hu => hU₁ u (hU hu).1.2
  rw [e, map_sum]
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨a, ha, hqa⟩ := Set.mem_iUnion₂.mp (hcov ((ht q).1 hq))
  have haP : a ∉ P := hP a (hs a ha)
  have h3 := hl a haP _ (ind_mem h₀ (fun u hu => (hU hu).1.1) q.out)
  have h4 : (fun x => χ a x * ind U q.out x) = χ a a • ind U q.out := by
    funext x
    simp only [ind, Pi.smul_apply, smul_eq_mul]
    split_ifs with hx
    · have := hV a haP _ ((V a).add_mem (Set.mem_iInter₂.1 (hU hx).2 a ha) hqa)
      rw [← this]; congr 2; beta_reduce; abel
    · simp
  rw [h4, map_smul, smul_eq_mul] at h3
  rw [map_smul, (mul_left_eq_self₀.1 h3).resolve_left (hne a haP), smul_zero]

include h₀ in

theorem test (hP0 : (0 : G) ∈ P) (h1 : ∀ p ∈ P, ∀ φ ∈ SB G, l (fun x => φ (x + p)) = l φ)
    (h2 : ∀ a ∉ P, ∃ χ : G → ℂ, IsLocallyConstant χ ∧ χ a ≠ 1 ∧ ∀ φ ∈ SB G, l (fun x => χ x * φ x) = l φ)
    (h0 : l (ind U₀ 0) = 0) {φ : G → ℂ} (hφ : φ ∈ SB G) : l φ = 0 := by
  have key : ∀ U ≤ U₀, ∀ a, l (ind U a) = if ∃ p ∈ P, p - a ∈ U then l (ind U 0) else 0 := by
    intro U hU a
    split_ifs with h
    · obtain ⟨p, hp, hpa⟩ := h
      rw [← h1 p hp _ (ind_mem h₀ hU a)]
      congr 1
      funext x
      simp only [ind, sub_zero, add_sub_assoc]
      exact if_congr (U.toAddSubgroup.add_mem_cancel_right hpa) rfl rfl
    · refine off h₀ h2 (ind_mem h₀ hU a) fun b hb hbP => h ⟨b, hbP, ?_⟩
      by_contra hc
      exact hb (if_neg hc)
  have zero : ∀ U ≤ U₀, l (ind U 0) = 0 := by
    intro U hU
    obtain ⟨t, ht, e⟩ := decomp (ind_mem h₀ le_rfl 0) U fun u hu x => by
      simp only [ind, sub_zero]
      exact if_congr (U₀.toAddSubgroup.add_mem_cancel_right (hU hu)) rfl rfl
    have h3 : ∀ q ∈ t, ind U₀ 0 q.out = 1 := fun q hq => by
      have := (ht q).1 hq
      unfold ind at this ⊢
      split_ifs at this ⊢ with h
      · rfl
      · exact absurd rfl this
    rw [e, map_sum, Finset.sum_congr rfl fun q hq => by rw [h3 q hq, one_smul, key U hU], ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul] at h0
    refine (mul_eq_zero.1 h0).resolve_left (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨0, ?_⟩))
    have h4 : (0 : G ⧸ U.toAddSubgroup).out ∈ U :=
      (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' (0 : G ⧸ U.toAddSubgroup))
    refine Finset.mem_filter.2 ⟨(ht _).2 ?_, 0, hP0, by simpa using U.neg_mem h4⟩
    simp [ind, hU h4]
  obtain ⟨U₁, hU₁⟩ := uniform hφ
  obtain ⟨t, -, e⟩ := decomp hφ (U₀ ⊓ U₁) fun u hu => hU₁ u hu.2
  rw [e, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [map_smul, key _ inf_le_left, zero _ inf_le_left, ite_self, smul_zero]

end PositivityTheory.ThKF0.FinLine
