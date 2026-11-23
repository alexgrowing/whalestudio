import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainBoundaryPrefixChain

open GlobalTheory.SeqCx Matrix
open Classical

noncomputable section

namespace GlobalTheory.SeqCx

theorem mapDomain_prepend_apply' {V : Type} (τ : List V) (y : List V →₀ ℤ) (l : List V) :
    Finsupp.mapDomain (fun w => τ ++ w) y l = if τ <+: l then y (l.drop τ.length) else 0 := by
  by_cases h : τ <+: l
  · obtain ⟨u, rfl⟩ := h
    rw [if_pos (List.prefix_append τ u)]
    have hinj : Function.Injective (fun w : List V => τ ++ w) := fun a b hab => List.append_cancel_left hab
    rw [Finsupp.mapDomain_apply hinj y u]
    simp
  · rw [if_neg h, Finsupp.mapDomain_notin_range]
    rintro ⟨u, rfl⟩
    exact h (List.prefix_append τ u)

theorem bd_mem_supported_of_eraseIdx {V : Type} {A B : Set (List V)}
    (h : ∀ l ∈ A, ∀ i < l.length, l.eraseIdx i ∈ B) {x : List V →₀ ℤ}
    (hx : x ∈ Finsupp.supported ℤ ℤ A) : bd V x ∈ Finsupp.supported ℤ ℤ B := by
  rw [Finsupp.supported_eq_span_single] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    simp only [bd, Finsupp.linearCombination_single, one_smul]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    exact Finsupp.single_mem_supported ℤ _ (h l hl i (Finset.mem_range.1 hi))
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
    rw [LinearMap.map_smul]
    exact Submodule.smul_mem _ r ha

theorem mapDomain_mem_supported_of_maps {V : Type} {A B : Set (List V)} (f : List V → List V)
    (h : ∀ l ∈ A, f l ∈ B) {x : List V →₀ ℤ}
    (hx : x ∈ Finsupp.supported ℤ ℤ A) : Finsupp.mapDomain f x ∈ Finsupp.supported ℤ ℤ B := by
  rw [Finsupp.mem_supported] at hx ⊢
  intro l hl
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hl)
  exact h a (hx ha)

theorem prepend_part_mem_supported {V : Type} (τ : List V) {A B : Set (List V)}
    (h : ∀ w ∈ A, ∀ i < τ.length, τ.eraseIdx i ++ w ∈ B) {y : List V →₀ ℤ}
    (hy : y ∈ Finsupp.supported ℤ ℤ A) :
    (y.sum fun w a => a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1)))
      ∈ Finsupp.supported ℤ ℤ B := by
  refine Submodule.finsuppSum_mem ℤ _ y _ fun w hw => Submodule.smul_mem _ _ ?_
  have hwA : w ∈ A := (Finsupp.mem_supported ℤ y).1 hy (Finsupp.mem_support_iff.2 hw)
  have hb : bd V (Finsupp.single τ 1) ∈
      Finsupp.supported ℤ ℤ {σ | ∃ i < τ.length, σ = τ.eraseIdx i} := by
    refine bd_mem_supported_of_eraseIdx (A := {τ}) ?_ (Finsupp.single_mem_supported ℤ 1 (Set.mem_singleton τ))
    intro l hl i hi
    obtain rfl := Set.mem_singleton_iff.1 hl
    exact ⟨i, hi, rfl⟩
  refine mapDomain_mem_supported_of_maps _ ?_ hb
  intro σ hσ
  obtain ⟨i, hi, rfl⟩ := hσ
  exact h w hwA i hi

theorem drop_eraseIdx_sublist_drop {V : Type} :
    ∀ (l : List V) (i k : ℕ), ((l.eraseIdx i).drop k).Sublist (l.drop k)
  | [], _, _ => by simp
  | a :: t, 0, 0 => by simp
  | a :: t, 0, k + 1 => by simpa using List.drop_sublist_drop_left t (Nat.le_succ k)
  | a :: t, i + 1, 0 => by simpa using List.eraseIdx_sublist (a :: t) (i + 1)
  | a :: t, i + 1, k + 1 => by simpa using drop_eraseIdx_sublist_drop t i k

theorem retract_step : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p k : ℕ), (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length = k + 1 → τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ∀ c ∈ chains {l ∈ F | ∀ y ∈ l.drop (k + 1), y ∈ S} p, bd V c = 0 → ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains {l ∈ F | ∀ y ∈ l.drop k, y ∈ S} p := by
  intro V F S hF p k hex c hc hbd
  have hcs : ∀ l, c l ≠ 0 → (l ∈ F ∧ ∀ y ∈ l.drop (k+1), y ∈ S) ∧ l.length = p := fun l hl =>
    (Finsupp.mem_supported ℤ c).1 hc (Finsupp.mem_support_iff.2 hl)
  set P : Finset (List V) :=
    (c.support.filter (fun l => ¬ ∀ y ∈ l.drop k, y ∈ S)).image (List.take (k+1)) with hPdef
  have hP : ∀ τ ∈ P, τ.length = k+1 ∧ τ ∈ F ∧ k+1 ≤ p ∧
      ∃ hk : k < τ.length, τ[k] ∉ S ∧ τ.getLast? = some τ[k] := by
    intro τ hτ
    simp only [P, Finset.mem_image, Finset.mem_filter, Finsupp.mem_support_iff] at hτ
    obtain ⟨l, ⟨hl0, hlbad⟩, rfl⟩ := hτ
    obtain ⟨⟨hlF, hlS⟩, hlp⟩ := hcs l hl0
    have hkl : k < l.length := by
      by_contra hle
      apply hlbad
      intro y hy
      rw [List.drop_eq_nil_of_le (by omega)] at hy
      simp at hy
    have hlk : l[k] ∉ S := by
      intro hs
      apply hlbad
      intro y hy
      rw [List.drop_eq_getElem_cons hkl] at hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hs
      · exact hlS y hy
    have hlen : (l.take (k+1)).length = k+1 := by
      simp only [List.length_take]
      omega
    refine ⟨hlen, hF l hlF _ (List.take_sublist _ _), by omega, by omega, ?_, ?_⟩
    · simpa using hlk
    · rw [List.getLast?_eq_getElem?]
      simp [hlen]
  have hpre : ∀ τ ∈ P, ∀ m, τ <+: m → ¬ ∀ y ∈ m.drop k, y ∈ S := by
    intro τ hτ m hm hmS
    obtain ⟨hlen, -, -, hk, hkS, -⟩ := hP τ hτ
    obtain ⟨u, rfl⟩ := hm
    apply hkS
    apply hmS
    rw [List.drop_append_of_le_length (by omega), List.drop_eq_getElem_cons hk]
    exact List.mem_append_left _ (List.mem_cons_self ..)
  have huniq : ∀ τ ∈ P, ∀ τ' ∈ P, ∀ l, τ <+: l → τ' <+: l → τ' = τ := by
    intro τ hτ τ' hτ' l h1 h2
    have e1 := List.prefix_iff_eq_take.1 h1
    have e2 := List.prefix_iff_eq_take.1 h2
    rw [(hP τ hτ).1] at e1
    rw [(hP τ' hτ').1] at e2
    rw [e1, e2]
  have hinj : ∀ τ : List V, Function.Injective (fun w : List V => τ ++ w) :=
    fun τ a b hab => List.append_cancel_left hab
  let ys : List V → (List V →₀ ℤ) := fun τ =>
    Finsupp.comapDomain (fun w => τ ++ w) c (fun a _ b _ hab => hinj τ hab)
  have hys : ∀ τ w, ys τ w = c (τ ++ w) := fun τ w => rfl
  have happly : ∀ l, (∑ τ ∈ P, Finsupp.mapDomain (fun w => τ ++ w) (ys τ)) l =
      ∑ τ ∈ P, if τ <+: l then c l else 0 := by
    intro l
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mapDomain_prepend_apply']
    split_ifs with h
    · rw [hys]
      congr 1
      exact List.prefix_iff_eq_append.1 h
    · rfl
  obtain ⟨Cg, hCg⟩ : ∃ C, C = c - ∑ τ ∈ P, Finsupp.mapDomain (fun w => τ ++ w) (ys τ) := ⟨_, rfl⟩
  have hCgmem : Cg ∈ chains {l ∈ F | ∀ y ∈ l.drop k, y ∈ S} p := by
    rw [chains, Finsupp.mem_supported]
    intro l hl
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hCg, Finsupp.sub_apply, happly] at hl
    by_cases hex' : ∃ τ ∈ P, τ <+: l
    · obtain ⟨τ0, hτ0, hpr⟩ := hex'
      rw [Finset.sum_eq_single τ0
        (fun τ hτ hne => by rw [if_neg]; exact fun h => hne (huniq τ0 hτ0 τ hτ l hpr h))
        (fun h => absurd hτ0 h), if_pos hpr, sub_self] at hl
      exact absurd rfl hl
    · push_neg at hex'
      rw [Finset.sum_eq_zero (fun τ hτ => if_neg (hex' τ hτ)), sub_zero] at hl
      obtain ⟨⟨hlF, _⟩, hlp⟩ := hcs l hl
      simp only [Set.mem_setOf_eq]
      refine ⟨⟨hlF, ?_⟩, hlp⟩
      by_contra hbad
      apply hex' (l.take (k+1)) _ (List.take_prefix _ _)
      exact Finset.mem_image.2 ⟨l, Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hl, hbad⟩, rfl⟩
  have hysmem : ∀ τ ∈ P, ys τ ∈ chains (linkIn F S τ) (p - τ.length) := by
    intro τ hτ
    obtain ⟨hlen, -, -, -⟩ := hP τ hτ
    rw [chains, Finsupp.mem_supported]
    intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hys] at hw
    obtain ⟨⟨hF1, hS1⟩, hp1⟩ := hcs _ hw
    rw [List.drop_left' hlen] at hS1
    simp only [Set.mem_setOf_eq, linkIn]
    refine ⟨⟨hS1, hF1⟩, ?_⟩
    rw [List.length_append] at hp1
    omega
  have hGood : ∀ τ ∈ P, ∀ w, (∀ x ∈ w, x ∈ S) → ∀ i < τ.length,
      ∀ y ∈ (τ.eraseIdx i ++ w).drop k, y ∈ S := by
    intro τ hτ w hw i hi y hy
    have hel : (τ.eraseIdx i).length = k := by
      rw [List.length_eraseIdx_of_lt hi, (hP τ hτ).1]
      omega
    rw [List.drop_left' hel] at hy
    exact hw y hy
  have hbdys : ∀ τ ∈ P, bd V (ys τ) = 0 := by
    have hdec : bd V c = bd V Cg + ∑ τ ∈ P, ((ys τ).sum fun w a =>
        a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1))) +
        ∑ τ ∈ P, (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (bd V (ys τ)) := by
      have hc2 : c = Cg + ∑ τ ∈ P, Finsupp.mapDomain (fun w => τ ++ w) (ys τ) := by
        rw [hCg]
        abel
      conv_lhs => rw [hc2]
      rw [map_add, map_sum, add_assoc, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun τ _ => GlobalTheory.T.seqChain_boundary_prefix_chain V τ (ys τ)
    set g := bd V Cg + ∑ τ ∈ P, ((ys τ).sum fun w a =>
        a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1))) with hg
    have hgmem : g ∈ Finsupp.supported ℤ ℤ {l | ∀ y ∈ l.drop k, y ∈ S} := by
      refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun τ hτ => ?_)
      · refine bd_mem_supported_of_eraseIdx (A := {l | ∀ y ∈ l.drop k, y ∈ S}) ?_
          (Finsupp.supported_mono ?_ hCgmem)
        · intro l hl i _
          exact fun y hy => hl y ((drop_eraseIdx_sublist_drop l i k).subset hy)
        · intro l hl
          exact hl.1.2
      · refine prepend_part_mem_supported τ (A := {w | ∀ x ∈ w, x ∈ S}) ?_
          (Finsupp.supported_mono ?_ (hysmem τ hτ))
        · intro w hw i hi
          exact hGood τ hτ w hw i hi
        · intro w hw
          exact hw.1.1
    intro τ0 hτ0
    ext w
    have h0 := congrArg (fun f => f (τ0 ++ w)) hdec
    simp only [hbd, Finsupp.zero_apply] at h0
    rw [Finsupp.add_apply, Finsupp.finset_sum_apply] at h0
    have hg0 : g (τ0 ++ w) = 0 := by
      by_contra hne
      exact hpre τ0 hτ0 (τ0 ++ w) (List.prefix_append _ _)
        ((Finsupp.mem_supported ℤ g).1 hgmem (Finsupp.mem_support_iff.2 hne))
    rw [hg0, zero_add, Finset.sum_eq_single τ0] at h0
    · rw [Finsupp.smul_apply, mapDomain_prepend_apply', if_pos (List.prefix_append _ _),
        List.drop_left, smul_eq_mul] at h0
      rw [Finsupp.zero_apply]
      rcases mul_eq_zero.1 h0.symm with h | h
      · exact absurd h (pow_ne_zero _ (by norm_num))
      · exact h
    · intro τ hτ hne
      rw [Finsupp.smul_apply, mapDomain_prepend_apply', if_neg, smul_zero]
      exact fun h => hne (huniq τ0 hτ0 τ hτ _ (List.prefix_append _ _) h)
    · intro h
      exact absurd hτ0 h
  have hz : ∀ τ ∈ P, ∃ z, z ∈ chains (linkIn F S τ) (p - τ.length + 1) ∧ bd V z = ys τ := by
    intro τ hτ
    obtain ⟨hlen, hτF, hkp, hk, hkS, hlast⟩ := hP τ hτ
    obtain ⟨z, hzm, hzb⟩ :=
      hex τ hτF τ[k] hlast hkS hlen (by omega) (ys τ) (hysmem τ hτ) (hbdys τ hτ)
    exact ⟨z, hzm, hzb⟩
  choose! zf hzc hzb using hz
  refine ⟨∑ τ ∈ P, (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (zf τ), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun τ hτ => Submodule.smul_mem _ _ ?_
    obtain ⟨hlen, hτF, hkp, -⟩ := hP τ hτ
    refine mapDomain_mem_supported_of_maps _ ?_ (hzc τ hτ)
    intro w hw
    simp only [Set.mem_setOf_eq, linkIn] at hw ⊢
    obtain ⟨⟨_, hwF⟩, hwl⟩ := hw
    refine ⟨hwF, ?_⟩
    rw [List.length_append, hwl]
    omega
  · have hbdb : bd V (∑ τ ∈ P, (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (zf τ)) =
        ∑ τ ∈ P, ((-1 : ℤ) ^ τ.length • ((zf τ).sum fun w a =>
          a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1))) +
          Finsupp.mapDomain (fun w => τ ++ w) (ys τ)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      rw [LinearMap.map_smul, GlobalTheory.T.seqChain_boundary_prefix_chain, hzb τ hτ, smul_add, smul_smul, ← mul_pow]
      simp
    rw [hbdb, Finset.sum_add_distrib]
    have hrw : c - (∑ τ ∈ P, (-1 : ℤ) ^ τ.length • ((zf τ).sum fun w a =>
          a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1))) +
          ∑ τ ∈ P, Finsupp.mapDomain (fun w => τ ++ w) (ys τ)) =
        Cg - ∑ τ ∈ P, (-1 : ℤ) ^ τ.length • ((zf τ).sum fun w a =>
          a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1))) := by
      rw [hCg]
      abel
    rw [hrw]
    refine Submodule.sub_mem _ hCgmem (Submodule.sum_mem _ fun τ hτ => Submodule.smul_mem _ _ ?_)
    obtain ⟨hlen, hτF, hkp, -⟩ := hP τ hτ
    refine prepend_part_mem_supported τ ?_ (hzc τ hτ)
    intro w hw i hi
    simp only [Set.mem_setOf_eq, linkIn] at hw ⊢
    obtain ⟨⟨hwS, hwF⟩, hwl⟩ := hw
    have hel : (τ.eraseIdx i).length = k := by
      rw [List.length_eraseIdx_of_lt hi, hlen]
      omega
    refine ⟨⟨hF _ hwF _ ((List.eraseIdx_sublist τ i).append_right w), ?_⟩, ?_⟩
    · intro y hy
      rw [List.drop_left' hel] at hy
      exact hwS y hy
    · rw [List.length_append, hel, hwl]
      omega

end GlobalTheory.SeqCx

end

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_cycle_retraction_of_link_exact : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p k : ℕ), (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length = k + 1 → τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ∀ c ∈ chains {l ∈ F | ∀ y ∈ l.drop (k + 1), y ∈ S} p, bd V c = 0 → ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains {l ∈ F | ∀ y ∈ l.drop k, y ∈ S} p := by
  first
  | exact @GlobalTheory.SeqCx.retract_step
  | exact @GlobalTheory.SeqCx.drop_eraseIdx_sublist_drop
  | exact @GlobalTheory.SeqCx.prepend_part_mem_supported
  | exact @GlobalTheory.SeqCx.mapDomain_mem_supported_of_maps
  | exact @GlobalTheory.SeqCx.bd_mem_supported_of_eraseIdx
  | exact @GlobalTheory.SeqCx.mapDomain_prepend_apply'
end
