import Formalism.RealPlaceAnalysis.StatementKT

open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

theorem mem_compactSpan_self {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : x ∈ kSpan ε F x := by
  unfold kSpan
  rw [Submodule.mem_sInf]
  intro S hS
  exact hS.1

theorem compactSpan_le_of_mem {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) {x : V} {S : Submodule ℂ V} (hx : x ∈ S)
    (hS : KStable ε F S) : kSpan ε F x ≤ S :=
  sInf_le ⟨hx, hS⟩

theorem compactSpan_isCompactInvariant {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  unfold kSpan at *
  rw [Submodule.mem_sInf] at *
  intro S hS
  exact hS.2 a b hab y (hy S hS)

theorem inner_compactCasimir_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hu : KUnit ε F) (y : V) :
    ⟪y, CasK ε F y⟫_ℂ = ((∑ a, ∑ b, if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) : ℂ) := by
  unfold CasK
  simp only [LinearMap.sum_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [Module.End.mul_apply, ← hu b a h.symm y (F b a y), inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  · simp

theorem kWtBound_of (hc : KCasSpan) : KWtBound := by
  intro V _ _ n ε F μ ν x y hr hu hx hy hy0 hν
  have h1 := hc V n ε F μ x hr hx y hy
  have h2 := inner_compactCasimir_self ε F hu y
  rw [h1, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ckv ε μ * ‖y‖ ^ 2 = ∑ a, ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) := by
    apply Complex.ofReal_injective
    push_cast at h2 ⊢
    exact h2
  have h4 : nsq ν * ‖y‖ ^ 2 ≤ ∑ a, ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) := by
    unfold nsq dot
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    calc ν a * ν a * ‖y‖ ^ 2 = (if ε a = ε a then ‖F a a y‖ ^ 2 else 0 : ℝ) := by
          rw [if_pos rfl, hν a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
          ring
      _ ≤ ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) :=
          Finset.single_le_sum (f := fun b => (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ))
            (fun b _ => by split_ifs <;> positivity) (Finset.mem_univ a)
  have hpos : 0 < ‖y‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right (h4.trans h3.ge) hpos

theorem isCompactInvariant_orthogonal_inf {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hu : KUnit ε F)
    {K S : Submodule ℂ V} (hK : KStable ε F K) (hS : KStable ε F S) : KStable ε F (Kᗮ ⊓ S) := by
  intro a b hab y hy
  rw [Submodule.mem_inf] at hy ⊢
  refine ⟨?_, hS a b hab y hy.2⟩
  rw [Submodule.mem_orthogonal]
  intro z hz
  rw [← hu b a hab.symm z y]
  exact (Submodule.mem_orthogonal K y).1 hy.1 _ (hK b a hab.symm z hz)

theorem compactDecomposition_of_finrank (he : KHiExist) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (n : ℕ) (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hr : KRel ε F)
    (hu : KUnit ε F) :
    ∀ (d : ℕ) (S : Submodule ℂ V), Module.finrank ℂ S = d → FiniteDimensional ℂ S →
    KStable ε F S →
    ∃ (m : ℕ) (x : Fin m → V) (μ : Fin m → Fin n → ℝ),
      (∀ i, x i ∈ S ∧ x i ≠ 0 ∧ KHighest ε F (μ i) (x i)) ∧
      (∀ i i', i ≠ i' → ∀ y ∈ kSpan ε F (x i), ∀ z ∈ kSpan ε F (x i'), ⟪y, z⟫_ℂ = 0) ∧
      (⨆ i, kSpan ε F (x i)) = S := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro S hd hfin hS
  by_cases h0 : S = ⊥
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [h0]
    exact iSup_of_empty _
  obtain ⟨x, hxS, hx0, μ, hxμ⟩ := he V n ε F S hfin hr hu hS h0
  have hKS : kSpan ε F x ≤ S := compactSpan_le_of_mem ε F hxS hS
  have : FiniteDimensional ℂ (kSpan ε F x) := Submodule.finiteDimensional_of_le hKS
  have hS'S : (kSpan ε F x)ᗮ ⊓ S < S := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    have hx' : x ∈ (kSpan ε F x)ᗮ ⊓ S := by rw [heq]; exact hxS
    rw [Submodule.mem_inf] at hx'
    have h1 := (Submodule.mem_orthogonal (kSpan ε F x) x).1 hx'.1 x (mem_compactSpan_self ε F x)
    exact hx0 (inner_self_eq_zero.1 h1)
  have : FiniteDimensional ℂ ↥((kSpan ε F x)ᗮ ⊓ S) := Submodule.finiteDimensional_of_le hS'S.le
  have hlt : Module.finrank ℂ ↥((kSpan ε F x)ᗮ ⊓ S) < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hS'S
  obtain ⟨m, xs, μs, h1, h2, h3⟩ := ih _ hlt ((kSpan ε F x)ᗮ ⊓ S) rfl inferInstance
    (isCompactInvariant_orthogonal_inf ε F hu (compactSpan_isCompactInvariant ε F x) hS)
  have hle : ∀ j, kSpan ε F (xs j) ≤ (kSpan ε F x)ᗮ ⊓ S := fun j =>
    h3 ▸ le_iSup (fun i => kSpan ε F (xs i)) j
  refine ⟨m + 1, Fin.cons x xs, Fin.cons μ μs, ?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simp only [Fin.cons_zero]
      exact ⟨hxS, hx0, hxμ⟩
    · simp only [Fin.cons_succ]
      exact ⟨(h1 j).1.2, (h1 j).2⟩
  · intro i i' hii'
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨j', rfl⟩
    · exact absurd rfl hii'
    · simp only [Fin.cons_zero, Fin.cons_succ]
      intro y hy z hz
      exact Submodule.inner_right_of_mem_orthogonal hy (hle j' hz).1
    · simp only [Fin.cons_zero, Fin.cons_succ]
      intro y hy z hz
      exact Submodule.inner_left_of_mem_orthogonal hz (hle j hy).1
    · simp only [Fin.cons_succ]
      exact h2 j j' (fun h => hii' (congrArg Fin.succ h))
  · apply le_antisymm
    · refine iSup_le fun i => ?_
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simpa using hKS
      · simp only [Fin.cons_succ]
        exact (hle j).trans inf_le_right
    · calc S = kSpan ε F x ⊔ (kSpan ε F x)ᗮ ⊓ S :=
            (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKS).symm
        _ ≤ _ := by
          refine sup_le ?_ ?_
          · exact le_iSup_of_le (0 : Fin (m + 1)) (by simp)
          · conv_lhs => rw [← h3]
            exact iSup_le fun j => le_iSup_of_le j.succ (by simp)

theorem kDecomp_of (he : KHiExist) (ho : KOrth) : KDecomp := by
  intro V _ _ n ε F S hfin hr hu hS
  exact compactDecomposition_of_finrank he V n ε F hr hu _ S rfl hfin hS

theorem compactSpan_le_isotypicPart {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Fin n → ℝ)) (S : Submodule ℂ V) {y : V}
    {μ : Fin n → ℝ} (hy : y ∈ S) (hμ : μ ∈ T) (hk : KHighest ε F μ y) :
    kSpan ε F y ≤ isoPart ε F T S := by
  unfold isoPart
  exact le_iSup₂_of_le (f := fun y (_ : y ∈ S ∧ ∃ μ ∈ T, KHighest ε F μ y) => kSpan ε F y)
    y ⟨hy, μ, hμ, hk⟩ le_rfl

theorem isotypicPart_le {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Fin n → ℝ)) (S : Submodule ℂ V)
    (hS : KStable ε F S) : isoPart ε F T S ≤ S := by
  unfold isoPart
  exact iSup₂_le fun y hy => compactSpan_le_of_mem ε F hy.1 hS

theorem kIsoSplit_of (hd : KDecomp) (ho : KOrth) : KIsoSplit := by
  intro V _ _ n ε F S T hfin hr hu hS
  constructor
  · have h : isoPart ε F T S ⟂ isoPart ε F Tᶜ S := by
      unfold isoPart
      rw [Submodule.isOrtho_iSup_left]; intro y
      rw [Submodule.isOrtho_iSup_left]; rintro ⟨_, μ, hμT, hyμ⟩
      rw [Submodule.isOrtho_iSup_right]; intro z
      rw [Submodule.isOrtho_iSup_right]; rintro ⟨_, ν, hνT, hzν⟩
      rw [Submodule.isOrtho_iff_inner_eq]
      exact ho V n ε F μ ν y z hr hu hyμ hzν (fun h => hνT (h ▸ hμT))
    exact Submodule.isOrtho_iff_inner_eq.1 h
  · obtain ⟨m, x, μ, h1, h2, h3⟩ := hd V n ε F S hfin hr hu hS
    apply le_antisymm
    · exact sup_le (isotypicPart_le ε F T S hS) (isotypicPart_le ε F Tᶜ S hS)
    · conv_lhs => rw [← h3]
      refine iSup_le fun i => ?_
      by_cases hi : μ i ∈ T
      · exact le_sup_of_le_left (compactSpan_le_isotypicPart ε F T S (h1 i).1 hi (h1 i).2.2)
      · exact le_sup_of_le_right (compactSpan_le_isotypicPart ε F Tᶜ S (h1 i).1 hi (h1 i).2.2)

theorem abs_compactHalfSum_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : |rhoC ε a| ≤ n := by
  unfold rhoC
  have c1 := Finset.card_filter_le (univ : Finset (Fin n)) (fun b => a < b ∧ ε b = ε a)
  have c2 := Finset.card_filter_le (univ : Finset (Fin n)) (fun b => b < a ∧ ε b = ε a)
  simp only [Finset.card_univ, Fintype.card_fin] at c1 c2
  have d1 : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) ≤ n := by exact_mod_cast c1
  have d2 : ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) ≤ n := by exact_mod_cast c2
  have e1 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  have e2 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem compactCasimirValue_le {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (R : ℝ)
    (hμ : ∀ a, |μ a| ≤ R) : ckv ε μ ≤ n * (R + n) ^ 2 := by
  unfold ckv nsq dot
  have h0 : 0 ≤ ∑ a, rhoC ε a * rhoC ε a := Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have h1 : ∑ a, (μ + rhoC ε) a * (μ + rhoC ε) a ≤ ∑ _a : Fin n, (R + n) ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    simp only [Pi.add_apply]
    have h3 : |μ a + rhoC ε a| ≤ R + n :=
      (abs_add_le (μ a) (rhoC ε a)).trans (add_le_add (hμ a) (abs_compactHalfSum_le ε a))
    rw [← sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  linarith

theorem kCasBound_of (hd : KDecomp) (hc : KCasSpan) (ho : KOrth) : KCasBound := by
  intro V _ _ n ε F S R hfin hr hu hS hR hw y hy
  obtain ⟨m, x, μ, h1, h2, h3⟩ := hd V n ε F S hfin hr hu hS
  have hy' : y ∈ ⨆ i ∈ (univ : Finset (Fin m)), kSpan ε F (x i) := by simpa [h3] using hy
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy'
  have hC : CasK ε F y = ∑ i, ((ckv ε (μ i) : ℝ) : ℂ) • (v i : V) := by
    rw [← hv, map_sum]
    exact Finset.sum_congr rfl fun i _ => hc V n ε F (μ i) (x i) hr (h1 i).2.2 _ (v i).2
  have key : ∀ c : Fin m → ℂ,
      ⟪y, ∑ i, c i • (v i : V)⟫_ℂ = ∑ i, c i * ⟪(v i : V), (v i : V)⟫_ℂ := by
    intro c
    rw [← hv, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right]
    · intro i _ hij
      rw [inner_smul_right, h2 j i (Ne.symm hij) _ (v j).2 _ (v i).2, mul_zero]
    · simp
  have hvv : ∀ i, ⟪(v i : V), (v i : V)⟫_ℂ = ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hn : ‖y‖ ^ 2 = ∑ i, ‖(v i : V)‖ ^ 2 := by
    have h := key (fun _ => 1)
    simp only [one_smul, one_mul, hv, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    exact h
  have key2 := key (fun i => ((ckv ε (μ i) : ℝ) : ℂ))
  rw [hC, key2]
  simp only [hvv]
  have hre : (∑ i, ((ckv ε (μ i) : ℝ) : ℂ) * ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ)).re =
      ∑ i, ckv ε (μ i) * ‖(v i : V)‖ ^ 2 := by
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hre, hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact compactCasimirValue_le ε (μ i) R (hw (μ i) (x i) (h1 i).1 (h1 i).2.1 (h1 i).2.2.1)

end Formalism.REAL
