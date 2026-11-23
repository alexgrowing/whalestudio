import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemInterConjIff
open MeasureTheory Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.OrbDesc

theorem finsum_eq_zero_of_fibres {α β : Type} (π : α → β) (g : α → ℂ)
    (h : ∀ b, ∑ᶠ a, (if π a = b then g a else 0) = 0) : ∑ᶠ a, g a = 0 := by
  by_cases hf : (Function.support g).Finite
  · rw [finsum_eq_sum_of_support_subset g (s := hf.toFinset) (by simp)]
    rw [← Finset.sum_fiberwise_of_maps_to (s := hf.toFinset) (t := hf.toFinset.image π) (g := π)
      (fun a ha => Finset.mem_image_of_mem π ha)]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Finset.sum_filter]
    refine (finsum_eq_sum_of_support_subset _ (s := hf.toFinset) ?_).symm.trans (h b)
    intro a ha
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at ha
    obtain ⟨_, ha⟩ := ha
    simpa using ha
  · exact finsum_of_infinite_support hf

theorem finsum_comp_eq_ncard {X Z : Type} (A : Set X) (φ : X → Z) (F : Z → ℂ)
    (hφ : ∀ z, {x | x ∈ A ∧ φ x = z}.Finite) :
    ∑ᶠ x, (if x ∈ A then F (φ x) else 0) = ∑ᶠ z, ({x | x ∈ A ∧ φ x = z}.ncard : ℂ) * F z := by
  have hsub : ∀ x, x ∈ Function.support (fun x => if x ∈ A then F (φ x) else 0) ↔ x ∈ A ∧ F (φ x) ≠ 0 := by
    intro x; simp
  have hsz : ∀ z, z ∈ Function.support (fun z => ({x | x ∈ A ∧ φ x = z}.ncard : ℂ) * F z) ↔
      (∃ x, x ∈ A ∧ φ x = z) ∧ F z ≠ 0 := by
    intro z
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Nat.cast_eq_zero, Set.ncard_eq_zero (hφ z)]
    rw [← ne_eq, ← Set.nonempty_iff_ne_empty]
    rfl
  by_cases hf : (Function.support (fun z => ({x | x ∈ A ∧ φ x = z}.ncard : ℂ) * F z)).Finite
  · have hX : (⋃ z ∈ hf.toFinset, {x | x ∈ A ∧ φ x = z}).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) fun z _ => hφ z
    have hmem : ∀ x, x ∈ hX.toFinset ↔ x ∈ A ∧ φ x ∈ hf.toFinset := by
      intro x
      simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨z, hz, hx, rfl⟩
        exact ⟨hx, hz⟩
      · rintro ⟨hx, hz⟩
        exact ⟨_, hz, hx, rfl⟩
    rw [finsum_eq_sum_of_support_subset _ (s := hf.toFinset) (by simp),
      finsum_eq_sum_of_support_subset _ (s := hX.toFinset)]
    · rw [← Finset.sum_fiberwise_of_maps_to (s := hX.toFinset) (t := hf.toFinset) (g := φ)
        (fun x hx => ((hmem x).1 hx).2)]
      refine Finset.sum_congr rfl fun z hz => ?_
      have hset : ((hX.toFinset.filter fun x => φ x = z : Finset X) : Set X) = {x | x ∈ A ∧ φ x = z} := by
        ext x
        simp only [Finset.coe_filter, hmem, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨h1, _⟩, h2⟩
          exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, h2 ▸ hz⟩, h2⟩
      rw [← hset, Set.ncard_coe_finset, Finset.sum_congr rfl (g := fun _ => F z), Finset.sum_const, nsmul_eq_mul]
      intro x hx
      have hx' : x ∈ {x | x ∈ A ∧ φ x = z} := hset ▸ (Finset.mem_coe.2 hx)
      rw [if_pos hx'.1, hx'.2]
    · intro x hx
      rw [hsub] at hx
      rw [Finset.mem_coe, hmem, Set.Finite.mem_toFinset, hsz]
      exact ⟨hx.1, ⟨x, hx.1, rfl⟩, hx.2⟩
  · rw [finsum_of_infinite_support hf, finsum_of_infinite_support]
    intro hX
    apply hf
    refine (hX.image φ).subset fun z hz => ?_
    obtain ⟨⟨x, hx, rfl⟩, h⟩ := (hsz z).1 hz
    exact ⟨x, (hsub x).2 ⟨hx, h⟩, rfl⟩

variable {H : Type} [Group H]

theorem volRat_of_le (U : Subgroup H) {W S : Subgroup H} (hWS : W ≤ S) (h : W.relIndex S ≠ 0) :
    GlobalTheory.LKLoc.volRat U W = (W.relIndex S : ℝ) * GlobalTheory.LKLoc.volRat U S := by
  have e1 := Subgroup.relIndex_inf_mul_relIndex W S U
  have e2 := Subgroup.relIndex_inf_mul_relIndex U W S
  have e3 := Subgroup.relIndex_inf_mul_relIndex W U S
  rw [inf_eq_left.2 hWS] at e1 e2
  rw [inf_comm U S, inf_comm W U, ← e2] at e3
  have hb : W.relIndex (S ⊓ U) ≠ 0 := fun h0 => h (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h0)
  unfold GlobalTheory.LKLoc.volRat
  rw [← e1]
  have e3' : (W.relIndex (S ⊓ U) : ℝ) * (U.relIndex S : ℝ) = (U.relIndex W : ℝ) * (W.relIndex S : ℝ) := by
    exact_mod_cast e3
  have hs : (W.relIndex S : ℝ) ≠ 0 := by exact_mod_cast h
  have hb' : (W.relIndex (S ⊓ U) : ℝ) ≠ 0 := by exact_mod_cast hb
  push_cast
  by_cases hc : (U.relIndex S : ℝ) = 0
  · have hd : (U.relIndex W : ℝ) = 0 := by
      rw [hc, mul_zero] at e3'
      exact (mul_eq_zero.1 e3'.symm).resolve_right hs
    simp [hc, hd]
  · have hd : (U.relIndex W : ℝ) ≠ 0 := by
      intro hd
      rw [hd, zero_mul] at e3'
      exact mul_ne_zero hb' hc e3'
    field_simp
    linear_combination (S.relIndex U : ℝ) * e3'

theorem mem_locPart {T L : Subgroup H} {x g : H} :
    g ∈ GlobalTheory.LKLoc.locPart T L x ↔ g ∈ T ∧ x⁻¹ * g * x ∈ L := by
  first
  | exact @_root_.GlobalTheory.ConjugateIntersectionMembership.mem_inter_conj_iff
  | exact _root_.GlobalTheory.ConjugateIntersectionMembership.mem_inter_conj_iff
  | (apply _root_.GlobalTheory.ConjugateIntersectionMembership.mem_inter_conj_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateIntersectionMembership.mem_inter_conj_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateIntersectionMembership.mem_inter_conj_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateIntersectionMembership.mem_inter_conj_iff ..)

theorem exists_mul_of_mem_sup {L N : Subgroup H} (hLN : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) {k : H}
    (hk : k ∈ L ⊔ N) : ∃ n ∈ N, ∃ l ∈ L, k = n * l := by
  let S : Subgroup H :=
    { carrier := {k | ∃ n ∈ N, ∃ l ∈ L, k = n * l}
      one_mem' := ⟨1, N.one_mem, 1, L.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, l, hl, rfl⟩ ⟨n', hn', l', hl', rfl⟩
        exact ⟨n * (l * n' * l⁻¹), N.mul_mem hn (hLN l hl n' hn'), l * l', L.mul_mem hl hl', by group⟩
      inv_mem' := by
        rintro _ ⟨n, hn, l, hl, rfl⟩
        exact ⟨l⁻¹ * n⁻¹ * l⁻¹⁻¹, hLN _ (L.inv_mem hl) _ (N.inv_mem hn), l⁻¹, L.inv_mem hl, by group⟩ }
  have : L ⊔ N ≤ S := sup_le (fun l hl => ⟨1, N.one_mem, l, hl, by simp⟩)
    (fun n hn => ⟨n, hn, 1, L.one_mem, by simp⟩)
  exact this hk

theorem ncard_fibre_eq_relIndex (T : Subgroup H) {L N : Subgroup H} (hLN : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N)
    {m y : H} (hy : m⁻¹ * y ∈ L ⊔ N) :
    {q : H ⧸ (N ⊓ L) | Quotient.out q ∈ N ∧ DoubleCoset.mk T L (m * Quotient.out q) = DoubleCoset.mk T L y}.ncard =
      (GlobalTheory.LKLoc.locPart T L y).relIndex (GlobalTheory.LKLoc.locPart T (L ⊔ N) y) := by
  set S := GlobalTheory.LKLoc.locPart T (L ⊔ N) y with hS
  have hstab : MulAction.stabilizer S ((y : H) : H ⧸ L) = (GlobalTheory.LKLoc.locPart T L y).subgroupOf S := by
    ext s
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_locPart]
    change (((s : H) * y : H) : H ⧸ L) = _ ↔ _
    rw [eq_comm, QuotientGroup.eq, ← mul_assoc]
    exact ⟨fun h => ⟨(mem_locPart.1 s.2).1, h⟩, fun h => h.2⟩
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer]
  refine Set.ncard_congr (fun q _ => ((m * Quotient.out q : H) : H ⧸ L)) ?_ ?_ ?_
  · rintro q ⟨hq, he⟩
    obtain ⟨t, ht, l, hl, h⟩ := (DoubleCoset.eq T L _ _).1 he.symm
    have hts : t ∈ S := by
      refine mem_locPart.2 ⟨ht, ?_⟩
      have : y⁻¹ * t * y = (m⁻¹ * y)⁻¹ * Quotient.out q * l⁻¹ := by
        calc y⁻¹ * t * y = y⁻¹ * (t * y * l) * l⁻¹ := by group
          _ = _ := by rw [← h]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) (Subgroup.mem_sup_right hq))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left hl))
    refine ⟨⟨t, hts⟩, ?_⟩
    change ((t * y : H) : H ⧸ L) = _
    rw [h, QuotientGroup.eq]
    have : (t * y)⁻¹ * (t * y * l) = l := by group
    rwa [this]
  · rintro q q' ⟨hq, _⟩ ⟨hq', _⟩ he
    rw [QuotientGroup.eq] at he
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    refine ⟨N.mul_mem (N.inv_mem hq) hq', ?_⟩
    have : (m * Quotient.out q)⁻¹ * (m * Quotient.out q') = (Quotient.out q)⁻¹ * Quotient.out q' := by group
    rwa [this] at he
  · rintro _ ⟨s, rfl⟩
    obtain ⟨hsT, hs⟩ := mem_locPart.1 s.2
    obtain ⟨n, hn, l, hl, hnl⟩ := exists_mul_of_mem_sup hLN (Subgroup.mul_mem _ hy hs)
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (N ⊓ L) n
    have hsy : (s : H) * y = m * n * l := by
      calc (s : H) * y = m * (m⁻¹ * y * (y⁻¹ * s * y)) := by group
        _ = _ := by rw [hnl]; group
    refine ⟨(n : H ⧸ (N ⊓ L)), ⟨?_, ?_⟩, ?_⟩
    · rw [hj]; exact N.mul_mem hn j.2.1
    · rw [hj, eq_comm, DoubleCoset.eq]
      refine ⟨s, hsT, l⁻¹ * j, L.mul_mem (L.inv_mem hl) j.2.2, ?_⟩
      rw [hsy]; group
    · change _ = (((s : H) * y : H) : H ⧸ L)
      rw [hj, hsy, QuotientGroup.eq]
      have : (m * (n * j))⁻¹ * (m * n * l) = (j : H)⁻¹ * l := by group
      rw [this]
      exact L.mul_mem (L.inv_mem j.2.2) hl

theorem dsum_eq_zero_of_fibre_sums : ∀ (H : Type) [Group H] (T P N L U : Subgroup H) (Ψ : H → ℂ),
    T ≤ P → N ≤ P → L ≤ P →
    (∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
    (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) → (∀ x, x ∉ P → Ψ x = 0) →
    (∀ x ∈ P, (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex
      (T ⊓ (L ⊔ N).map (MulAut.conj x).toMonoidHom) ≠ 0) →
    (∀ m ∈ P, ∑ᶠ q : H ⧸ (N ⊓ L), (if Quotient.out q ∈ N then Ψ (m * Quotient.out q) else 0) = 0) →
    GlobalTheory.OrbDesc.dsum T L U Ψ = 0 := by
  intro H _ T P N L U Ψ hTP hNP hLP hPN hT hl hr hP hfin hsum
  have hLN : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N := fun l h => hPN l (hLP h)
  have hsup : L ⊔ N ≤ P := sup_le hLP hNP
  unfold dsum
  refine finsum_eq_zero_of_fibres (fun D => DoubleCoset.mk T (L ⊔ N) (Quotient.out D)) _ fun D' => ?_
  obtain ⟨m, rfl⟩ : ∃ m, DoubleCoset.mk T (L ⊔ N) m = D' := ⟨_, DoubleCoset.out_eq' _ _ D'⟩
  by_cases hm : m ∈ P
  swap
  · refine finsum_eq_zero_of_forall_eq_zero fun D => ?_
    split_ifs with h
    · obtain ⟨t, ht, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 h
      have : Quotient.out D ∉ P := fun hD => hm (e ▸ P.mul_mem (P.mul_mem (hTP ht) hD) (hsup hk))
      simp [wt, hP _ this]
    · rfl

  have key : ∀ D : DoubleCoset.Quotient (T : Set H) (L : Set H),
      DoubleCoset.mk T (L ⊔ N) (Quotient.out D) = DoubleCoset.mk T (L ⊔ N) m →
      {q : H ⧸ (N ⊓ L) | Quotient.out q ∈ N ∧ DoubleCoset.mk T L (m * Quotient.out q) = D}.ncard ≠ 0 ∧
      wt T L U Ψ (Quotient.out D) = (GlobalTheory.LKLoc.volRat U (GlobalTheory.LKLoc.locPart T (L ⊔ N) m) : ℂ) *
        (({q : H ⧸ (N ⊓ L) | Quotient.out q ∈ N ∧ DoubleCoset.mk T L (m * Quotient.out q) = D}.ncard : ℂ) *
          Ψ (Quotient.out D)) := by
    intro D h
    obtain ⟨t, ht, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 h.symm
    have hD : D = DoubleCoset.mk T L (m * k) := by
      rw [← DoubleCoset.out_eq' T L D, eq_comm, DoubleCoset.eq]
      exact ⟨t, ht, 1, L.one_mem, by rw [e]; group⟩
    have hc := ncard_fibre_eq_relIndex T hLN (m := m) (y := m * k) (by simpa using hk)
    rw [← hD] at hc
    have hne : (GlobalTheory.LKLoc.locPart T L (m * k)).relIndex (GlobalTheory.LKLoc.locPart T (L ⊔ N) (m * k)) ≠ 0 :=
      hfin _ (P.mul_mem hm (hsup hk))
    have hle : GlobalTheory.LKLoc.locPart T L (m * k) ≤ GlobalTheory.LKLoc.locPart T (L ⊔ N) (m * k) := fun g hg =>
      mem_locPart.2 ⟨(mem_locPart.1 hg).1, Subgroup.mem_sup_left (mem_locPart.1 hg).2⟩
    have h1 : GlobalTheory.LKLoc.locPart T L (Quotient.out D) = GlobalTheory.LKLoc.locPart T L (m * k) := by
      rw [← locPart_mul hT (x := m * k) ht L.one_mem, e]; congr 1; group
    have h2 : GlobalTheory.LKLoc.locPart T (L ⊔ N) (m * k) = GlobalTheory.LKLoc.locPart T (L ⊔ N) m := by
      rw [← locPart_mul hT (x := m) T.one_mem hk, one_mul]
    refine ⟨hc ▸ hne, ?_⟩
    rw [wt, h1, volRat_of_le U hle hne, hc, h2]
    push_cast
    ring
  have hout : ∀ D : DoubleCoset.Quotient (T : Set H) (L : Set H),
      ¬ DoubleCoset.mk T (L ⊔ N) (Quotient.out D) = DoubleCoset.mk T (L ⊔ N) m →
      {q : H ⧸ (N ⊓ L) | Quotient.out q ∈ N ∧ DoubleCoset.mk T L (m * Quotient.out q) = D} = ∅ := by
    intro D h
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hq, rfl⟩
    apply h
    obtain ⟨t, l, ht, hl', e⟩ := DoubleCoset.mk_out_eq_mul T L (m * Quotient.out q)
    rw [e, eq_comm, DoubleCoset.eq]
    exact ⟨t, ht, Quotient.out q * l, Subgroup.mul_mem _ (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left hl'),
      by group⟩
  have hB := finsum_comp_eq_ncard {q : H ⧸ (N ⊓ L) | Quotient.out q ∈ N}
    (fun q => DoubleCoset.mk T L (m * Quotient.out q)) (fun D => Ψ (Quotient.out D)) (fun D => by
      by_cases h : DoubleCoset.mk T (L ⊔ N) (Quotient.out D) = DoubleCoset.mk T (L ⊔ N) m
      · exact Set.finite_of_ncard_ne_zero (key D h).1
      · exact (hout D h) ▸ Set.finite_empty)
  have hΨ : ∀ x, Ψ (Quotient.out (DoubleCoset.mk T L x)) = Ψ x := by
    intro x
    obtain ⟨t, l, ht, hl', e⟩ := DoubleCoset.mk_out_eq_mul T L x
    rw [e, hr l hl', hl t ht]
  simp only [hΨ, Set.mem_setOf_eq] at hB
  have h0 := hsum m hm
  rw [show (∑ᶠ q : H ⧸ (N ⊓ L), (if Quotient.out q ∈ N then Ψ (m * Quotient.out q) else 0)) = _ from by
    convert hB] at h0
  have hm0 := mul_finsum (fun D : DoubleCoset.Quotient (T : Set H) (L : Set H) =>
    (({q : H ⧸ (N ⊓ L) | Quotient.out q ∈ N ∧ DoubleCoset.mk T L (m * Quotient.out q) = D}.ncard : ℂ) *
          Ψ (Quotient.out D))) (GlobalTheory.LKLoc.volRat U (GlobalTheory.LKLoc.locPart T (L ⊔ N) m) : ℂ)
  rw [h0, mul_zero] at hm0
  refine Eq.trans (finsum_congr fun D => ?_) hm0.symm
  split_ifs with h
  · exact (key D h).2
  · rw [hout D h]; simp

end GlobalTheory.OrbDesc
