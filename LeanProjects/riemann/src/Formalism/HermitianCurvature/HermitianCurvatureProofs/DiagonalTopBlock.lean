import Formalism.HermitianCurvature.StatementTA

namespace Formalism.FourierDecayAlt.P.TA1

open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate

section general
variable {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def form (P : Finset α) (k : α → α → ℂ) (U V : α → H) : ℂ :=
  ∑ p ∈ P, ∑ p' ∈ P, k p p' * ⟪U p, V p'⟫_ℂ

lemma form_self_nonneg (P : Finset α) (k : α → α → ℂ) (hk : PSDOn P k) (V : α → H) :
    0 ≤ (form P k V V).re := by
  classical
  let S : Submodule ℂ H := Submodule.span ℂ (V '' (P : Set α))
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (P.finite_toSet.image V)
  let b := stdOrthonormalBasis ℂ S
  have hmem : ∀ p ∈ P, V p ∈ S := fun p hp => Submodule.subset_span ⟨p, hp, rfl⟩
  let a : Fin (Module.finrank ℂ S) → α → ℂ := fun i p => ⟪((b i : S) : H), V p⟫_ℂ
  have hin : ∀ p ∈ P, ∀ p' ∈ P, ⟪V p, V p'⟫_ℂ = ∑ i, conj (a i p) * a i p' := by
    intro p hp p' hp'
    have h := b.sum_inner_mul_inner ⟨V p, hmem p hp⟩ ⟨V p', hmem p' hp'⟩
    simp only [Submodule.coe_inner] at h
    rw [← h]
    refine sum_congr rfl fun i _ => ?_
    simp only [a, inner_conj_symm]
  have e : form P k V V = ∑ i, ∑ p ∈ P, ∑ p' ∈ P, conj (a i p) * k p p' * a i p' := by
    unfold form
    symm
    rw [Finset.sum_comm]
    refine sum_congr rfl fun p hp => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun p' hp' => ?_
    rw [hin p hp p' hp', mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [e, Complex.re_sum]
  exact sum_nonneg fun i _ => hk.2 (a i)

@[instance_reducible]
noncomputable def core (P : Finset α) (k : α → α → ℂ) (hk : PSDOn P k) :
    PreInnerProductSpace.Core ℂ (α → H) where
  inner U V := form P k U V
  conj_inner_symm U V := by
    unfold form
    simp only [map_sum, map_mul, inner_conj_symm]
    rw [sum_comm]
    refine sum_congr rfl fun p hp => sum_congr rfl fun p' hp' => ?_
    rw [hk.1 p' hp' p hp]
  re_inner_nonneg V := form_self_nonneg P k hk V
  add_left U V X := by
    simp only [form, Pi.add_apply, inner_add_left, mul_add, sum_add_distrib]
  smul_left U V r := by
    simp only [form, Pi.smul_apply, inner_smul_left, mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun p' _ => by ring

lemma sqrt_form_sum_le (P : Finset α) (k : α → α → ℂ) (hk : PSDOn P k) {ι : Type} (T : Finset ι)
    (U : ι → α → H) :
    √(form P k (∑ s ∈ T, U s) (∑ s ∈ T, U s)).re ≤ ∑ s ∈ T, √(form P k (U s) (U s)).re := by
  let c : PreInnerProductSpace.Core ℂ (α → H) := core P k hk
  let _ : SeminormedAddCommGroup (α → H) :=
    @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ (α → H) _ _ _ c
  exact norm_sum_le T U

end general

section points
variable {E : Type} [DecidableEq E]

def ls (p : Pt E) : ℕ := (p.getLast?.map Prod.fst).getD 0

omit [DecidableEq E] in
lemma ls_ext (h : Pt E) (s : ℕ) (t : E) : ls (Formalism.FourierDecayAlt.TA.ext h s t) = s := by
  simp [ls, Formalism.FourierDecayAlt.TA.ext]

lemma mem_PT_succ (Sg : ℕ → ℕ → Finset E) (n : ℕ) (p : Pt E) :
    p ∈ PT Sg (n + 1) ↔ ∃ m, m < n + 1 ∧ ∃ h ∈ PT Sg m, ∃ t ∈ Sg (n + 1) (n + 1 - m),
      Formalism.FourierDecayAlt.TA.ext h (n + 1 - m) t = p := by
  rw [PT]
  simp only [mem_biUnion, mem_attach, true_and, mem_image, Subtype.exists, mem_range]
  constructor
  · rintro ⟨m, hm, h, hh, t, ht, rfl⟩; exact ⟨m, hm, h, hh, t, ht, rfl⟩
  · rintro ⟨m, hm, h, hh, t, ht, rfl⟩; exact ⟨m, hm, h, hh, t, ht, rfl⟩

lemma ls_mem_Icc (Sg : ℕ → ℕ → Finset E) (i : ℕ) (hi : 1 ≤ i) (p : Pt E) (hp : p ∈ PT Sg i) :
    ls p ∈ Icc 1 i := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨m, hm, h, _, t, _, rfl⟩ := (mem_PT_succ Sg n p).1 hp
  rw [ls_ext, mem_Icc]; omega

lemma filter_PT (Sg : ℕ → ℕ → Finset E) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) :
    (PT Sg i).filter (fun p => ls p = s) =
      ((PT Sg (i - s)) ×ˢ (Sg i s)).image (fun x => Formalism.FourierDecayAlt.TA.ext x.1 s x.2) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  ext p
  simp only [mem_filter, mem_PT_succ, mem_image, mem_product, Prod.exists]
  constructor
  · rintro ⟨⟨m, hm, h, hh, t, ht, rfl⟩, hls⟩
    rw [ls_ext] at hls
    subst hls
    have e : n + 1 - (n + 1 - m) = m := by omega
    exact ⟨h, t, ⟨by rwa [e], ht⟩, rfl⟩
  · rintro ⟨h, t, ⟨hh, ht⟩, rfl⟩
    have e : n + 1 - (n + 1 - s) = s := by omega
    exact ⟨⟨n + 1 - s, by omega, h, hh, t, by rwa [e], by rw [e]⟩, ls_ext _ _ _⟩

lemma sum_PT_ls {M : Type} [AddCommMonoid M] (Sg : ℕ → ℕ → Finset E) (i s : ℕ) (hs : 1 ≤ s)
    (hsi : s ≤ i) (F : Pt E → M) :
    ∑ p ∈ PT Sg i, (if ls p = s then F p else 0) =
      ∑ t ∈ Sg i s, ∑ h ∈ PT Sg (i - s), F (Formalism.FourierDecayAlt.TA.ext h s t) := by
  rw [← sum_filter, filter_PT Sg i s hs hsi, sum_image, sum_product_right]
  rintro ⟨h, t⟩ _ ⟨h', t'⟩ _ hxy
  simp only [Formalism.FourierDecayAlt.TA.ext] at hxy
  have := List.append_inj' hxy rfl
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at this
  exact Prod.ext this.1 this.2

end points

theorem isPt_PT {E : Type} [Field E] [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n p, p ∈ PT Sg n → IsPt n p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hp
    cases n with
    | zero =>
      simp [PT] at hp; subst hp; exact ⟨by simp [lvl], by simp⟩
    | succ n =>
      obtain ⟨m, hm, h, hh, t, ht, rfl⟩ := (mem_PT_succ Sg n p).1 hp
      have h0 := ih m (by omega) h hh
      refine ⟨?_, ?_⟩
      · have := h0.1
        simp only [lvl] at this
        simp [lvl, Formalism.FourierDecayAlt.TA.ext, this]; omega
      · intro b hb
        simp only [Formalism.FourierDecayAlt.TA.ext, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact h0.2 b hb
        · exact ⟨by simp; omega, hNZ _ _ t ht⟩

end Formalism.FourierDecayAlt.P.TA1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.TA Finset Filter Topology TA1
open scoped InnerProductSpace ComplexConjugate

theorem split_last_block : Formalism.FourierDecayAlt.TA.SplitLast := by
  intro E _ _ H _ _ W D Sg Φ w i _ hi hK
  let U : ℕ → Pt E → H := fun s p => if ls p = s then Φ w p else 0
  have h1 : Slev D Sg Φ w i =
      (form (PT Sg i) (D.K i) (∑ s ∈ Icc 1 i, U s) (∑ s ∈ Icc 1 i, U s)).re := by
    have hU : ∀ p ∈ PT Sg i, (∑ s ∈ Icc 1 i, U s) p = Φ w p := by
      intro p hp
      rw [Finset.sum_apply]
      simp only [U]
      rw [sum_ite_eq, if_pos (ls_mem_Icc Sg i hi p hp)]
    unfold Slev gram form
    congr 1
    refine sum_congr rfl fun p hp => sum_congr rfl fun p' hp' => ?_
    rw [hU p hp, hU p' hp']
  have h2 : ∀ s ∈ Icc 1 i, Ssplit D Sg Φ w i s = (form (PT Sg i) (D.K i) (U s) (U s)).re := by
    intro s hs
    obtain ⟨hs1, hsi⟩ := mem_Icc.1 hs
    have e : form (PT Sg i) (D.K i) (U s) (U s) =
        ∑ p ∈ PT Sg i, if ls p = s then
          (∑ p' ∈ PT Sg i, if ls p' = s then D.K i p p' * ⟪Φ w p, Φ w p'⟫_ℂ else 0) else 0 := by
      unfold form
      refine sum_congr rfl fun p _ => ?_
      by_cases hp : ls p = s
      · rw [if_pos hp]
        refine sum_congr rfl fun p' _ => ?_
        by_cases hp' : ls p' = s
        · simp only [U, if_pos hp, if_pos hp']
        · simp only [U, if_neg hp', inner_zero_right, mul_zero]
      · rw [if_neg hp]
        refine sum_eq_zero fun p' _ => ?_
        simp only [U, if_neg hp, inner_zero_left, mul_zero]
    rw [e, sum_PT_ls Sg i s hs1 hsi]
    unfold Ssplit Nst offK
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun h _ => ?_
    rw [sum_PT_ls Sg i s hs1 hsi]
  rw [h1]
  refine (sqrt_form_sum_le (PT Sg i) (D.K i) hK (Icc 1 i) U).trans (le_of_eq ?_)
  exact sum_congr rfl fun s hs => by rw [h2 s hs]

theorem diagonal_top_block : Formalism.FourierDecayAlt.TA.DiagTop := by
  intro E _ _ H _ _ W D Sg Φ w hNZ hA2
  unfold Ssplit Diag
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.sum_eq_single t]
  · intro t' ht' hne
    unfold Nst
    refine Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun h' hh' => ?_
    have := hA2 (D.r + 1) 1 le_rfl (by omega) le_rfl h h' t t' (isPt_PT Sg hNZ _ h hh)
      (isPt_PT Sg hNZ _ h' hh') (hNZ _ _ t ht) (hNZ _ _ t' ht')
      (Or.inr ⟨rfl, rfl, fun e => hne e.symm⟩)
    simp [offK, this]
  · intro h; exact absurd ht h

theorem diagonal_cosets : Formalism.FourierDecayAlt.TA.DiagCosets := by
  classical
  intro E _ _ H _ _ W D Sg Φ w i s R hNZ hs hsi hi hA hcov huniq
  obtain ⟨_, hper, hdom, _⟩ := hA i s hs hsi hi
  have hHd : ∀ h ∈ PT Sg (i - s), IsPt (i - s) h := isPt_PT Sg hNZ (i - s)
  have key : ∀ t ∈ Sg i s, ∀ t0, t - t0 ∈ D.La i s →
      (Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t) s t t).re ≤
        (Nst (Φ w) (PT Sg (i - s)) (D.Th i s t0) s t t).re := by
    intro t ht t0 h0
    have e : D.Th i s t = D.Th i s t0 := by
      have := hper t0 (t - t0) h0
      rwa [add_sub_cancel] at this
    have h := form_self_nonneg (PT Sg (i - s)) _ (hdom t (PT Sg (i - s)) (hNZ _ _ t ht) hHd)
      (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t))
    have e2 : form (PT Sg (i - s))
        (fun h h' => D.Th i s t h h' - D.K i (Formalism.FourierDecayAlt.TA.ext h s t) (Formalism.FourierDecayAlt.TA.ext h' s t))
        (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t)) (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t)) =
        Nst (Φ w) (PT Sg (i - s)) (D.Th i s t) s t t -
          Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t) s t t := by
      simp only [form, Nst, offK, sub_mul, sum_sub_distrib]
    rw [e2, e, Complex.sub_re] at h
    linarith
  unfold Diag Cosets
  refine le_trans ?_ (le_of_eq (sum_comm' (s := Sg i s)
    (t := fun t => R.filter (fun t0 => t - t0 ∈ D.La i s)) ?_))
  · refine sum_le_sum fun t ht => ?_
    obtain ⟨t0, ht0, h0⟩ := hcov t ht
    have hf : R.filter (fun x => t - x ∈ D.La i s) = {t0} := by
      ext x
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hx, hxl⟩
        refine huniq x hx t0 ht0 ?_
        have := (D.La i s).sub_mem h0 hxl
        simpa using this
      · rintro rfl; exact ⟨ht0, h0⟩
    rw [hf, sum_singleton]
    exact key t ht t0 h0
  · intro t t0
    simp only [mem_filter]
    tauto

theorem epsilon_limit : Formalism.FourierDecayAlt.TA.EpsLimit := by
  intro E H _ _ W _ len k P Φ V w0 B0 Bc jn hw0 hb hE hV
  have h1 : ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      (gram k V P).re ≤ Bc * wsup len B0 (fun w => ‖Φ eps w []‖ ^ 2) := by
    have hall : ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ p ∈ P, Φ eps w0 p = V p :=
      (Filter.eventually_all_finset P).2 hV
    filter_upwards [hall, self_mem_nhdsWithin] with eps h1 h2
    have h3 := hb eps h2
    have e : gram k (Φ eps w0) P = gram k V P := by
      unfold gram
      refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => ?_
      rw [h1 p hp, h1 p' hp']
    rwa [e] at h3
  have h2 : Tendsto (fun eps => wsup len B0 (fun w => ‖Φ eps w []‖ ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 jn) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [(tendsto_order.1 (hE w0 hw0)).1 a ha] with eps h
      exact lt_of_lt_of_le h (le_ciSup (f := fun w : {w // len w ≤ B0} => ‖Φ eps w.1 []‖ ^ 2)
        (Set.finite_range _).bddAbove ⟨w0, hw0⟩)
    · have : ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ w : {w // len w ≤ B0}, ‖Φ eps w.1 []‖ ^ 2 < (a + jn) / 2 :=
        eventually_all.2 (fun w => (tendsto_order.1 (hE w.1 w.2)).2 _ (by linarith))
      filter_upwards [this] with eps h
      have : Nonempty {w // len w ≤ B0} := ⟨⟨w0, hw0⟩⟩
      exact lt_of_le_of_lt (ciSup_le fun w => (h w).le) (by linarith)
  exact ge_of_tendsto (h2.const_mul Bc) h1

end Formalism.FourierDecayAlt.P
