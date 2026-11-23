import Formalism.HermitianCurvature.StatementTA

namespace Formalism.FourierDecayAlt.P.PointSetConstantMembership

open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate

theorem gram_nonneg {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : Finset α) (k : α → α → ℂ) (V : α → H)
    (hk : ∀ a : α → ℂ, 0 ≤ (∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y).re) :
    0 ≤ (∑ p ∈ P, ∑ p' ∈ P, k p p' * ⟪V p, V p'⟫_ℂ).re := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Matrix P P ℂ, Matrix.gram ℂ (fun p : P => V p.1) = star B * B := by
    open scoped MatrixOrder Matrix.Norms.L2Operator in
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
      (Matrix.posSemidef_gram ℂ (fun p : P => V p.1)).nonneg
  have hG : ∀ p (hp : p ∈ P) p' (hp' : p' ∈ P),
      ⟪V p, V p'⟫_ℂ = ∑ j, conj (B j ⟨p, hp⟩) * B j ⟨p', hp'⟩ := by
    intro p hp p' hp'
    have := congrFun (congrFun hB ⟨p, hp⟩) ⟨p', hp'⟩
    simpa [Matrix.gram, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] using this
  set a : P → α → ℂ := fun j p => if h : p ∈ P then B j ⟨p, h⟩ else 0 with ha
  have e : ∑ p ∈ P, ∑ p' ∈ P, k p p' * ⟪V p, V p'⟫_ℂ
      = ∑ j, ∑ x ∈ P, ∑ y ∈ P, conj (a j x) * k x y * a j y := by
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' hp' => ?_
    rw [hG p hp p' hp', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ha, dif_pos hp, dif_pos hp']
    ring
  rw [e, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => hk (a j)

theorem norm_sq_comb {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : Finset α) (c : α → ℂ) (V : α → H) :
    ((‖∑ p ∈ P, c p • V p‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ P, ∑ p' ∈ P, (conj (c p) * c p') * ⟪V p, V p'⟫_ℂ := by
  have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ p ∈ P, c p • V p)
  rw [Complex.ofReal_pow]
  refine this.symm.trans ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

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
      rw [PT] at hp
      simp only [mem_biUnion, mem_attach, true_and, mem_image, Subtype.exists, mem_range] at hp
      obtain ⟨m, hm, h, hh, t, ht, rfl⟩ := hp
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

theorem mem_PT_const {E : Type} [Field E] [DecidableEq E] (T : Finset E) (p : Pt E) :
    ∀ n, IsPt n p → (∀ b ∈ p, b.2 ∈ T) → p ∈ PT (fun _ _ => T) n := by
  induction p using List.reverseRecOn with
  | nil =>
    intro n hp _
    have : n = 0 := by simpa [lvl] using hp.1.symm
    subst this
    simp [PT]
  | append_singleton h b ih =>
    intro n hp hT
    obtain ⟨s, t⟩ := b
    have hs : 1 ≤ s := (hp.2 (s, t) (by simp)).1
    have hl : lvl h + s = n := by
      have := hp.1
      simpa [lvl] using this
    have hh : h ∈ PT (fun _ _ => T) (lvl h) :=
      ih (lvl h) ⟨rfl, fun b hb => hp.2 b (by simp [hb])⟩ (fun b hb => hT b (by simp [hb]))
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [PT]
    simp only [mem_biUnion, mem_attach, true_and, mem_image, Subtype.exists, mem_range]
    refine ⟨lvl h, by omega, h, hh, t, hT (s, t) (by simp), ?_⟩
    have : n' + 1 - lvl h = s := by omega
    rw [this]; rfl

theorem bound_PT {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Kn : Pt E → Pt E → ℂ) (V : Pt E → H) {ρ : Type}
    (c : ρ → Pt E → ℂ) (P : Finset (Pt E)) (R : Finset ρ)
    (h : PSDOn P (fun p p' => Kn p p' - ∑ x ∈ R, conj (c x p) * c x p')) :
    ∑ x ∈ R, ‖∑ p ∈ P, c x p • V p‖ ^ 2 ≤ (gram Kn V P).re := by
  have h0 := gram_nonneg P _ V h.2
  have e : ∑ p ∈ P, ∑ p' ∈ P, (Kn p p' - ∑ x ∈ R, conj (c x p) * c x p') * ⟪V p, V p'⟫_ℂ
      = gram Kn V P - ((∑ x ∈ R, ‖∑ p ∈ P, c x p • V p‖ ^ 2 : ℝ) : ℂ) := by
    unfold gram
    rw [Complex.ofReal_sum]
    simp_rw [norm_sq_comb]
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [sub_mul, Finset.sum_mul]
  rw [e, Complex.sub_re, Complex.ofReal_re] at h0
  linarith

end Formalism.FourierDecayAlt.P.PointSetConstantMembership

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate

theorem domination_limit : Formalism.FourierDecayAlt.TA.TopDominationLimit := by
  intro E _ _ H _ _ _ n Kn V ρ c B hB hA4 hS R
  classical
  have hsum : ∀ x, Summable (fun p : {p : Pt E // IsPt n p} => c x p.1 • V p.1) := by
    intro x
    refine Summable.of_norm ?_
    simpa [norm_smul] using hS x
  have hlim : Tendsto (fun F : Finset {p : Pt E // IsPt n p} =>
      ∑ x ∈ R, ‖∑ p ∈ F, c x p.1 • V p.1‖ ^ 2) atTop
      (𝓝 (∑ x ∈ R, ‖∑' p : {p : Pt E // IsPt n p}, c x p.1 • V p.1‖ ^ 2)) := by
    refine tendsto_finsetSum _ fun x _ => ?_
    exact ((hsum x).hasSum.norm).pow 2
  refine le_of_tendsto_of_frequently hlim ?_
  rw [Filter.frequently_atTop]
  intro F
  set T : Finset E := F.biUnion fun p => (p.1.map Prod.snd).toFinset with hT
  have hNZ : NZSg (fun _ _ : ℕ => T) := by
    intro i s t ht
    simp only [hT, mem_biUnion, List.mem_toFinset, List.mem_map] at ht
    obtain ⟨p, _, b, hb, rfl⟩ := ht
    exact (p.2.2 b hb).2
  have hPt := PointSetConstantMembership.isPt_PT (fun _ _ => T) hNZ n
  refine ⟨(PT (fun _ _ => T) n).subtype (IsPt n), ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_subtype]
    refine PointSetConstantMembership.mem_PT_const T p.1 n p.2 fun b hb => ?_
    simp only [hT, mem_biUnion, List.mem_toFinset, List.mem_map]
    exact ⟨p, hp, b, hb, rfl⟩
  · have e : ∀ x, ∑ p ∈ (PT (fun _ _ => T) n).subtype (IsPt n), c x p.1 • V p.1
        = ∑ p ∈ PT (fun _ _ => T) n, c x p • V p := by
      intro x
      exact Finset.sum_subtype_of_mem (fun p => c x p • V p) hPt
    simp_rw [e]
    exact (PointSetConstantMembership.bound_PT Kn V c _ R (hA4 _ R hPt)).trans (hB _ hNZ)

end Formalism.FourierDecayAlt.P
