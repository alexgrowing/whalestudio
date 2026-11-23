import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DigitPartMonomial
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.ProjKeepsLetter
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

theorem vala_iff_Aset' {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (θ : ℝ)
    (F : MvPolynomial (L × Fin r) K) : vala sg S θ F ↔ F ∈ Aset sg S ⌈θ⌉ := by
  exact vala_iff_Aset sg S θ F

theorem lg_mono' {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) {a b : ℕ} (hab : a ≤ b) :
    lg p r a ≤ lg p r b := by
  unfold lg
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (a : ℝ) + r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    positivity
  have hle : (a : ℝ) + r ≤ (b : ℝ) + r := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  linarith [Real.logb_le_logb_of_le hp1 hpos hle]

theorem lg_nonneg' {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) (a : ℕ) : 0 ≤ lg p r a := by
  unfold lg
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have h1 : (1 : ℝ) ≤ (a : ℝ) + r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  linarith [Real.logb_nonneg hp1 h1]

theorem monomial_mem_PolK {L : Type} {r : ℕ} (ζ : L × Fin r →₀ ℕ) (c : K) :
    monomial ζ c ∈ PolK K r (fun i => ldeg ζ i) := by
  rw [PolK, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' := MvPolynomial.support_monomial_subset (Finset.mem_coe.1 hm)
  rw [Finset.mem_singleton] at hm'
  subst hm'
  intro i
  rfl

namespace TwistData

variable (D : TwistData K)

theorem primed_embedding_injective : Function.Injective D.aux₃ := by
  have key : ∀ a : Fin D.J, (a.val + D.J - 1) % D.J = if a.val = 0 then D.J - 1 else a.val - 1 := by
    intro a
    have := a.isLt
    split_ifs with h
    · rw [h, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [show a.val + D.J - 1 = (a.val - 1) + D.J by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  intro a b h
  have e : (a.val + D.J - 1) % D.J = (b.val + D.J - 1) % D.J := congrArg Fin.val h
  rw [key a, key b] at e
  apply Fin.ext
  have := a.isLt
  have := b.isLt
  split_ifs at e <;> omega

theorem mem_chainSet (j : Fin D.J) (i : Fin (D.nch j)) (z : D.ML) :
    z ∈ D.chainSet j i ↔ (∃ b ∈ D.chain j i, D.mb b = z) ∨ ∃ m : Fin D.r, D.mw (D.aux₃ j, m) = z := by
  simp [chainSet, wSet]

theorem mem_Yset (j : Fin D.J) (m : Fin D.r) (z : D.ML) :
    z ∈ D.Yset j m ↔ (∃ m' : Fin D.r, D.mw (D.aux₃ j, m') = z) ∨ (∃ b ∈ D.LLj j, D.mb b = z) ∨
      ∃ m' : Fin D.r, m < m' ∧ D.mtp (j, m') = z := by
  simp [Yset, wSet, or_assoc]

theorem mlab_notMem_chainSet (j : Fin D.J) (i : Fin (D.nch j)) (t : D.Tau) :
    D.mlab t ∉ D.chainSet j i := by
  rw [D.mem_chainSet]
  rintro (⟨b, _, h⟩ | ⟨m, h⟩) <;> simp [mlab, mb, mw] at h

theorem mtp_notMem_chainSet (j : Fin D.J) (i : Fin (D.nch j)) (t : D.Tau) :
    D.mtp t ∉ D.chainSet j i := by
  rw [D.mem_chainSet]
  rintro (⟨b, _, h⟩ | ⟨m, h⟩) <;> simp [mtp, mb, mw] at h

theorem chainSet_mono (j : Fin D.J) (i i' : Fin (D.nch j)) (h : D.chain j i ⊆ D.chain j i') :
    D.chainSet j i ⊆ D.chainSet j i' := by
  exact Finset.union_subset_union (Finset.image_subset_image h) (Finset.Subset.refl _)

theorem chainSet_disjoint (hch : ∀ j i, D.chain j i ⊆ D.LLj j) (j j' : Fin D.J) (hj : j ≠ j')
    (i : Fin (D.nch j)) (i' : Fin (D.nch j')) : Disjoint (D.chainSet j i) (D.chainSet j' i') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [D.mem_chainSet] at hz hz'
  rcases hz with ⟨b, hb, rfl⟩ | ⟨m, rfl⟩ <;> rcases hz' with ⟨b', hb', h⟩ | ⟨m', h⟩
  · simp only [mb, Sum.inl.injEq] at h
    subst h
    have h1 := hch j i hb
    have h2 := hch j' i' hb'
    simp only [LLj, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hj (h1.symm.trans h2)
  · simp [mw, mb] at h
  · simp [mw, mb] at h
  · simp only [mw, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
    exact hj (D.primed_embedding_injective h.1).symm

theorem chainSet_pair (hch : ∀ j i, D.chain j i ⊆ D.LLj j)
    (hnest : ∀ (j : Fin D.J) (i i' : Fin (D.nch j)), i < i' → D.chain j i ⊂ D.chain j i')
    (x y : Σ j : Fin D.J, Fin (D.nch j)) :
    D.chainSet x.1 x.2 ⊆ D.chainSet y.1 y.2 ∨ D.chainSet y.1 y.2 ⊆ D.chainSet x.1 x.2 ∨
      Disjoint (D.chainSet x.1 x.2) (D.chainSet y.1 y.2) := by
  obtain ⟨j, i⟩ := x
  obtain ⟨j', i'⟩ := y
  by_cases hj : j = j'
  · subst hj
    rcases lt_trichotomy i i' with h | h | h
    · left
      exact D.chainSet_mono j i i' (hnest j i i' h).1
    · left
      rw [h]
    · right; left
      exact D.chainSet_mono j i' i (hnest j i' i h).1
  · right; right
    exact D.chainSet_disjoint hch j j' hj i i'

theorem chainSet_Yset (hch : ∀ j i, D.chain j i ⊆ D.LLj j) (j : Fin D.J) (i : Fin (D.nch j))
    (j' : Fin D.J) (m : Fin D.r) :
    D.chainSet j i ⊆ D.Yset j' m ∨ Disjoint (D.chainSet j i) (D.Yset j' m) := by
  by_cases hj : j = j'
  · subst hj
    left
    intro z hz
    rw [D.mem_chainSet] at hz
    rw [D.mem_Yset]
    rcases hz with ⟨b, hb, rfl⟩ | ⟨m', rfl⟩
    · right; left
      exact ⟨b, hch j i hb, rfl⟩
    · left
      exact ⟨m', rfl⟩
  · right
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [D.mem_chainSet] at hz
    rw [D.mem_Yset] at hz'
    rcases hz with ⟨b, hb, rfl⟩ | ⟨m1, rfl⟩ <;>
      rcases hz' with ⟨m2, h⟩ | ⟨b2, hb2, h⟩ | ⟨m2, _, h⟩
    · simp [mw, mb] at h
    · simp only [mb, Sum.inl.injEq] at h
      subst h
      have h1 := hch j i hb
      simp only [LLj, Finset.mem_filter, Finset.mem_univ, true_and] at h1 hb2
      exact hj (h1.symm.trans hb2)
    · simp [mtp, mb] at h
    · simp only [mw, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
      exact hj (D.primed_embedding_injective h.1).symm
    · simp [mw, mb] at h
    · simp [mtp, mw] at h

theorem sum_ldeg_le (p : ℕ) (hp : 0 < p) (ζ : D.EM) (h : D.GoodE p ζ) :
    ∑ i : D.ML, ldeg ζ i ≤ D.totDeg := by
  obtain ⟨_, _, hb, ht, _⟩ := h
  unfold totDeg
  simp only [Fintype.sum_sum_type, dO, Sum.elim_inl, Sum.elim_inr]
  have e1 : ∑ b : D.Lb, ldeg ζ (Sum.inl b) = ∑ b : D.Lb, D.dB b :=
    Finset.sum_congr rfl (fun b _ => hb b)
  have e2 : ∀ t : D.Tau, ldeg ζ (Sum.inr (Sum.inl t)) + (ldeg ζ (Sum.inr (Sum.inr (Sum.inl t)))
      + ldeg ζ (Sum.inr (Sum.inr (Sum.inr t)))) ≤ D.dT t := by
    intro t
    have h1 := ht t
    have hP : 0 < D.P p t := by
      show 0 < p ^ D.g t
      exact Nat.pow_pos hp
    have h2 : ldeg ζ (D.mw t) ≤ D.P p t * ldeg ζ (D.mw t) := Nat.le_mul_of_pos_left _ hP
    show ldeg ζ (D.mlab t) + (ldeg ζ (D.mw t) + ldeg ζ (D.mtp t)) ≤ D.dT t
    omega
  rw [e1]
  apply Nat.add_le_add_left
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun t _ => e2 t)

end TwistData

theorem Aset_sum {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (n : ℤ) {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial (L × Fin r) K) (h : ∀ i ∈ s, f i ∈ Aset sg S n) :
    ∑ i ∈ s, f i ∈ Aset sg S n := by
  exact valS_sum_le sg S s f n h

theorem Aset_smul {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (n : ℤ) (a : K)
    {F : MvPolynomial (L × Fin r) K} (h : F ∈ Aset sg S n) : a • F ∈ Aset sg S n := by
  exact le_trans h (valS_smul_le sg S a F)

theorem stepP_of [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ) (C0 : ℝ) (h1 : 1 ≤ C0)
    (hP : PROJ K v p C0) : StepP K v p C0 := by
  intro hD D hV
  obtain ⟨hr, hJ, hc, hch, hnest, hthl, hga⟩ := hV
  haveI : NeZero D.r := ⟨hr.ne'⟩
  have hp0 : 0 < p := hD.prime.pos
  have hp2 : 2 ≤ p := by have := hD.five_le; omega

  let Sx : (Σ j : Fin D.J, Fin (D.nch j)) → Finset D.ML := fun x => D.chainSet x.1 x.2
  let thx : (Σ j : Fin D.J, Fin (D.nch j)) → ℤ := fun x => ⌈D.th x.1 x.2 - D.sl x.1 x.2⌉
  have hpair : ∀ x ∈ (Finset.univ : Finset (Σ j : Fin D.J, Fin (D.nch j))), ∀ y ∈ Finset.univ,
      Sx x ⊆ Sx y ∨ Sx y ⊆ Sx x ∨ Disjoint (Sx x) (Sx y) :=
    fun x _ y _ => D.chainSet_pair hch hnest x y

  have hex := fun d : D.ML → ℕ =>
    prodProj (L := D.ML) (sg := D.msg) (r := D.r) (d := d) hP hD Finset.univ Sx thx hpair
  choose Pr h1 h2 h3 h4 h5 h6 using hex
  obtain ⟨Pj, hPj⟩ : ∃ Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K,
      ∀ ζ : D.EM, Pj (monomial ζ 1) = Pr (fun i => ldeg ζ i) (monomial ζ 1) := by
    refine ⟨(MvPolynomial.basisMonomials (D.ML × Fin D.r) K).constr K
      (fun ζ => Pr (fun i => ldeg ζ i) (monomial ζ 1)), fun ζ => ?_⟩
    have e := (MvPolynomial.basisMonomials (D.ML × Fin D.r) K).constr_basis K
      (fun ζ => Pr (fun i => ldeg ζ i) (monomial ζ 1)) ζ
    rw [MvPolynomial.coe_basisMonomials] at e
    exact e
  have hmono : ∀ (ζ : D.EM) (c : K), monomial ζ c = c • (monomial ζ 1 : MvPolynomial (D.ML × Fin D.r) K) := by
    intro ζ c
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hlin : ∀ Z : MvPolynomial (D.ML × Fin D.r) K,
      Pj Z = ∑ ζ ∈ Z.support, Z.coeff ζ • Pr (fun i => ldeg ζ i) (monomial ζ 1) := by
    intro Z
    conv_lhs => rw [Z.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun ζ _ => ?_)
    rw [hmono, map_smul, hPj]
  have hhom : ∀ (d : D.ML → ℕ), ∀ F ∈ PolK K D.r d, Pj F = Pr d F := by
    intro d F hF
    rw [hlin]
    conv_rhs => rw [F.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun ζ hζ => ?_)
    have hd : (fun i => ldeg ζ i) = d := funext ((mem_PolK_iff d F).1 hF ζ hζ)
    rw [hd, hmono ζ (F.coeff ζ), map_smul]
  refine ⟨Pj, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ ζ' hmem
    rw [hPj] at hmem
    obtain ⟨hdeg, hfix⟩ := prodProj_entries D.msg (fun i => ldeg ζ i) Finset.univ Sx
      (Pr (fun i => ldeg ζ i)) (h1 _) (h6 _) ζ (fun k => rfl) ζ' hmem
    exact ⟨hdeg, fun t a => hfix _ rfl (fun x _ => D.mlab_notMem_chainSet x.1 x.2 t) a,
      fun t a => hfix _ rfl (fun x _ => D.mtp_notMem_chainSet x.1 x.2 t) a⟩
  · intro ζ hG
    have hbm : bge v (vN v (fact ζ) / 2) (monomial ζ (1 : K)) := by
      classical
      intro α
      rw [MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst h
        simp [vge, vR, AddValuation.map_one]
      · simp [vge, vR, AddValuation.map_zero]
    have hb := h4 (fun i => ldeg ζ i) (monomial ζ 1) (monomial_mem_PolK ζ 1) _ hbm
    rw [hPj]
    refine bge_mono (hab := ?_) (h := hb)
    have hcard : ((Finset.univ : Finset (Σ j : Fin D.J, Fin (D.nch j))).card : ℝ)
        = ∑ j, (D.nch j : ℝ) := by
      rw [Finset.card_univ, Fintype.card_sigma]
      simp [Fintype.card_fin]
    have hlg : lg p D.r (2 * ∑ i, ldeg ζ i) ≤ lg p D.r (2 * D.totDeg) :=
      lg_mono' hp2 hr (by have := D.sum_ldeg_le p hp0 ζ hG; omega)
    have hDm : D.Dm p C0 = (∑ j, (D.nch j : ℝ)) * ((D.r : ℝ) ^ 2 * lg p D.r (2 * D.totDeg)) := by
      unfold TwistData.Dm TwistData.eC
      rw [Finset.sum_mul]
    have hnn : (0 : ℝ) ≤ ∑ j, (D.nch j : ℝ) := Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)
    have hm : (∑ j, (D.nch j : ℝ)) * ((D.r : ℝ) ^ 2 * lg p D.r (2 * ∑ i, ldeg ζ i))
        ≤ (∑ j, (D.nch j : ℝ)) * ((D.r : ℝ) ^ 2 * lg p D.r (2 * D.totDeg)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlg (sq_nonneg _)) hnn
    rw [hcard, hDm]
    linarith
  · intro Z j i
    rw [vala_iff_Aset, hlin]
    apply Aset_sum
    intro ζ _
    apply Aset_smul
    exact h2 _ _ (monomial_mem_PolK ζ 1) ⟨j, i⟩ (Finset.mem_univ _)
  · intro A ζ hA hvA
    rw [hPj]
    exact h3 _ A hA (fun x _ => (vala_iff_Aset _ _ _ _).1 (hvA x.1 x.2)) _ (monomial_mem_PolK ζ 1)
  · intro j m θ Z hZ
    have hsplit : Pj Z = ∑ d ∈ Z.support.image (fun α i => ldeg α i), Pr d (hcomp d Z) := by
      conv_lhs => rw [sum_hcomp Z]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun d _ => hhom d _ (hcomp_mem_PolK d Z))
    rw [vala_iff_Aset, hsplit]
    apply Aset_sum
    intro d _
    exact h5 d (D.Yset j m) ⌈θ⌉ (fun x _ => D.chainSet_Yset hch x.1 x.2 j m) _ (hcomp_mem_PolK d Z)
      ((vala_iff_Aset _ _ _ _).1 (vala_hcomp d hZ))

end Formalism.MainNotions.PlaneGram
