import Formalism.HermitianCurvature.StatementKB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfCauchySchwarz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWave

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Finset
open scoped ComplexConjugate ComplexOrder

noncomputable section

section form

variable {V : Type} [AddCommGroup V] [Module ℂ V] (Dv : V → Prop) (β : V → V → ℂ)

theorem herm_of_nonneg (h0 : Dv 0) (hadd : ∀ x y, Dv x → Dv y → Dv (x + y)) (hsmul : ∀ (c : ℂ) x, Dv x → Dv (c • x))
    (hl : ∀ x₁ x₂ y (c : ℂ), Dv x₁ → Dv x₂ → Dv y → β (x₁ + c • x₂) y = β x₁ y + c * β x₂ y)
    (hr : ∀ x y₁ y₂ (c : ℂ), Dv x → Dv y₁ → Dv y₂ → β x (y₁ + c • y₂) = β x y₁ + conj c * β x y₂)
    (hpos : ∀ x, Dv x → 0 ≤ β x x) (x y : V) (hx : Dv x) (hy : Dv y) : β y x = conj (β x y) := by
  have e1 : β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y) = β x x + β x y + β y x + β y y := by
    rw [hl _ _ _ _ hx hy (hadd _ _ hx (hsmul _ _ hy)), hr _ _ _ _ hx hx hy, hr _ _ _ _ hy hx hy]
    simp; ring
  have e2 : β (x + Complex.I • y) (x + Complex.I • y) = β x x - Complex.I * β x y + Complex.I * β y x + β y y := by
    rw [hl _ _ _ _ hx hy (hadd _ _ hx (hsmul _ _ hy)), hr _ _ _ _ hx hx hy, hr _ _ _ _ hy hx hy]
    simp only [Complex.conj_I]; ring_nf; rw [Complex.I_sq]; ring
  have p1 := (Complex.nonneg_iff.1 (hpos _ (hadd _ _ hx (hsmul (1 : ℂ) _ hy)))).2
  have p2 := (Complex.nonneg_iff.1 (hpos _ (hadd _ _ hx (hsmul (Complex.I) _ hy)))).2
  have p3 := (Complex.nonneg_iff.1 (hpos _ hx)).2
  have p4 := (Complex.nonneg_iff.1 (hpos _ hy)).2
  rw [e1] at p1
  rw [e2] at p2
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add] at p1 p2
  apply Complex.ext
  · simp only [Complex.conj_re]; linarith
  · simp only [Complex.conj_im]; linarith

theorem gram_psd (h0 : Dv 0) (hadd : ∀ x y, Dv x → Dv y → Dv (x + y)) (hsmul : ∀ (c : ℂ) x, Dv x → Dv (c • x))
    (hl : ∀ x₁ x₂ y (c : ℂ), Dv x₁ → Dv x₂ → Dv y → β (x₁ + c • x₂) y = β x₁ y + c * β x₂ y)
    (hr : ∀ x y₁ y₂ (c : ℂ), Dv x → Dv y₁ → Dv y₂ → β x (y₁ + c • y₂) = β x y₁ + conj c * β x y₂)
    (hpos : ∀ x, Dv x → 0 ≤ β x x) {α : Type} (Y : Finset α) (u : α → V) (hu : ∀ a, Dv (u a)) :
    TB.PSDOn Y (fun a b => β (u a) (u b)) := by
  rw [PBA.psd_iff_qf]
  refine ⟨fun a _ b _ => herm_of_nonneg Dv β h0 hadd hsmul hl hr hpos _ _ (hu a) (hu b), fun c => ?_⟩
  have hD : ∀ t : Finset α, Dv (∑ i ∈ t, conj (c i) • u i) := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using h0
    | insert b t hb ih => rw [Finset.sum_insert hb]; exact hadd _ _ (hsmul _ _ (hu b)) ih
  have key : PBA.qf Y (fun a b => β (u a) (u b)) c =
      β (∑ i ∈ Y, conj (c i) • u i) (∑ i ∈ Y, conj (c i) • u i) := by
    rw [PBG.sesq_sum_left Dv Dv β h0 hadd hsmul hl Y (fun i => conj (c i)) u hu _ (hD Y)]
    unfold PBA.qf
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [PBG.sesq_sum_right Dv Dv β h0 hadd hsmul hr _ (hu a) Y (fun i => conj (c i)) u hu, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Complex.conj_conj]; ring
  rw [key]
  exact (Complex.nonneg_iff.1 (hpos _ (hD Y))).1

end form

section choices

theorem swap3 {α N : Type} [Fintype N] (Y : Finset α) (f : N → α → α → ℂ) :
    ∑ p ∈ Y, ∑ q ∈ Y, ∑ n, f n p q = ∑ n, ∑ p ∈ Y, ∑ q ∈ Y, f n p q := by
  calc ∑ p ∈ Y, ∑ q ∈ Y, ∑ n, f n p q = ∑ p ∈ Y, ∑ n, ∑ q ∈ Y, f n p q :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ n, ∑ p ∈ Y, ∑ q ∈ Y, f n p q := Finset.sum_comm

theorem quad_mix {α N : Type} [Fintype N] (Y : Finset α) (A : N → α → α → ℂ) (θ : N → ℝ) (M : ℂ) (c d : α → ℂ) :
    ∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * (M * ∑ n, (θ n : ℂ) * A n p q) =
      M * ∑ n, (θ n : ℂ) * ∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * A n p q := by
  have e : ∀ p q, c p * conj (d q) * (M * ∑ n, (θ n : ℂ) * A n p q) =
      ∑ n, M * ((θ n : ℂ) * (c p * conj (d q) * A n p q)) := by
    intro p q
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp_rw [e]
  rw [swap3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]

theorem quad_nonneg {α : Type} {Y : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn Y k) (c : α → ℂ) :
    0 ≤ (∑ p ∈ Y, ∑ q ∈ Y, c p * conj (c q) * k p q).re := by
  have h := ((PBA.psd_iff_qf Y k).1 hk).2 (fun p => conj (c p))
  unfold PBA.qf at h
  have e : (∑ p ∈ Y, ∑ q ∈ Y, conj (conj (c p)) * k p q * conj (c q)) =
      ∑ p ∈ Y, ∑ q ∈ Y, c p * conj (c q) * k p q := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.conj_conj]; ring
  rw [e] at h
  exact h

theorem psd_mix {α N : Type} [Fintype N] {Y : Finset α} (A : N → α → α → ℂ) (θ : N → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hθ : ∀ n, 0 ≤ θ n) (hA : ∀ n, TB.PSDOn Y (A n)) :
    TB.PSDOn Y (fun p q => (M : ℂ) * ∑ n, (θ n : ℂ) * A n p q) := by
  rw [PBA.psd_iff_qf]
  refine ⟨fun a ha b hb => ?_, fun c => ?_⟩
  · rw [map_mul, Complex.conj_ofReal, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, Complex.conj_ofReal, ((PBA.psd_iff_qf Y (A n)).1 (hA n)).1 a ha b hb]
  · have e : PBA.qf Y (fun p q => (M : ℂ) * ∑ n, (θ n : ℂ) * A n p q) c =
        (M : ℂ) * ∑ n, (θ n : ℂ) * PBA.qf Y (A n) c := by
      unfold PBA.qf
      have e' : ∀ x y, conj (c x) * ((M : ℂ) * ∑ n, (θ n : ℂ) * A n x y) * c y =
          ∑ n, (M : ℂ) * ((θ n : ℂ) * (conj (c x) * A n x y * c y)) := by
        intro x y
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun n _ => by ring
      simp_rw [e']
      rw [swap3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [e, Complex.re_ofReal_mul, Complex.re_sum]
    refine mul_nonneg hM (Finset.sum_nonneg fun n _ => ?_)
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg (hθ n) (((PBA.psd_iff_qf Y (A n)).1 (hA n)).2 c)

theorem block_of_choices {α N : Type} [Fintype N] (Y : Finset α) (A B P : N → α → α → ℂ) (θ : N → ℝ) (R M : ℝ)
    (hθ : ∀ n, 0 ≤ θ n) (hA : ∀ n, TB.PSDOn Y (A n)) (hB : ∀ n, TB.PSDOn Y (B n)) (hR : 0 ≤ R) (hRM : R ≤ M)
    (hCS : ∀ n (c d : α → ℂ), ‖∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * P n p q‖ ^ 2 ≤
      R ^ 2 * ((∑ p ∈ Y, ∑ p' ∈ Y, c p * conj (c p') * A n p p').re *
        (∑ q ∈ Y, ∑ q' ∈ Y, d q * conj (d q') * B n q q').re)) :
    KB.BlockPSD Y Y (fun p q => (M : ℂ) * ∑ n, (θ n : ℂ) * A n p q) (fun p q => ∑ n, (θ n : ℂ) * P n p q)
      (fun p q => (M : ℂ) * ∑ n, (θ n : ℂ) * B n p q) := by
  have hM : 0 ≤ M := hR.trans hRM
  refine PBA.block_of_cauchy_schwarz _ _ Y Y _ _ _ (psd_mix A θ M hM hθ hA) (psd_mix B θ M hM hθ hB) fun c d => ?_
  set a : N → ℝ := fun n => (∑ p ∈ Y, ∑ p' ∈ Y, c p * conj (c p') * A n p p').re with ha
  set b : N → ℝ := fun n => (∑ q ∈ Y, ∑ q' ∈ Y, d q * conj (d q') * B n q q').re with hb
  have ha0 : ∀ n, 0 ≤ a n := fun n => quad_nonneg (hA n) c
  have hb0 : ∀ n, 0 ≤ b n := fun n => quad_nonneg (hB n) d

  have eA : (∑ p ∈ Y, ∑ p' ∈ Y, c p * conj (c p') * ((M : ℂ) * ∑ n, (θ n : ℂ) * A n p p')).re =
      M * ∑ n, θ n * a n := by
    rw [quad_mix, Complex.re_ofReal_mul, Complex.re_sum]
    simp only [Complex.re_ofReal_mul, ha]
  have eB : (∑ q ∈ Y, ∑ q' ∈ Y, d q * conj (d q') * ((M : ℂ) * ∑ n, (θ n : ℂ) * B n q q')).re =
      M * ∑ n, θ n * b n := by
    rw [quad_mix, Complex.re_ofReal_mul, Complex.re_sum]
    simp only [Complex.re_ofReal_mul, hb]
  rw [eA, eB]

  have eW : (∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * ∑ n, (θ n : ℂ) * P n p q) =
      ∑ n, (θ n : ℂ) * ∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * P n p q := by
    have := quad_mix Y P θ 1 c d
    simp only [one_mul] at this
    exact this
  rw [eW]
  have hn : ∀ n, ‖(θ n : ℂ) * ∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * P n p q‖ ≤
      R * (Real.sqrt (θ n * a n) * Real.sqrt (θ n * b n)) := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hθ n)]
    have h1 : ‖∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * P n p q‖ ≤ R * Real.sqrt (a n * b n) := by
      rw [← Real.sqrt_sq hR, ← Real.sqrt_mul (sq_nonneg R)]
      exact Real.le_sqrt_of_sq_le (hCS n c d)
    have h1' : ‖∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * P n p q‖ ≤ R * (Real.sqrt (a n) * Real.sqrt (b n)) := by
      rw [← Real.sqrt_mul (ha0 n)]; exact h1
    have hsq := Real.mul_self_sqrt (hθ n)
    calc θ n * ‖∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * P n p q‖ ≤ θ n * (R * (Real.sqrt (a n) * Real.sqrt (b n))) :=
          mul_le_mul_of_nonneg_left h1' (hθ n)
      _ = R * (Real.sqrt (θ n * a n) * Real.sqrt (θ n * b n)) := by
          rw [Real.sqrt_mul (hθ n), Real.sqrt_mul (hθ n)]
          linear_combination (-(R * (Real.sqrt (a n) * Real.sqrt (b n)))) * hsq
  have hsum : ‖∑ n, (θ n : ℂ) * ∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * P n p q‖ ≤
      R * ∑ n, Real.sqrt (θ n * a n) * Real.sqrt (θ n * b n) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => hn n).trans (by rw [Finset.mul_sum]))
  have hcs2 : (∑ n, Real.sqrt (θ n * a n) * Real.sqrt (θ n * b n)) ^ 2 ≤
      (∑ n, θ n * a n) * (∑ n, θ n * b n) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun n => Real.sqrt (θ n * a n))
      (fun n => Real.sqrt (θ n * b n))
    simpa only [Real.sq_sqrt (mul_nonneg (hθ _) (ha0 _)), Real.sq_sqrt (mul_nonneg (hθ _) (hb0 _))] using this
  have hSa : 0 ≤ ∑ n, θ n * a n := Finset.sum_nonneg fun n _ => mul_nonneg (hθ n) (ha0 n)
  have hSb : 0 ≤ ∑ n, θ n * b n := Finset.sum_nonneg fun n _ => mul_nonneg (hθ n) (hb0 n)
  have hS0 : 0 ≤ ∑ n, Real.sqrt (θ n * a n) * Real.sqrt (θ n * b n) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc ‖∑ n, (θ n : ℂ) * ∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * P n p q‖ ^ 2
      ≤ (R * ∑ n, Real.sqrt (θ n * a n) * Real.sqrt (θ n * b n)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hsum 2
    _ = R ^ 2 * (∑ n, Real.sqrt (θ n * a n) * Real.sqrt (θ n * b n)) ^ 2 := by ring
    _ ≤ R ^ 2 * ((∑ n, θ n * a n) * (∑ n, θ n * b n)) := mul_le_mul_of_nonneg_left hcs2 (sq_nonneg R)
    _ ≤ M ^ 2 * ((∑ n, θ n * a n) * (∑ n, θ n * b n)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR hRM 2) (mul_nonneg hSa hSb)
    _ = M * (∑ n, θ n * a n) * (M * ∑ n, θ n * b n) := by ring

end choices

section block0

theorem psd_congr {α : Type} {Y : Finset α} {k k' : α → α → ℂ} (h : ∀ x ∈ Y, ∀ y ∈ Y, k x y = k' x y)
    (hk : TB.PSDOn Y k) : TB.PSDOn Y k' := by
  have e : (Matrix.of fun x y : Y => k x y) = Matrix.of fun x y : Y => k' x y := by
    ext x y; exact h x x.2 y y.2
  unfold TB.PSDOn at hk ⊢
  rwa [← e]

variable {V : Type} [AddCommGroup V] [Module ℂ V] (Dv : V → Prop) (β : V → V → ℂ)

theorem block_iso (h0 : Dv 0) (hadd : ∀ x y, Dv x → Dv y → Dv (x + y)) (hsmul : ∀ (c : ℂ) x, Dv x → Dv (c • x))
    (hl : ∀ x₁ x₂ y (c : ℂ), Dv x₁ → Dv x₂ → Dv y → β (x₁ + c • x₂) y = β x₁ y + c * β x₂ y)
    (hr : ∀ x y₁ y₂ (c : ℂ), Dv x → Dv y₁ → Dv y₂ → β x (y₁ + c • y₂) = β x y₁ + conj c * β x y₂)
    (hpos : ∀ x, Dv x → 0 ≤ β x x) (Vop : V → V) (hV : ∀ x, Dv x → Dv (Vop x))
    (hiso : ∀ x y, Dv x → Dv y → β (Vop x) (Vop y) = β x y) {α : Type} (Y : Finset α) (u : α → V)
    (hu : ∀ a, Dv (u a)) (c0 : ℝ) (hc0 : 0 ≤ c0) (a w : α → α → ℂ)
    (ha : ∀ p ∈ Y, ∀ q ∈ Y, a p q = c0 * β (u p) (u q)) (hw : ∀ p ∈ Y, ∀ q ∈ Y, w p q = c0 * β (Vop (u p)) (u q)) :
    KB.BlockPSD Y Y a w a := by
  set β' : V → V → ℂ := fun x y => (c0 : ℂ) * β x y with hβ'
  have hl' : ∀ x₁ x₂ y (c : ℂ), Dv x₁ → Dv x₂ → Dv y → β' (x₁ + c • x₂) y = β' x₁ y + c * β' x₂ y := by
    intro x₁ x₂ y c h₁ h₂ hy; simp only [hβ', hl _ _ _ _ h₁ h₂ hy]; ring
  have hr' : ∀ x y₁ y₂ (c : ℂ), Dv x → Dv y₁ → Dv y₂ → β' x (y₁ + c • y₂) = β' x y₁ + conj c * β' x y₂ := by
    intro x y₁ y₂ c hx h₁ h₂; simp only [hβ', hr _ _ _ _ hx h₁ h₂]; ring
  have hpos' : ∀ x, Dv x → 0 ≤ β' x x := fun x hx => by
    simp only [hβ']
    exact mul_nonneg (by exact_mod_cast hc0) (hpos x hx)
  set z : α ⊕ α → V := fun x => match x with
    | .inl p => Vop (u p)
    | .inr q => u q with hz
  have hzD : ∀ x, Dv (z x) := fun x => by
    cases x with
    | inl p => exact hV _ (hu p)
    | inr q => exact hu q
  have hG := gram_psd Dv β' h0 hadd hsmul hl' hr' hpos' (Y.disjSum Y) z hzD
  rw [PBA.blockPSD_iff]
  refine psd_congr (fun x hx y hy => ?_) hG
  cases x with
  | inl p =>
    cases y with
    | inl q =>
      simp only [hz, hβ', PBA.blockK]
      rw [hiso _ _ (hu p) (hu q), ha p (Finset.inl_mem_disjSum.1 hx) q (Finset.inl_mem_disjSum.1 hy)]
    | inr q =>
      simp only [hz, hβ', PBA.blockK]
      rw [hw p (Finset.inl_mem_disjSum.1 hx) q (Finset.inr_mem_disjSum.1 hy)]
  | inr q =>
    cases y with
    | inl p =>
      simp only [hz, hβ', PBA.blockK]
      rw [hw p (Finset.inl_mem_disjSum.1 hy) q (Finset.inr_mem_disjSum.1 hx), map_mul, Complex.conj_ofReal,
        herm_of_nonneg Dv β h0 hadd hsmul hl hr hpos _ _ (hV _ (hu p)) (hu q)]
    | inr q' =>
      simp only [hz, hβ', PBA.blockK]
      rw [ha q (Finset.inr_mem_disjSum.1 hx) q' (Finset.inr_mem_disjSum.1 hy)]

end block0

theorem common_eps {ι : Type} [Fintype ι] (Q : ι → ℝ → Prop) (hmono : ∀ i ε ε', Q i ε → 0 < ε' → ε' ≤ ε → Q i ε')
    (h : ∀ i, ∃ ε, 0 < ε ∧ Q i ε) : ∃ ε, 0 < ε ∧ ∀ i, Q i ε := by
  classical
  choose f hf using h
  by_cases hne : Nonempty ι
  · obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f i0, (hf i0).1, fun i => hmono i _ _ (hf i).2 (hf i0).1 (hi0 i (Finset.mem_univ i))⟩
  · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hne⟩

section choice

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (Dv : V → Prop) (Dw : W → Prop) (β : V → V → ℂ) (γ : W → W → ℂ) (π : V → W → ℂ)

theorem sum_mem_of {X : Type} [AddCommGroup X] [Module ℂ X] (D : X → Prop) (h0 : D 0)
    (hadd : ∀ x y, D x → D y → D (x + y)) (hsmul : ∀ (c : ℂ) x, D x → D (c • x)) {α : Type} (Y : Finset α)
    (a : α → ℂ) (u : α → X) (hu : ∀ i, D (u i)) : D (∑ i ∈ Y, a i • u i) := by
  classical
  induction Y using Finset.induction_on with
  | empty => simpa using h0
  | insert b t hb ih => rw [Finset.sum_insert hb]; exact hadd _ _ (hsmul _ _ (hu b)) ih

theorem cs_choice (h0 : Dv 0) (hadd : ∀ x y, Dv x → Dv y → Dv (x + y)) (hsmul : ∀ (c : ℂ) x, Dv x → Dv (c • x))
    (h0' : Dw 0) (hadd' : ∀ x y, Dw x → Dw y → Dw (x + y)) (hsmul' : ∀ (c : ℂ) x, Dw x → Dw (c • x))
    (hl : ∀ x₁ x₂ y (c : ℂ), Dv x₁ → Dv x₂ → Dv y → β (x₁ + c • x₂) y = β x₁ y + c * β x₂ y)
    (hr : ∀ x y₁ y₂ (c : ℂ), Dv x → Dv y₁ → Dv y₂ → β x (y₁ + c • y₂) = β x y₁ + conj c * β x y₂)
    (hl' : ∀ x₁ x₂ y (c : ℂ), Dw x₁ → Dw x₂ → Dw y → γ (x₁ + c • x₂) y = γ x₁ y + c * γ x₂ y)
    (hr' : ∀ x y₁ y₂ (c : ℂ), Dw x → Dw y₁ → Dw y₂ → γ x (y₁ + c • y₂) = γ x y₁ + conj c * γ x y₂)
    (hπl : ∀ x₁ x₂ y (c : ℂ), Dv x₁ → Dv x₂ → Dw y → π (x₁ + c • x₂) y = π x₁ y + c * π x₂ y)
    (hπr : ∀ x y₁ y₂ (c : ℂ), Dv x → Dw y₁ → Dw y₂ → π x (y₁ + c • y₂) = π x y₁ + conj c * π x y₂)
    (Vop : V → V) (hV : ∀ x, Dv x → Dv (Vop x))
    (hVlin : ∀ x y (c : ℂ), Dv x → Dv y → Vop (x + c • y) = Vop x + c • Vop y)
    (hiso : ∀ x y, Dv x → Dv y → β (Vop x) (Vop y) = β x y) (Q : ℝ) (hQ : 0 < Q)
    (hCS : ∀ x y, Dv x → Dw y → ‖π x y‖ ^ 2 * Q ≤ (β x x).re * (γ y y).re)
    {α : Type} (Y : Finset α) (u : α → V) (u' : α → W) (hu : ∀ a, Dv (u a)) (hu' : ∀ a, Dw (u' a))
    (κ : ℂ) (cp cm : ℝ) (hcp : 0 < cp) (hcm : 0 < cm) (c d : α → ℂ) :
    ‖∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * (κ * π (Vop (u p)) (u' q))‖ ^ 2 ≤
      (‖κ‖ ^ 2 / (Q * cp * cm)) * ((∑ p ∈ Y, ∑ p' ∈ Y, c p * conj (c p') * ((cp : ℂ) * β (u p) (u p'))).re *
        (∑ q ∈ Y, ∑ q' ∈ Y, d q * conj (d q') * ((cm : ℂ) * γ (u' q) (u' q'))).re) := by
  classical
  set X : V := ∑ p ∈ Y, c p • u p with hX
  set X' : W := ∑ q ∈ Y, d q • u' q with hX'
  have hXD : Dv X := sum_mem_of Dv h0 hadd hsmul Y c u hu
  have hX'D : Dw X' := sum_mem_of Dw h0' hadd' hsmul' Y d u' hu'
  have hV0 : Vop 0 = 0 := by
    have := hVlin 0 0 1 h0 h0
    simp only [one_smul, add_zero] at this
    have h2 : Vop 0 + Vop 0 - Vop 0 = Vop 0 - Vop 0 := by rw [← this]
    simpa using h2
  have hVsum : ∀ t : Finset α, Vop (∑ p ∈ t, c p • u p) = ∑ p ∈ t, c p • Vop (u p) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using hV0
    | insert b t hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb, add_comm (c b • u b), hVlin _ _ _ (sum_mem_of Dv h0 hadd hsmul t c u hu) (hu b), ih, add_comm]

  have eP : ∑ p ∈ Y, ∑ q ∈ Y, c p * conj (d q) * (κ * π (Vop (u p)) (u' q)) = κ * π (Vop X) X' := by
    rw [hX, hVsum Y, PBG.sesq_sum_left Dv Dw π h0 hadd hsmul hπl Y c (fun p => Vop (u p)) (fun p => hV _ (hu p)) _ hX'D,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [PBG.sesq_sum_right Dv Dw π h0' hadd' hsmul' hπr _ (hV _ (hu p)) Y d u' hu', Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have eA : ∑ p ∈ Y, ∑ p' ∈ Y, c p * conj (c p') * ((cp : ℂ) * β (u p) (u p')) = (cp : ℂ) * β X X := by
    rw [hX, PBG.sesq_sum_left Dv Dv β h0 hadd hsmul hl Y c u hu _ hXD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [PBG.sesq_sum_right Dv Dv β h0 hadd hsmul hr _ (hu p) Y c u hu, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have eB : ∑ q ∈ Y, ∑ q' ∈ Y, d q * conj (d q') * ((cm : ℂ) * γ (u' q) (u' q')) = (cm : ℂ) * γ X' X' := by
    rw [hX', PBG.sesq_sum_left Dw Dw γ h0' hadd' hsmul' hl' Y d u' hu' _ hX'D, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [PBG.sesq_sum_right Dw Dw γ h0' hadd' hsmul' hr' _ (hu' p) Y d u' hu', Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [eP, eA, eB, Complex.re_ofReal_mul, Complex.re_ofReal_mul, norm_mul]
  have h1 := hCS _ _ (hV _ hXD) hX'D
  rw [hiso _ _ hXD hXD] at h1
  have hQcc : 0 < Q * cp * cm := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hQcc, mul_pow]
  have hk : 0 ≤ ‖κ‖ ^ 2 := sq_nonneg _
  calc ‖κ‖ ^ 2 * ‖π (Vop X) X'‖ ^ 2 * (Q * cp * cm) = ‖κ‖ ^ 2 * (‖π (Vop X) X'‖ ^ 2 * Q) * (cp * cm) := by ring
    _ ≤ ‖κ‖ ^ 2 * ((β X X).re * (γ X' X').re) * (cp * cm) := by gcongr
    _ = ‖κ‖ ^ 2 * (cp * (β X X).re * (cm * (γ X' X').re)) := by ring

end choice

end

end Formalism.FourierDecayAlt.P.PBL
