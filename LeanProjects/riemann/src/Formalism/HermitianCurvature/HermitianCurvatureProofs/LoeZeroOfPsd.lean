import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfChoices

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Finset
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

section gram

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

def gramH (h : α → H) : α → α → ℂ := fun P Q => ⟪h Q, h P⟫_ℂ

theorem qf_gramH (Y : Finset α) (h : α → H) (c : α → ℂ) :
    PBA.qf Y (gramH h) c = ⟪∑ P ∈ Y, conj (c P) • h P, ∑ P ∈ Y, conj (c P) • h P⟫_ℂ := by
  unfold PBA.qf gramH
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring

theorem psd_gramH (Y : Finset α) (h : α → H) : TB.PSDOn Y (gramH h) := by
  rw [PBA.psd_iff_qf]
  refine ⟨fun P _ Q _ => (inner_conj_symm (𝕜 := ℂ) (h P) (h Q)).symm, fun c => ?_⟩
  rw [qf_gramH]
  exact inner_self_nonneg (𝕜 := ℂ)

def Loe (Y : Finset α) (A B : α → α → ℂ) : Prop := TB.PSDOn Y fun P Q => B P Q - A P Q

theorem loe_iff (Y : Finset α) (A B : α → α → ℂ) :
    Loe Y A B ↔ (∀ x ∈ Y, ∀ y ∈ Y, B y x - A y x = conj (B x y - A x y)) ∧
      ∀ c, (PBA.qf Y A c).re ≤ (PBA.qf Y B c).re := by
  unfold Loe
  rw [PBA.psd_iff_qf]
  have e : ∀ c, PBA.qf Y (fun P Q => B P Q - A P Q) c = PBA.qf Y B c - PBA.qf Y A c := by
    intro c; unfold PBA.qf; simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring
  simp only [e, Complex.sub_re, sub_nonneg]

theorem loe_trans {Y : Finset α} {A B C : α → α → ℂ} (h1 : Loe Y A B) (h2 : Loe Y B C) : Loe Y A C := by
  rw [loe_iff] at h1 h2 ⊢
  refine ⟨fun x hx y hy => ?_, fun c => (h1.2 c).trans (h2.2 c)⟩
  have a := h1.1 x hx y hy
  have b := h2.1 x hx y hy
  have : C y x - A y x = (C y x - B y x) + (B y x - A y x) := by ring
  rw [this, a, b, ← map_add]; ring_nf

theorem loe_zero_of_psd {Y : Finset α} {B : α → α → ℂ} (h : TB.PSDOn Y B) : Loe Y (fun _ _ => 0) B := by
  unfold Loe; simpa using h

theorem psd_of_loe_zero {Y : Finset α} {B : α → α → ℂ} (h : Loe Y (fun _ _ => 0) B) : TB.PSDOn Y B := by
  unfold Loe at h; simpa using h

theorem qf_mix {N : Type} [Fintype N] (Y : Finset α) (A : N → α → α → ℂ) (θ : N → ℝ) (M : ℝ) (c : α → ℂ) :
    PBA.qf Y (fun p q => (M : ℂ) * ∑ n, (θ n : ℂ) * A n p q) c = (M : ℂ) * ∑ n, (θ n : ℂ) * PBA.qf Y (A n) c := by
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

theorem norm_mix_sq {N : Type} [Fintype N] (lam : N → ℂ) (W : N → H) :
    ‖∑ n, lam n • W n‖ ^ 2 ≤ (∑ n, ‖lam n‖) * ∑ n, ‖lam n‖ * ‖W n‖ ^ 2 := by
  have h1 : ‖∑ n, lam n • W n‖ ≤ ∑ n, ‖lam n‖ * ‖W n‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_smul _ _).le)
  have h2 : (∑ n, ‖lam n‖ * ‖W n‖) ^ 2 ≤ (∑ n, ‖lam n‖) * ∑ n, ‖lam n‖ * ‖W n‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun n => Real.sqrt ‖lam n‖)
      (fun n => Real.sqrt ‖lam n‖ * ‖W n‖)
    have e1 : ∀ n, Real.sqrt ‖lam n‖ * (Real.sqrt ‖lam n‖ * ‖W n‖) = ‖lam n‖ * ‖W n‖ := fun n => by
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have e2 : ∀ n, Real.sqrt ‖lam n‖ ^ 2 = ‖lam n‖ := fun n => Real.sq_sqrt (norm_nonneg _)
    have e3 : ∀ n, (Real.sqrt ‖lam n‖ * ‖W n‖) ^ 2 = ‖lam n‖ * ‖W n‖ ^ 2 := fun n => by
      rw [mul_pow, e2]
    simp only [e1, e2, e3] at this
    exact this
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem loe_convex {N : Type} [Fintype N] (Y : Finset α) (lam : N → ℂ) (h : N → α → H) :
    Loe Y (gramH fun P => ∑ n, lam n • h n P)
      (fun P Q => ((∑ n, ‖lam n‖ : ℝ) : ℂ) * ∑ n, ((‖lam n‖ : ℝ) : ℂ) * gramH (h n) P Q) := by
  rw [loe_iff]
  constructor
  · intro x _ y _
    simp only [gramH, map_sub, map_mul, map_sum, Complex.conj_ofReal, inner_conj_symm]
  · intro c
    have eW : ∑ P ∈ Y, conj (c P) • ∑ n, lam n • h n P = ∑ n, lam n • ∑ P ∈ Y, conj (c P) • h n P := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun P _ => by rw [mul_comm]
    rw [qf_gramH, eW, qf_mix]
    simp only [qf_gramH]
    have hre : ∀ x : H, (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := fun x => by
      have := inner_self_eq_norm_sq (𝕜 := ℂ) x; simpa using this
    rw [Complex.re_ofReal_mul, Complex.re_sum, hre]
    simp only [Complex.re_ofReal_mul, hre]
    exact norm_mix_sq lam _

theorem loe_congr {Y : Finset α} {A A' B B' : α → α → ℂ} (hA : ∀ x ∈ Y, ∀ y ∈ Y, A x y = A' x y)
    (hB : ∀ x ∈ Y, ∀ y ∈ Y, B x y = B' x y) (h : Loe Y A B) : Loe Y A' B' :=
  psd_congr (fun x hx y hy => by rw [hA x hx y hy, hB x hx y hy]) h

theorem loe_refl (Y : Finset α) (A : α → α → ℂ) : Loe Y A A := by
  unfold Loe
  refine psd_congr (k := fun _ _ => (0 : ℂ)) (fun x _ y _ => by ring) ?_
  rw [PBA.psd_iff_qf]; exact ⟨fun _ _ _ _ => by simp, fun c => by simp [PBA.qf]⟩

theorem loe_add {Y : Finset α} {A B A' B' : α → α → ℂ} (h : Loe Y A B) (h' : Loe Y A' B') :
    Loe Y (fun x y => A x y + A' x y) (fun x y => B x y + B' x y) := by
  rw [loe_iff] at h h' ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy; have b := h'.1 x hx y hy
    have : B y x + B' y x - (A y x + A' y x) = (B y x - A y x) + (B' y x - A' y x) := by ring
    rw [this, a, b, ← map_add]; ring_nf
  · have e : ∀ K K' : α → α → ℂ, PBA.qf Y (fun x y => K x y + K' x y) c = PBA.qf Y K c + PBA.qf Y K' c := by
      intro K K'; unfold PBA.qf; simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, e, Complex.add_re, Complex.add_re]
    linarith [h.2 c, h'.2 c]

theorem loe_smul {Y : Finset α} {A B : α → α → ℂ} (r : ℝ) (hr : 0 ≤ r) (h : Loe Y A B) :
    Loe Y (fun x y => (r : ℂ) * A x y) (fun x y => (r : ℂ) * B x y) := by
  rw [loe_iff] at h ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy
    rw [← mul_sub, ← mul_sub, a, map_mul, Complex.conj_ofReal]
  · have e : ∀ K : α → α → ℂ, PBA.qf Y (fun x y => (r : ℂ) * K x y) c = (r : ℂ) * PBA.qf Y K c := by
      intro K; unfold PBA.qf; simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, e, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (h.2 c) hr

theorem loe_sum {ι : Type} (s : Finset ι) {Y : Finset α} {A B : ι → α → α → ℂ} (h : ∀ i ∈ s, Loe Y (A i) (B i)) :
    Loe Y (fun x y => ∑ i ∈ s, A i x y) (fun x y => ∑ i ∈ s, B i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using loe_refl Y (fun _ _ => (0 : ℂ))
  | insert b t hb ih =>
    have h1 := loe_add (h b (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine loe_congr (fun x _ y _ => ?_) (fun x _ y _ => ?_) h1
    · rw [Finset.sum_insert hb]
    · rw [Finset.sum_insert hb]

theorem loe_diag {Y : Finset α} {A B : α → α → ℂ} (ω : α → ℝ) (h : Loe Y A B) :
    Loe Y (fun x y => (ω x : ℂ) * (ω y : ℂ) * A x y) (fun x y => (ω x : ℂ) * (ω y : ℂ) * B x y) := by
  rw [loe_iff] at h ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy
    have : (ω y : ℂ) * (ω x : ℂ) * B y x - (ω y : ℂ) * (ω x : ℂ) * A y x = (ω y : ℂ) * (ω x : ℂ) * (B y x - A y x) := by
      ring
    rw [this, a]; simp only [map_mul, map_sub, Complex.conj_ofReal]; ring
  · have e : ∀ K : α → α → ℂ, PBA.qf Y (fun x y => (ω x : ℂ) * (ω y : ℂ) * K x y) c =
        PBA.qf Y K (fun x => (ω x : ℂ) * c x) := by
      intro K; unfold PBA.qf
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        simp only [map_mul, Complex.conj_ofReal]; ring
    rw [e, e]
    exact h.2 _

theorem loe_scale {Y : Finset α} {K : α → α → ℂ} (hK : TB.PSDOn Y K) {r r' : ℝ} (hr : 0 ≤ r' - r) :
    Loe Y (fun x y => (r : ℂ) * K x y) (fun x y => (r' : ℂ) * K x y) := by
  have h := loe_smul (r' - r) hr (loe_zero_of_psd hK)
  unfold Loe at h ⊢
  refine psd_congr (fun x _ y _ => ?_) h
  push_cast; ring

theorem gramH_smul (c : ℂ) (h : α → H) :
    gramH (fun P => c • h P) = fun P Q => ((‖c‖ ^ 2 : ℝ) : ℂ) * gramH h P Q := by
  funext P Q
  unfold gramH
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, mul_comm (conj c) c, Complex.mul_conj']
  push_cast; ring

end gram

end

end Formalism.FourierDecayAlt.P.PBL
