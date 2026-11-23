import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussianHessianIntegral
import Lemmata.GeneralBFactSecondBisForm.Goal1

section PartD0

open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel

noncomputable section

def Sym {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Set E) (w : E → ℝ) (m : ℤ) (N : ℕ) (K : ℝ) (f : E → F) : Prop :=
  ContDiff ℝ N f ∧ ∀ x ∈ A, ∀ i : ℕ, i ≤ N → ‖iteratedFDeriv ℝ i f x‖ ≤ K * w x ^ (m - (i : ℤ))

def wt {E : Type*} [NormedAddCommGroup E] (σ : ℝ) (x : E) : ℝ := ‖x‖ + σ

def osc {E : Type*} (φ : E → ℝ) (τ : ℝ) (x : E) : ℂ := Complex.exp (Complex.I * ((φ x / τ : ℝ) : ℂ))

def dirv {d : ℕ} (l : Fin d × Bool) : Fin d → ℂ := Pi.single l.1 (if l.2 then Complex.I else 1)

def cutB (d : ℕ) (ρ : ℝ) (x : Fin d → ℂ) : ℝ :=
  if h : 0 < ρ then (⟨ρ / 2, ρ, half_pos h, half_lt_self h⟩ : ContDiffBump (0 : Fin d → ℂ)) x else 0

def quad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : E → ℝ) (x : E) : ℝ :=
  φ 0 + (1 / 2) * fderiv ℝ (fderiv ℝ φ) 0 x x

end

end Formalism.FourierDecayAlt.P.StationaryPhaseModel

end PartD0

section PartA

open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel

section SymCalc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {A : Set E} {w : E → ℝ} {m m₁ m₂ : ℤ} {N : ℕ} {K K₁ K₂ : ℝ}

theorem A_const_nonneg {f : E → F} (hw : ∀ x ∈ A, 0 < w x) (h : Sym A w m N K f) {x : E} (hx : x ∈ A) :
    0 ≤ K := by
  have h0 := h.2 x hx 0 (Nat.zero_le _)
  have hp : 0 < w x ^ (m - ((0 : ℕ) : ℤ)) := zpow_pos (hw x hx) _
  by_contra hK
  push Not at hK
  have : K * w x ^ (m - ((0 : ℕ) : ℤ)) < 0 := mul_neg_of_neg_of_pos hK hp
  linarith [norm_nonneg (iteratedFDeriv ℝ 0 f x)]

theorem Sym.mono {f : E → F} {N' : ℕ} {K' : ℝ} (hw : ∀ x ∈ A, 0 < w x) (h : Sym A w m N K f) (hN : N' ≤ N)
    (hK : K ≤ K') : Sym A w m N' K' f := by
  refine ⟨h.1.of_le (by exact_mod_cast hN), fun x hx i hi => ?_⟩
  refine (h.2 x hx i (hi.trans hN)).trans ?_
  exact mul_le_mul_of_nonneg_right hK (zpow_pos (hw x hx) _).le

theorem Sym.subset {f : E → F} {A' : Set E} (h : Sym A w m N K f) (hA : A' ⊆ A) : Sym A' w m N K f :=
  ⟨h.1, fun x hx i hi => h.2 x (hA hx) i hi⟩

theorem A_cda {f : E → F} (h : ContDiff ℝ N f) {i : ℕ} (hi : i ≤ N) (x : E) : ContDiffAt ℝ i f x :=
  (h.of_le (by exact_mod_cast hi)).contDiffAt

theorem Sym.add {f g : E → F} (hf : Sym A w m N K₁ f) (hg : Sym A w m N K₂ g) :
    Sym A w m N (K₁ + K₂) (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun x hx i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun x => f x + g x) x = iteratedFDeriv ℝ i f x + iteratedFDeriv ℝ i g x :=
    iteratedFDeriv_add_apply (A_cda hf.1 hi x) (A_cda hg.1 hi x)
  rw [h1, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf.2 x hx i hi) (hg.2 x hx i hi))

theorem Sym.neg {f : E → F} (hf : Sym A w m N K f) : Sym A w m N K (fun x => - f x) := by
  refine ⟨hf.1.neg, fun x hx i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun x => - f x) x = - iteratedFDeriv ℝ i f x :=
    iteratedFDeriv_neg_apply
  rw [h1, norm_neg]
  exact hf.2 x hx i hi

theorem Sym.sub {f g : E → F} (hf : Sym A w m N K₁ f) (hg : Sym A w m N K₂ g) :
    Sym A w m N (K₁ + K₂) (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem Sym.sum {ι : Type*} (s : Finset ι) {f : ι → E → F} {Kl : ι → ℝ}
    (h : ∀ l ∈ s, Sym A w m N (Kl l) (f l)) : Sym A w m N (∑ l ∈ s, Kl l) (fun x => ∑ l ∈ s, f l x) := by
  refine ⟨ContDiff.sum fun l hl => (h l hl).1, fun x hx i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun x => ∑ l ∈ s, f l x) = ∑ l ∈ s, iteratedFDeriv ℝ i (f l) :=
    iteratedFDeriv_sum fun l hl => (h l hl).1.of_le (by exact_mod_cast hi)
  rw [h1, Finset.sum_apply, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => (h l hl).2 x hx i hi)

theorem Sym.const_smul {f : E → F} (c : ℝ) (hf : Sym A w m N K f) :
    Sym A w m N (|c| * K) (fun x => c • f x) := by
  refine ⟨hf.1.const_smul c, fun x hx i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun x => c • f x) x = c • iteratedFDeriv ℝ i f x :=
    iteratedFDeriv_const_smul_apply (A_cda hf.1 hi x)
  rw [h1, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf.2 x hx i hi) (abs_nonneg c)

theorem Sym.const_smul_complex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : E → V} (c : ℂ)
    (hf : Sym A w m N K f) : Sym A w m N (‖c‖ * K) (fun x => c • f x) := by
  refine ⟨hf.1.const_smul c, fun x hx i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun x => c • f x) x = c • iteratedFDeriv ℝ i f x :=
    iteratedFDeriv_const_smul_apply (A_cda hf.1 hi x)
  rw [h1, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf.2 x hx i hi) (norm_nonneg c)

theorem Sym.smul {f : E → ℝ} {g : E → F} (hw : ∀ x ∈ A, 0 < w x) (hf : Sym A w m₁ N K₁ f)
    (hg : Sym A w m₂ N K₂ g) : Sym A w (m₁ + m₂) N (2 ^ N * K₁ * K₂) (fun x => f x • g x) := by
  refine ⟨hf.1.smul hg.1, fun x hx n hn => ?_⟩
  have hK₁ := A_const_nonneg hw hf hx
  have hK₂ := A_const_nonneg hw hg hx
  have hwx := hw x hx
  refine (norm_iteratedFDeriv_smul_le hf.1 hg.1 x (by exact_mod_cast hn)).trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ ≤
        (n.choose i : ℝ) * (K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ))) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := hf.2 x hx i (hin.trans hn)
    have h2 := hg.2 x hx (n - i) ((Nat.sub_le _ _).trans hn)
    have h3 : w x ^ (m₁ - (i : ℤ)) * w x ^ (m₂ - ((n - i : ℕ) : ℤ)) = w x ^ (m₁ + m₂ - (n : ℤ)) := by
      rw [← zpow_add₀ hwx.ne']
      congr 1
      push_cast [hin]
      ring
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖
        ≤ (K₁ * w x ^ (m₁ - (i : ℤ))) * (K₂ * w x ^ (m₂ - ((n - i : ℕ) : ℤ))) :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ)) := by rw [← h3]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hs : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [hs]
  have hpos : 0 ≤ K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ)) :=
    mul_nonneg (mul_nonneg hK₁ hK₂) (zpow_pos hwx _).le
  calc (2 : ℝ) ^ n * (K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ)))
      ≤ 2 ^ N * (K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ))) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hpos
    _ = 2 ^ N * K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ)) := by ring

theorem Sym.mul {f g : E → ℝ} (hw : ∀ x ∈ A, 0 < w x) (hf : Sym A w m₁ N K₁ f)
    (hg : Sym A w m₂ N K₂ g) : Sym A w (m₁ + m₂) N (2 ^ N * K₁ * K₂) (fun x => f x * g x) := by
  simpa only [smul_eq_mul] using Sym.smul hw hf hg

theorem Sym.fderiv {f : E → F} (hf : Sym A w m (N + 1) K f) : Sym A w (m - 1) N K (fderiv ℝ f) := by
  refine ⟨hf.1.fderiv_right (by norm_cast), fun x hx i hi => ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  have h := hf.2 x hx (i + 1) (Nat.succ_le_succ hi)
  have e : m - ((i + 1 : ℕ) : ℤ) = m - 1 - (i : ℤ) := by push_cast; ring
  rwa [e] at h

theorem Sym.comp_clm {f : E → F} (T : F →L[ℝ] G) (hf : Sym A w m N K f) :
    Sym A w m N (‖T‖ * K) (fun x => T (f x)) := by
  refine ⟨T.contDiff.comp hf.1, fun x hx i hi => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ i (fun x => T (f x)) x‖ ≤ ‖T‖ * ‖iteratedFDeriv ℝ i f x‖ :=
    T.norm_iteratedFDeriv_comp_left (A_cda hf.1 hi x) le_rfl
  rw [mul_assoc]
  exact h1.trans (mul_le_mul_of_nonneg_left (hf.2 x hx i hi) (norm_nonneg T))

theorem Sym.clm_apply {L : E → G →L[ℝ] F} (v : G) (hL : Sym A w m N K L) :
    Sym A w m N (K * ‖v‖) (fun x => L x v) := by
  refine ⟨hL.1.clm_apply contDiff_const, fun x hx i hi => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ i (fun x => L x v) x‖ ≤
      ‖ContinuousLinearMap.apply ℝ F v‖ * ‖iteratedFDeriv ℝ i L x‖ :=
    (ContinuousLinearMap.apply ℝ F v).norm_iteratedFDeriv_comp_left (A_cda hL.1 hi x) le_rfl
  have h2 : ‖ContinuousLinearMap.apply ℝ F v‖ ≤ ‖v‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun T => ?_
    rw [ContinuousLinearMap.apply_apply, mul_comm]
    exact T.le_opNorm v
  calc ‖iteratedFDeriv ℝ i (fun x => L x v) x‖
      ≤ ‖v‖ * ‖iteratedFDeriv ℝ i L x‖ := h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _ ≤ ‖v‖ * (K * w x ^ (m - (i : ℤ))) := mul_le_mul_of_nonneg_left (hL.2 x hx i hi) (norm_nonneg v)
    _ = K * ‖v‖ * w x ^ (m - (i : ℤ)) := by ring

theorem Sym.const (c : F) (hK : 0 ≤ K) (hw : ∀ x ∈ A, 0 < w x) (h : ∀ x ∈ A, ‖c‖ ≤ K * w x ^ m) :
    Sym A w m N K (fun _ : E => c) := by
  refine ⟨contDiff_const, fun x hx i _ => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [norm_iteratedFDeriv_zero]
    simpa using h x hx
  · rw [iteratedFDeriv_const_of_ne hi.ne']
    simpa using mul_nonneg hK (zpow_pos (hw x hx) _).le

theorem Sym.lower {f : E → F} {W : ℝ} (p : ℕ) (hw : ∀ x ∈ A, 0 < w x) (hW : ∀ x ∈ A, w x ≤ W)
    (hf : Sym A w (m + p) N K f) : Sym A w m N (K * W ^ p) f := by
  refine ⟨hf.1, fun x hx i hi => ?_⟩
  have hK := A_const_nonneg hw hf hx
  have hwx := hw x hx
  have e : w x ^ (m + (p : ℤ) - (i : ℤ)) = w x ^ (m - (i : ℤ)) * w x ^ p := by
    rw [← zpow_natCast, ← zpow_add₀ hwx.ne']
    congr 1
    ring
  calc ‖iteratedFDeriv ℝ i f x‖ ≤ K * w x ^ (m + (p : ℤ) - (i : ℤ)) := hf.2 x hx i hi
    _ = K * w x ^ p * w x ^ (m - (i : ℤ)) := by rw [e]; ring
    _ ≤ K * W ^ p * w x ^ (m - (i : ℤ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hwx.le (hW x hx) p) hK) (zpow_pos hwx _).le

theorem Sym.raise {f : E → F} {w₀ : ℝ} (p : ℕ) (hw₀ : 0 < w₀) (hW : ∀ x ∈ A, w₀ ≤ w x)
    (hf : Sym A w m N K f) : Sym A w (m + p) N (K / w₀ ^ p) f := by
  have hw : ∀ x ∈ A, 0 < w x := fun x hx => hw₀.trans_le (hW x hx)
  refine ⟨hf.1, fun x hx i hi => ?_⟩
  have hK := A_const_nonneg hw hf hx
  have hwx := hw x hx
  have e : w x ^ (m + (p : ℤ) - (i : ℤ)) = w x ^ (m - (i : ℤ)) * w x ^ p := by
    rw [← zpow_natCast, ← zpow_add₀ hwx.ne']
    congr 1
    ring
  have h1 : 1 ≤ w x ^ p / w₀ ^ p := by
    rw [le_div_iff₀ (pow_pos hw₀ p), one_mul]
    exact pow_le_pow_left₀ hw₀.le (hW x hx) p
  calc ‖iteratedFDeriv ℝ i f x‖ ≤ K * w x ^ (m - (i : ℤ)) := hf.2 x hx i hi
    _ = K * w x ^ (m - (i : ℤ)) * 1 := by ring
    _ ≤ K * w x ^ (m - (i : ℤ)) * (w x ^ p / w₀ ^ p) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hK (zpow_pos hwx _).le)
    _ = K / w₀ ^ p * w x ^ (m + (p : ℤ) - (i : ℤ)) := by rw [e]; ring

theorem A_fderiv_inv {f : E → ℝ} (hf : Differentiable ℝ f) (hpos : ∀ x, 0 < f x) :
    fderiv ℝ (fun x => (f x)⁻¹) = fun x => -(((f x)⁻¹ * (f x)⁻¹) • fderiv ℝ f x) := by
  funext x
  have h := (hasDerivAt_inv (hpos x).ne').comp_hasFDerivAt x (hf x).hasFDerivAt
  have h2 : HasFDerivAt (fun x => (f x)⁻¹) ((-(f x ^ 2)⁻¹) • fderiv ℝ f x) x := h
  rw [h2.fderiv, neg_smul, sq, mul_inv]

theorem Sym.inv (N : ℕ) (K c : ℝ) (hc : 0 < c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Set E) (w : E → ℝ) (f : E → ℝ),
    (∀ x ∈ A, 0 < w x) → Sym A w 2 N K f → (∀ x, 0 < f x) → (∀ x ∈ A, c * w x ^ 2 ≤ f x) →
    Sym A w (-2) N C (fun x => (f x)⁻¹) := by
  have hzero : ∀ (A : Set E) (w : E → ℝ) (f : E → ℝ), (∀ x ∈ A, 0 < w x) → (∀ x, 0 < f x) →
      (∀ x ∈ A, c * w x ^ 2 ≤ f x) → ∀ x ∈ A, ‖(f x)⁻¹‖ ≤ c⁻¹ * w x ^ (-2 : ℤ) := by
    intro A w f hw hpos hlow x hx
    have hwx := hw x hx
    rw [Real.norm_of_nonneg (inv_pos.2 (hpos x)).le]
    have h1 : (f x)⁻¹ ≤ (c * w x ^ 2)⁻¹ := inv_anti₀ (by positivity) (hlow x hx)
    refine h1.trans (le_of_eq ?_)
    rw [mul_inv, zpow_neg]
    norm_cast
  induction N with
  | zero =>
    refine ⟨c⁻¹, (inv_pos.2 hc).le, fun A w f hw hf hpos hlow => ?_⟩
    refine ⟨hf.1.inv fun x => (hpos x).ne', fun x hx i hi => ?_⟩
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    rw [norm_iteratedFDeriv_zero]
    simpa using hzero A w f hw hpos hlow x hx
  | succ N ih =>
    obtain ⟨C, hC, ih⟩ := ih
    refine ⟨max c⁻¹ (2 ^ N * (2 ^ N * C * C) * K), le_max_of_le_left (inv_pos.2 hc).le,
      fun A w f hw hf hpos hlow => ?_⟩
    refine ⟨hf.1.inv fun x => (hpos x).ne', fun x hx i hi => ?_⟩
    have hwx := hw x hx
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [norm_iteratedFDeriv_zero]
      refine (hzero A w f hw hpos hlow x hx).trans ?_
      simpa using mul_le_mul_of_nonneg_right (le_max_left c⁻¹ (2 ^ N * (2 ^ N * C * C) * K))
        (zpow_pos hwx (-2 : ℤ)).le
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j ≤ N := Nat.succ_le_succ_iff.1 hi
      have hg := ih A w f hw (hf.mono hw (Nat.le_succ N) le_rfl) hpos hlow
      have hd : Differentiable ℝ f := hf.1.differentiable (by norm_cast)
      have hS := ((hg.mul hw hg).smul hw hf.fderiv).neg
      rw [← norm_iteratedFDeriv_fderiv, A_fderiv_inv hd hpos]
      have h := hS.2 x hx j hj
      have e : (-2 + -2 + (2 - 1) - (j : ℤ)) = -2 - ((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zpow_pos hwx _).le)

theorem iteratedFDeriv_vanishing_bound {f : E → F} {r M : ℝ} (p : ℕ) (hp : p ≤ N) (hf : ContDiff ℝ N f)
    (hM : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ N → ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (h0 : ∀ i : ℕ, i < p → iteratedFDeriv ℝ i f 0 = 0) (k : ℕ) (hk : k ≤ p) :
    ∀ x ∈ Metric.closedBall (0 : E) r, ‖iteratedFDeriv ℝ (p - k) f x‖ ≤ M * ‖x‖ ^ k := by
  induction k with
  | zero =>
    intro x hx
    simpa using hM x hx p hp
  | succ k ih =>
    intro x hx
    have ih := ih (Nat.le_of_succ_le hk)
    have hxr : ‖x‖ ≤ r := by simpa using hx
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx 0 (Nat.zero_le _))
    have e : p - (k + 1) + 1 = p - k := by omega
    have hlt : p - (k + 1) < N := by omega
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ (p - (k + 1)) f) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast hlt)
    have hb : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖,
        ‖fderiv ℝ (iteratedFDeriv ℝ (p - (k + 1)) f) y‖ ≤ M * ‖x‖ ^ k := by
      intro y hy
      have hyx : ‖y‖ ≤ ‖x‖ := by simpa using hy
      rw [norm_fderiv_iteratedFDeriv, e]
      refine (ih y (by simpa using hyx.trans hxr)).trans ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) hyx k) hM0
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun y _ => hdiff y) hb
      (convex_closedBall (0 : E) ‖x‖) (by simp : (0 : E) ∈ Metric.closedBall (0 : E) ‖x‖)
      (by simp : x ∈ Metric.closedBall (0 : E) ‖x‖)
    rw [h0 _ (by omega), sub_zero, sub_zero] at h
    rw [pow_succ, ← mul_assoc]
    exact h

theorem Sym.of_vanish {f : E → F} {r σ M : ℝ} (p : ℕ) (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hp : p ≤ N)
    (hf : ContDiff ℝ N f)
    (hM : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ N → ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (h0 : ∀ i : ℕ, i < p → iteratedFDeriv ℝ i f 0 = 0) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) p N (M * (r + 1) ^ N) f := by
  refine ⟨hf, fun x hx i hi => ?_⟩
  have hxr : ‖x‖ ≤ r := by simpa using hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx 0 (Nat.zero_le _))
  have hwpos : 0 < wt σ x := by unfold wt; positivity
  have hwle : wt σ x ≤ r + 1 := by unfold wt; linarith
  have hr1 : (1 : ℝ) ≤ r + 1 := by linarith
  rcases lt_or_ge i p with hip | hip
  · have h := iteratedFDeriv_vanishing_bound p hp hf hM h0 (p - i) (Nat.sub_le _ _) x hx
    have e1 : p - (p - i) = i := by omega
    rw [e1] at h
    have e2 : wt σ x ^ ((p : ℤ) - (i : ℤ)) = wt σ x ^ (p - i) := by
      rw [← zpow_natCast]
      congr 1
      push_cast [hip.le]
      ring
    rw [e2]
    calc ‖iteratedFDeriv ℝ i f x‖ ≤ M * ‖x‖ ^ (p - i) := h
      _ ≤ M * wt σ x ^ (p - i) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) (by unfold wt; linarith) _) hM0
      _ = M * 1 * wt σ x ^ (p - i) := by ring
      _ ≤ M * (r + 1) ^ N * wt σ x ^ (p - i) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (one_le_pow₀ hr1) hM0)
            (pow_pos hwpos _).le
  · have e2 : wt σ x ^ ((p : ℤ) - (i : ℤ)) = (wt σ x ^ (i - p))⁻¹ := by
      rw [← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast [hip]
      ring
    rw [e2]
    have h1 : wt σ x ^ (i - p) ≤ (r + 1) ^ N :=
      (pow_le_pow_left₀ hwpos.le hwle _).trans (pow_le_pow_right₀ hr1 ((Nat.sub_le _ _).trans hi))
    have h2 : 1 ≤ (r + 1) ^ N * (wt σ x ^ (i - p))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hwpos _), one_mul]
      exact h1
    calc ‖iteratedFDeriv ℝ i f x‖ ≤ M := hM x hx i hi
      _ = M * 1 := by ring
      _ ≤ M * ((r + 1) ^ N * (wt σ x ^ (i - p))⁻¹) := mul_le_mul_of_nonneg_left h2 hM0
      _ = M * (r + 1) ^ N * (wt σ x ^ (i - p))⁻¹ := by ring

theorem Sym.clm (L : E →L[ℝ] F) {σ : ℝ} (hσ : 0 < σ) : Sym A (wt σ) 1 N ‖L‖ (fun x => L x) := by
  refine ⟨L.contDiff, fun x _ i _ => ?_⟩
  have hwpos : 0 < wt σ x := by unfold wt; positivity
  match i with
  | 0 =>
    rw [norm_iteratedFDeriv_zero]
    have : wt σ x ^ ((1 : ℤ) - ((0 : ℕ) : ℤ)) = wt σ x := by simp
    rw [this]
    refine (L.le_opNorm x).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg L))
    unfold wt
    linarith
  | 1 =>
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
    have h1 : _root_.fderiv ℝ (fun x => L x) x = L := L.fderiv
    rw [h1]
    simp
  | j + 2 =>
    rw [← norm_iteratedFDeriv_fderiv]
    have h1 : _root_.fderiv ℝ (fun x => L x) = fun _ => L := by
      funext y
      exact L.fderiv
    rw [h1, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
    simpa using mul_nonneg (norm_nonneg L) (zpow_pos hwpos _).le

end SymCalc

end Formalism.FourierDecayAlt.P.StationaryPhaseModel

end PartA

section PartB

open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel

theorem isAddHaar_muPi (d : ℕ) (β : ℂ) (hβ : β ≠ 0) : (muPi β (Fin d)).IsAddHaarMeasure := by
  have hc : Real.toNNReal (‖β‖ / (2 * Real.pi)) ≠ 0 := by
    have : 0 < ‖β‖ / (2 * Real.pi) := div_pos (norm_pos_iff.2 hβ) (by positivity)
    exact (Real.toNNReal_pos.2 this).ne'
  have : (mu β).IsAddHaarMeasure := by
    unfold mu
    exact Measure.IsAddHaarMeasure.nnreal_smul _ hc
  unfold muPi
  infer_instance

theorem B_finrank (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem B_weight (d : ℕ) (β : ℂ) (hβ : β ≠ 0) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ σ : ℝ, 0 < σ →
    Integrable (fun x : Fin d → ℂ => wt σ x ^ (-(2 * (d : ℤ) + 2))) (muPi β (Fin d)) ∧
    ∫ x : Fin d → ℂ, wt σ x ^ (-(2 * (d : ℤ) + 2)) ∂(muPi β (Fin d)) ≤ C₀ / σ ^ 2 := by
  have := isAddHaar_muPi d β hβ
  have hI : Integrable (fun x : Fin d → ℂ => (1 + ‖x‖) ^ (-(2 * (d : ℤ) + 2))) (muPi β (Fin d)) := by
    have h := integrable_one_add_norm (E := Fin d → ℂ) (μ := muPi β (Fin d)) (r := ((2 * (d : ℤ) + 2 : ℤ) : ℝ))
      (by rw [B_finrank]; push_cast; linarith)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  refine ⟨∫ x : Fin d → ℂ, (1 + ‖x‖) ^ (-(2 * (d : ℤ) + 2)) ∂(muPi β (Fin d)),
    integral_nonneg fun x => by positivity, fun σ hσ => ?_⟩
  have hEq : (fun x : Fin d → ℂ => wt σ x ^ (-(2 * (d : ℤ) + 2))) =
      fun x => σ ^ (-(2 * (d : ℤ) + 2)) * (fun y : Fin d → ℂ => (1 + ‖y‖) ^ (-(2 * (d : ℤ) + 2))) (σ⁻¹ • x) := by
    funext x
    simp only [wt]
    rw [← mul_zpow, norm_smul, norm_inv, Real.norm_of_nonneg hσ.le]
    congr 1
    field_simp
    ring
  constructor
  · rw [hEq]
    exact (hI.comp_smul (inv_ne_zero hσ.ne')).const_mul _
  · have hsc := Measure.integral_comp_inv_smul (muPi β (Fin d))
      (fun y : Fin d → ℂ => (1 + ‖y‖) ^ (-(2 * (d : ℤ) + 2))) σ
    rw [hEq, integral_const_mul, hsc, B_finrank, abs_of_pos (by positivity), smul_eq_mul,
      ← mul_assoc]
    apply le_of_eq
    rw [div_eq_mul_inv, mul_comm]
    congr 1
    rw [zpow_neg, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_neg, ← zpow_add₀ hσ.ne']
    congr 1
    push_cast
    ring

theorem B_norm_osc {E : Type*} (φ : E → ℝ) (τ : ℝ) (x : E) : ‖osc φ τ x‖ = 1 := by
  unfold osc
  exact Complex.norm_exp_I_mul_ofReal _

section IBP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem B_hasFDerivAt_osc {φ : E → ℝ} (τ : ℝ) {x : E} (hφ : DifferentiableAt ℝ φ x) :
    HasFDerivAt (osc φ τ)
      ((Complex.I * osc φ τ x) • (Complex.ofRealCLM.comp (τ⁻¹ • fderiv ℝ φ x))) x := by
  unfold osc
  have h1 : HasFDerivAt (fun y => ((φ y / τ : ℝ) : ℂ)) (Complex.ofRealCLM.comp (τ⁻¹ • fderiv ℝ φ x)) x := by
    have h2 : HasFDerivAt (fun y => φ y / τ) (τ⁻¹ • fderiv ℝ φ x) x := by
      simpa [div_eq_inv_mul] using hφ.hasFDerivAt.const_mul τ⁻¹
    exact Complex.ofRealCLM.hasFDerivAt.comp x h2
  have h3 := (h1.const_mul Complex.I).cexp
  convert h3 using 1
  rw [smul_smul, mul_comm Complex.I]

theorem B_contDiff_osc {φ : E → ℝ} (τ : ℝ) {n : ℕ} (hφ : ContDiff ℝ n φ) : ContDiff ℝ n (osc φ τ) := by
  unfold osc
  have h1 : ContDiff ℝ n (fun y => ((φ y / τ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.div_const τ)
  exact (contDiff_const.mul h1).cexp

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem B_ibp {φ : E → ℝ} (τ : ℝ) (hφ : ContDiff ℝ 1 φ) {c : E → V} (hc : ContDiff ℝ 1 c)
    (hcs : HasCompactSupport c) (v : E) :
    ∫ x, osc φ τ x • fderiv ℝ c x v ∂μ =
      -∫ x, (Complex.I * osc φ τ x * ((τ⁻¹ * fderiv ℝ φ x v : ℝ) : ℂ)) • c x ∂μ := by
  have hoc : Continuous (osc φ τ) := (B_contDiff_osc τ hφ).continuous
  have hφ' : Continuous (fun x => fderiv ℝ φ x v) := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hc' : Continuous (fun x => fderiv ℝ c x v) := (hc.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := μ)
    (f := osc φ τ) (f' := fun x => Complex.I * osc φ τ x * ((τ⁻¹ * fderiv ℝ φ x v : ℝ) : ℂ))
    (g := c) (g' := fun x => fderiv ℝ c x v) (v := v) (B := ContinuousLinearMap.lsmul ℝ ℂ) ?_ ?_ ?_ ?_ ?_
  · simpa using key
  · simp only [ContinuousLinearMap.lsmul_apply]
    refine Continuous.integrable_of_hasCompactSupport ?_ hcs.smul_left
    exact Continuous.smul (by fun_prop) hc.continuous
  · simp only [ContinuousLinearMap.lsmul_apply]
    refine Continuous.integrable_of_hasCompactSupport (hoc.smul hc') (hcs.fderiv_apply ℝ v).smul_left
  · simp only [ContinuousLinearMap.lsmul_apply]
    exact Continuous.integrable_of_hasCompactSupport (hoc.smul hc.continuous) hcs.smul_left
  · intro x _
    have h := (B_hasFDerivAt_osc τ ((hφ.differentiable (by norm_num)) x)).hasLineDerivAt v
    convert h using 1
    simp [mul_assoc]
  · intro x _
    exact ((hc.differentiable (by norm_num)) x).hasFDerivAt.hasLineDerivAt v

end IBP

section Step

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem B_cast {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {A : Set E} {w : E → ℝ} {m m' : ℤ} {N : ℕ}
    {K K' : ℝ} {f : E → F} (h : Sym A w m N K f) (hm : m = m') (hK : K = K') : Sym A w m' N K' f := by
  subst hm; subst hK; exact h

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem B_step (ι : Type) [Fintype ι] (N : ℕ) (Γ c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C₁ : ℝ, 0 ≤ C₁ ∧
    ∀ (v : ι → E), (∀ l, ‖v l‖ = 1) → ∀ (A : Set E) (w : E → ℝ) (φ : E → ℝ) (τ : ℝ), 0 < τ →
      (∀ x ∈ A, 0 < w x) → (∀ x ∈ A, τ ≤ w x ^ 2) → ContDiff ℝ 1 φ → Sym A w 1 (N + 1) Γ (fderiv ℝ φ) →
      (∀ x ∈ A, c₀ * w x ^ 2 ≤ ∑ l, (fderiv ℝ φ x (v l)) ^ 2 + τ) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (b : E → V) (m : ℤ) (K : ℝ),
        HasCompactSupport b → tsupport b ⊆ A → Sym A w m (N + 1) K b →
        ∃ b' : E → V, HasCompactSupport b' ∧ tsupport b' ⊆ A ∧ Sym A w (m - 2) N (C₁ * τ * K) b' ∧
          ∫ x, osc φ τ x • b x ∂μ = ∫ x, osc φ τ x • b' x ∂μ := by
  obtain ⟨Ch, hCh0, hCh⟩ := Sym.inv (E := E) (N + 1) ((∑ _l : ι, 2 ^ (N + 1) * |Γ| * |Γ|) + 1) c₀ hc₀
  refine ⟨(Fintype.card ι : ℝ) * (2 ^ (N + 1) * (2 ^ (N + 1) * |Γ| * Ch)) + 2 ^ (N + 1) * Ch, by positivity, ?_⟩
  intro v hv A w φ τ hτ hw hτw hφ hφS hD V _ _ b m K hbs hbA hb
  set p : ι → E → ℝ := fun l x => fderiv ℝ φ x (v l) with hpdef
  set h : E → ℝ := fun x => (∑ l, p l x * p l x + τ)⁻¹ with hhdef
  have hp : ∀ l, Sym A w 1 (N + 1) |Γ| (p l) := fun l => by
    have := (hφS.mono hw le_rfl (le_abs_self Γ)).clm_apply (v l)
    rwa [hv l, mul_one] at this
  have hsum : Sym A w (1 + 1) (N + 1) (∑ _l : ι, 2 ^ (N + 1) * |Γ| * |Γ|) (fun x => ∑ l, p l x * p l x) :=
    Sym.sum Finset.univ (fun l _ => Sym.mul hw (hp l) (hp l))
  have hτS : Sym A w (1 + 1) (N + 1) 1 (fun _ : E => τ) :=
    Sym.const τ zero_le_one hw (fun x hx => by
      rw [Real.norm_of_nonneg hτ.le, one_mul]
      have : w x ^ ((1 : ℤ) + 1) = w x ^ 2 := by norm_num
      rw [this]; exact hτw x hx)
  have hDS : Sym A w 2 (N + 1) ((∑ _l : ι, 2 ^ (N + 1) * |Γ| * |Γ|) + 1) (fun x => ∑ l, p l x * p l x + τ) :=
    B_cast (hsum.add hτS) (by norm_num) rfl
  have hpos : ∀ x, 0 < ∑ l, p l x * p l x + τ := fun x =>
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun l _ => mul_self_nonneg _) hτ
  have hh : Sym A w (-2) (N + 1) Ch h := hCh A w _ hw hDS hpos (fun x hx => by
    have := hD x hx
    simpa [hpdef, sq] using this)
  have he : ∀ l, Sym A w (1 + -2) (N + 1) (2 ^ (N + 1) * |Γ| * Ch) (fun x => p l x * h x) :=
    fun l => Sym.mul hw (hp l) hh
  set c : ι → E → V := fun l x => (p l x * h x) • b x with hcdef
  have hc : ∀ l, Sym A w (1 + -2 + m) (N + 1) (2 ^ (N + 1) * (2 ^ (N + 1) * |Γ| * Ch) * K) (c l) :=
    fun l => Sym.smul hw (he l) hb
  have hhb : Sym A w (-2 + m) (N + 1) (2 ^ (N + 1) * Ch * K) (fun x => h x • b x) := Sym.smul hw hh hb
  have hS1 := (Sym.sum Finset.univ (fun l _ => ((hc l).fderiv.clm_apply (v l)))).const_smul_complex
    (Complex.I * (τ : ℂ))
  have hS2 := (hhb.mono hw (Nat.le_succ N) le_rfl).const_smul τ
  have hnI : ‖Complex.I * (τ : ℂ)‖ = τ := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  have hsupp : Function.support
      (fun x => (Complex.I * (τ : ℂ)) • ∑ l, fderiv ℝ (c l) x (v l) + τ • (h x • b x)) ⊆ tsupport b := by
    intro x hx
    by_contra hxb
    apply hx
    have hb0 : b =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hxb
    have hc0 : ∀ l, c l =ᶠ[𝓝 x] 0 := fun l => hb0.mono (fun y hy => by simp [hcdef, hy])
    have hf0 : ∀ l, fderiv ℝ (c l) x = 0 := fun l => by
      rw [(hc0 l).fderiv_eq]
      simp
    have hbx : b x = 0 := hb0.self_of_nhds
    simp [hf0, hbx]
  refine ⟨fun x => (Complex.I * (τ : ℂ)) • ∑ l, fderiv ℝ (c l) x (v l) + τ • (h x • b x), hbs.mono' hsupp,
    (closure_minimal hsupp (isClosed_tsupport _)).trans hbA, ?_, ?_⟩
  · refine B_cast ((B_cast hS1 (by ring) rfl).add (B_cast hS2 (by ring) rfl)) rfl ?_
    simp only [hnI, hv, abs_of_pos hτ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  · have hoc : Continuous (osc φ τ) := (B_contDiff_osc τ hφ).continuous
    have hc1 : ∀ l, ContDiff ℝ 1 (c l) := fun l => (hc l).1.of_le (by norm_cast; omega)
    have hccs : ∀ l, HasCompactSupport (c l) := fun l => hbs.smul_left
    have hpc : ∀ l, Continuous (p l) := fun l => (hp l).1.continuous
    have hI1 : ∀ l, Integrable (fun x => (Complex.I * (τ : ℂ)) • (osc φ τ x • fderiv ℝ (c l) x (v l))) μ := fun l =>
      (Continuous.integrable_of_hasCompactSupport
        (hoc.smul (((hc1 l).continuous_fderiv (by norm_num)).clm_apply continuous_const))
        ((hccs l).fderiv_apply ℝ (v l)).smul_left).smul _
    have hI2 : Integrable (fun x => osc φ τ x • (τ • (h x • b x))) μ :=
      Continuous.integrable_of_hasCompactSupport
        (hoc.smul (continuous_const.smul (hhb.1.continuous))) (hbs.smul_left.smul_left).smul_left
    have hI3 : ∀ l, Integrable (fun x => (Complex.I * (τ : ℂ)) •
        ((Complex.I * osc φ τ x * ((τ⁻¹ * p l x : ℝ) : ℂ)) • c l x)) μ := fun l =>
      (Continuous.integrable_of_hasCompactSupport
        (Continuous.smul (by have := hpc l; fun_prop) (hc1 l).continuous) (hccs l).smul_left).smul _
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    symm
    calc ∫ x, osc φ τ x • ((Complex.I * (τ : ℂ)) • ∑ l, fderiv ℝ (c l) x (v l) + τ • (h x • b x)) ∂μ
        = ∫ x, (∑ l, (Complex.I * (τ : ℂ)) • (osc φ τ x • fderiv ℝ (c l) x (v l))) +
            osc φ τ x • (τ • (h x • b x)) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [smul_add, Finset.smul_sum]
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [smul_comm]
      _ = (∑ l, (Complex.I * (τ : ℂ)) • ∫ x, osc φ τ x • fderiv ℝ (c l) x (v l) ∂μ) +
            ∫ x, osc φ τ x • (τ • (h x • b x)) ∂μ := by
          rw [integral_add (integrable_finsetSum _ fun l _ => hI1 l) hI2, integral_finsetSum _ fun l _ => hI1 l]
          simp_rw [integral_smul]
      _ = (∑ l, -∫ x, (Complex.I * (τ : ℂ)) • ((Complex.I * osc φ τ x * ((τ⁻¹ * p l x : ℝ) : ℂ)) • c l x) ∂μ) +
            ∫ x, osc φ τ x • (τ • (h x • b x)) ∂μ := by
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [B_ibp τ hφ (hc1 l) (hccs l) (v l), smul_neg, integral_smul]
      _ = ∫ x, (∑ l, -((Complex.I * (τ : ℂ)) • ((Complex.I * osc φ τ x * ((τ⁻¹ * p l x : ℝ) : ℂ)) • c l x))) +
            osc φ τ x • (τ • (h x • b x)) ∂μ := by
          have hI3n : ∀ l, Integrable (fun x => -((Complex.I * (τ : ℂ)) •
              ((Complex.I * osc φ τ x * ((τ⁻¹ * p l x : ℝ) : ℂ)) • c l x))) μ := fun l => (hI3 l).neg
          rw [integral_add (integrable_finsetSum _ fun l _ => hI3n l) hI2,
            integral_finsetSum _ fun l _ => hI3n l]
          simp_rw [integral_neg]
      _ = ∫ x, osc φ τ x • b x ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [hcdef, ← Complex.coe_smul, smul_smul, ← neg_smul, ← Finset.sum_smul, ← add_smul]
          congr 1
          have hterm : ∀ l, -(Complex.I * (τ : ℂ) * (Complex.I * osc φ τ x * ((τ⁻¹ * p l x : ℝ) : ℂ) *
              ((p l x * h x : ℝ) : ℂ))) = osc φ τ x * (h x : ℂ) * ((p l x * p l x : ℝ) : ℂ) := fun l => by
            push_cast
            calc -(Complex.I * (τ : ℂ) * (Complex.I * osc φ τ x * ((τ : ℂ)⁻¹ * (p l x : ℂ)) *
                  ((p l x : ℂ) * (h x : ℂ))))
                = -(Complex.I * Complex.I) * ((τ : ℂ) * (τ : ℂ)⁻¹) *
                  (osc φ τ x * (h x : ℂ) * ((p l x : ℂ) * (p l x : ℂ))) := by ring
              _ = _ := by rw [Complex.I_mul_I, mul_inv_cancel₀ hτc]; ring
          simp_rw [hterm]
          rw [← Finset.mul_sum, ← Complex.ofReal_sum]
          have hh1 : h x * (∑ l, p l x * p l x + τ) = 1 := inv_mul_cancel₀ (hpos x).ne'
          have hh2 : (h x : ℂ) * (((∑ l, p l x * p l x : ℝ) : ℂ) + (τ : ℂ)) = 1 := by exact_mod_cast hh1
          calc osc φ τ x * (h x : ℂ) * ((∑ l, p l x * p l x : ℝ) : ℂ) + osc φ τ x * ((τ : ℂ) * (h x : ℂ))
              = osc φ τ x * ((h x : ℂ) * (((∑ l, p l x * p l x : ℝ) : ℂ) + (τ : ℂ))) := by ring
            _ = osc φ τ x := by rw [hh2, mul_one]

end Step

section Reduce

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem B_reduce (ι : Type) [Fintype ι] (n : ℕ) (Γ c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (v : ι → E), (∀ l, ‖v l‖ = 1) → ∀ (A : Set E) (w : E → ℝ) (φ : E → ℝ) (τ : ℝ), 0 < τ →
      (∀ x ∈ A, 0 < w x) → (∀ x ∈ A, τ ≤ w x ^ 2) → ContDiff ℝ 1 φ → Sym A w 1 n Γ (fderiv ℝ φ) →
      (∀ x ∈ A, c₀ * w x ^ 2 ≤ ∑ l, (fderiv ℝ φ x (v l)) ^ 2 + τ) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (b : E → V) (m : ℤ) (K : ℝ),
        HasCompactSupport b → tsupport b ⊆ A → Sym A w m n K b →
        ∃ b' : E → V, HasCompactSupport b' ∧ tsupport b' ⊆ A ∧ Sym A w (m - 2 * (n : ℤ)) 0 (C * τ ^ n * K) b' ∧
          ∫ x, osc φ τ x • b x ∂μ = ∫ x, osc φ τ x • b' x ∂μ := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro v _ A w φ τ _ _ _ _ _ _ V _ _ b m K hbs hbA hb
    exact ⟨b, hbs, hbA, B_cast hb (by simp) (by simp), rfl⟩
  | succ n ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    obtain ⟨C₁, hC₁0, hC₁⟩ := B_step (E := E) (μ := μ) ι n Γ c₀ hc₀
    refine ⟨C * C₁, mul_nonneg hC0 hC₁0, ?_⟩
    intro v hv A w φ τ hτ hw hτw hφ hφS hD V _ _ b m K hbs hbA hb
    obtain ⟨b₁, hb₁s, hb₁A, hb₁S, hEq₁⟩ := hC₁ v hv A w φ τ hτ hw hτw hφ hφS hD V b m K hbs hbA hb
    obtain ⟨b₂, hb₂s, hb₂A, hb₂S, hEq₂⟩ := hC v hv A w φ τ hτ hw hτw hφ
      (hφS.mono hw (Nat.le_succ n) le_rfl) hD V b₁ (m - 2) (C₁ * τ * K) hb₁s hb₁A hb₁S
    refine ⟨b₂, hb₂s, hb₂A, B_cast hb₂S (by push_cast; ring) (by ring), hEq₁.trans hEq₂⟩

end Reduce

theorem B_norm_dirv {d : ℕ} (l : Fin d × Bool) : ‖dirv l‖ = 1 := by
  unfold dirv
  rw [Pi.norm_single]
  split_ifs <;> simp

theorem osc_bound (d q : ℕ) (β : ℂ) (hβ : β ≠ 0) (Γ c₁ : ℝ) (hc₁ : 0 < c₁) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : Set (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ) (τ : ℝ), 0 < τ →
      ContDiff ℝ (d + 2 + q : ℕ) φ →
      Sym A (wt (Real.sqrt τ)) 1 (d + 1 + q) Γ (fderiv ℝ φ) →
      (∀ x ∈ A, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b : (Fin d → ℂ) → V) (K : ℝ),
        0 ≤ K → HasCompactSupport b → tsupport b ⊆ A →
        Sym A (wt (Real.sqrt τ)) (2 * (q : ℤ)) (d + 1 + q) K b →
        ‖∫ x, osc φ τ x • b x ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + q) := by
  have := isAddHaar_muPi d β hβ
  have hmin : 0 < min (c₁ ^ 2) 1 := lt_min (by positivity) one_pos
  obtain ⟨C, hC0, hC⟩ := B_reduce (E := Fin d → ℂ) (μ := muPi β (Fin d)) (Fin d × Bool) (d + 1 + q) Γ
    (min (c₁ ^ 2) 1 / 2) (by positivity)
  obtain ⟨C₀, hC₀0, hC₀⟩ := B_weight d β hβ
  refine ⟨C * C₀, mul_nonneg hC0 hC₀0, ?_⟩
  intro A φ τ hτ hφ hφS hlow V _ _ _ b K hK hbs hbA hb
  set σ := Real.sqrt τ with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hτ
  have hσ2 : σ ^ 2 = τ := Real.sq_sqrt hτ.le
  have hw : ∀ x ∈ A, 0 < wt σ x := fun x _ => by unfold wt; positivity
  have hτw : ∀ x ∈ A, τ ≤ wt σ x ^ 2 := fun x _ => by
    unfold wt; nlinarith [norm_nonneg x]
  have hD : ∀ x ∈ A, min (c₁ ^ 2) 1 / 2 * wt σ x ^ 2 ≤ ∑ l, (fderiv ℝ φ x (dirv l)) ^ 2 + τ := fun x hx => by
    obtain ⟨l, hl⟩ := hlow x hx
    have h1 : (c₁ * ‖x‖) ^ 2 ≤ (fderiv ℝ φ x (dirv l)) ^ 2 := by
      rw [← sq_abs (fderiv ℝ φ x (dirv l))]
      exact pow_le_pow_left₀ (by positivity) hl 2
    have h2 : (fderiv ℝ φ x (dirv l)) ^ 2 ≤ ∑ l, (fderiv ℝ φ x (dirv l)) ^ 2 :=
      Finset.single_le_sum (f := fun l => (fderiv ℝ φ x (dirv l)) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ l)
    have h3 : wt σ x ^ 2 ≤ 2 * (‖x‖ ^ 2 + σ ^ 2) := by
      unfold wt; nlinarith [sq_nonneg (‖x‖ - σ)]
    have h4 : min (c₁ ^ 2) 1 * ‖x‖ ^ 2 ≤ c₁ ^ 2 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
    have h5 : min (c₁ ^ 2) 1 * σ ^ 2 ≤ 1 * σ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    have h6 : min (c₁ ^ 2) 1 / 2 * wt σ x ^ 2 ≤ min (c₁ ^ 2) 1 / 2 * (2 * (‖x‖ ^ 2 + σ ^ 2)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith
  obtain ⟨b', hb's, hb'A, hb'S, hEq⟩ := hC dirv B_norm_dirv A (wt σ) φ τ hτ hw hτw
    (hφ.of_le (by norm_cast; omega)) hφS hD V b (2 * (q : ℤ)) K hbs hbA hb
  rw [hEq]
  obtain ⟨hInt, hle⟩ := hC₀ σ hσ
  have hK' : 0 ≤ C * τ ^ (d + 1 + q) * K := by positivity
  have hbd : ∀ x, ‖osc φ τ x • b' x‖ ≤ C * τ ^ (d + 1 + q) * K * wt σ x ^ (-(2 * (d : ℤ) + 2)) := fun x => by
    rw [norm_smul, B_norm_osc, one_mul]
    by_cases hx : x ∈ A
    · have h := hb'S.2 x hx 0 le_rfl
      rw [norm_iteratedFDeriv_zero] at h
      convert h using 3
      push_cast
      ring
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hb'A h)), norm_zero]
      have : 0 < wt σ x := by unfold wt; positivity
      positivity
  calc ‖∫ x, osc φ τ x • b' x ∂(muPi β (Fin d))‖
      ≤ ∫ x, C * τ ^ (d + 1 + q) * K * wt σ x ^ (-(2 * (d : ℤ) + 2)) ∂(muPi β (Fin d)) :=
        norm_integral_le_of_norm_le (hInt.const_mul _) (Eventually.of_forall hbd)
    _ = C * τ ^ (d + 1 + q) * K * ∫ x, wt σ x ^ (-(2 * (d : ℤ) + 2)) ∂(muPi β (Fin d)) := integral_const_mul _ _
    _ ≤ C * τ ^ (d + 1 + q) * K * (C₀ / σ ^ 2) := mul_le_mul_of_nonneg_left hle hK'
    _ = C * C₀ * K * τ ^ (d + q) := by
        rw [hσ2, show d + 1 + q = (d + q) + 1 by ring, pow_succ]
        field_simp

end Formalism.FourierDecayAlt.P.StationaryPhaseModel

end PartB

section PartC

open MeasureTheory Filter Topology Metric

namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel

section Holo

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem C_line_hasDerivAt {f : E → F} {y v : E} {ζ : ℂ} (h : DifferentiableAt ℂ f (y + ζ • v)) :
    HasDerivAt (fun z : ℂ => f (y + z • v)) (fderiv ℂ f (y + ζ • v) v) ζ := by
  have h1 : HasDerivAt (fun z : ℂ => y + z • v) v ζ := by
    simpa using ((hasDerivAt_id ζ).smul_const v).const_add y
  exact h.hasFDerivAt.comp_hasDerivAt ζ h1

theorem C_norm_fderiv_le {f : E → F} {y : E} {δ M : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (ball y δ)) (hM : ∀ z ∈ ball y δ, ‖f z‖ ≤ M) :
    ‖fderiv ℂ f y‖ ≤ M / δ := by
  first | exact Bl.general_b_fact_second_bis_form.goal1 .. | (apply Bl.general_b_fact_second_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_bis_form.goal1 <;> assumption)

theorem C_continuousOn_fderiv [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn ℂ f U) : ContinuousOn (fderiv ℂ f) U := by
  have := FiniteDimensional.proper ℂ E
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.1 hU x hx
  set ρ := ρ0 / 3 with hρ
  have hρpos : 0 < ρ := by positivity
  have hsub : closedBall x (2 * ρ) ⊆ U := (closedBall_subset_ball (by rw [hρ]; linarith)).trans hball
  have hdf : ∀ y ∈ U, DifferentiableAt ℂ f y := fun y hy => (hf y hy).differentiableAt (hU.mem_nhds hy)
  have huc : UniformContinuousOn f (closedBall x (2 * ρ)) :=
    (isCompact_closedBall x (2 * ρ)).uniformContinuousOn_of_continuous (hf.continuousOn.mono hsub)
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := Metric.uniformContinuousOn_iff.1 huc (ε * ρ / 2) (by positivity)
  refine ⟨min η ρ, lt_min hη hρpos, fun x' hx' => ?_⟩
  have hx'η : ‖x' - x‖ < η := by rw [← dist_eq_norm]; exact hx'.trans_le (min_le_left _ _)
  have hx'ρ : ‖x' - x‖ < ρ := by rw [← dist_eq_norm]; exact hx'.trans_le (min_le_right _ _)
  have hin1 : ∀ z ∈ ball x ρ, z ∈ closedBall x (2 * ρ) := fun z hz =>
    ball_subset_closedBall (ball_subset_ball (by linarith) hz)
  have hin2 : ∀ z ∈ ball x ρ, z + (x' - x) ∈ closedBall x (2 * ρ) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    rw [mem_ball, dist_eq_norm] at hz
    calc ‖z + (x' - x) - x‖ = ‖(z - x) + (x' - x)‖ := by congr 1; abel
      _ ≤ ‖z - x‖ + ‖x' - x‖ := norm_add_le _ _
      _ ≤ 2 * ρ := by linarith
  have hd2 : ∀ z ∈ ball x ρ, HasFDerivAt (fun z => f (z + (x' - x))) (fderiv ℂ f (z + (x' - x))) z := by
    intro z hz
    have := (hdf _ (hsub (hin2 z hz))).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const (x' - x))
    simpa [Function.comp_def] using this
  have hxx : x ∈ ball x ρ := mem_ball_self hρpos
  have hfd : fderiv ℂ (fun z => f (z + (x' - x)) - f z) x = fderiv ℂ f x' - fderiv ℂ f x := by
    have h0 : HasFDerivAt (fun z => f (z + (x' - x)) - f z)
        (fderiv ℂ f (x + (x' - x)) - fderiv ℂ f x) x := (hd2 x hxx).sub (hdf x hx).hasFDerivAt
    rw [h0.fderiv]; congr 2; abel
  rw [dist_eq_norm, ← hfd]
  have hle : ‖fderiv ℂ (fun z => f (z + (x' - x)) - f z) x‖ ≤ (ε * ρ / 2) / ρ := by
    refine C_norm_fderiv_le hρpos ?_ ?_
    · intro z hz
      exact ((hd2 z hz).differentiableAt.sub (hdf z (hsub (hin1 z hz)))).differentiableWithinAt
    · intro z hz
      rw [← dist_eq_norm]
      refine (hηε _ (hin2 z hz) _ (hin1 z hz) ?_).le
      rw [dist_eq_norm, add_sub_cancel_left]; exact hx'η
  have : (ε * ρ / 2) / ρ = ε / 2 := by field_simp
  rw [this] at hle
  linarith

theorem C_differentiableOn_fderiv_apply [FiniteDimensional ℂ E] [CompleteSpace F] {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) (v : E) :
    DifferentiableOn ℂ (fun x => fderiv ℂ f x v) U := by
  have := FiniteDimensional.proper ℂ E
  by_cases hv : v = 0
  · subst hv
    simp
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  intro x₁ hx₁
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.1 hU x₁ hx₁
  set ρ := ρ0 / 3 with hρ
  have hρpos : 0 < ρ := by positivity
  set R := ρ / ‖v‖ with hR
  have hRpos : 0 < R := by positivity
  have hsub : closedBall x₁ (2 * ρ) ⊆ U := (closedBall_subset_ball (by rw [hρ]; linarith)).trans hball
  have hmem : ∀ x ∈ ball x₁ ρ, ∀ z ∈ closedBall (0:ℂ) R, x + z • v ∈ closedBall x₁ (2 * ρ) := by
    intro x hx z hz
    rw [mem_closedBall, dist_eq_norm]
    rw [mem_ball, dist_eq_norm] at hx
    have hz' : ‖z‖ ≤ R := by simpa using hz
    have h1 : ‖z • v‖ ≤ ρ := by
      rw [norm_smul]
      calc ‖z‖ * ‖v‖ ≤ R * ‖v‖ := by gcongr
        _ = ρ := by rw [hR]; field_simp
    calc ‖x + z • v - x₁‖ = ‖(x - x₁) + z • v‖ := by congr 1; abel
      _ ≤ ‖x - x₁‖ + ‖z • v‖ := norm_add_le _ _
      _ ≤ 2 * ρ := by linarith
  have hdf : ∀ y ∈ U, DifferentiableAt ℂ f y := fun y hy => (hf y hy).differentiableAt (hU.mem_nhds hy)
  have hcirc : ∀ θ : ℝ, circleMap 0 R θ ∈ closedBall (0:ℂ) R := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere 0 hRpos.le θ)
  have hform : ∀ x ∈ ball x₁ ρ, fderiv ℂ f x v =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(0, R), ((z - 0) ^ 2)⁻¹ • f (x + z • v) := by
    intro x hx
    have hopen : IsOpen ((fun z : ℂ => x + z • v) ⁻¹' U) := hU.preimage (by fun_prop)
    have h1 := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hopen
      (c := 0) (w₀ := 0) (R := R) (f := fun z => f (x + z • v)) (fun z hz => hsub (hmem x hx z hz))
      (fun z hz => (C_line_hasDerivAt (hdf _ hz)).differentiableAt.differentiableWithinAt)
      (mem_ball_self hRpos)
    have hx0 : DifferentiableAt ℂ f (x + (0:ℂ) • v) :=
      hdf _ (hsub (hmem x hx 0 (mem_closedBall_self hRpos.le)))
    rw [h1, (C_line_hasDerivAt hx0).deriv]
    simp
  obtain ⟨B, hB⟩ := (isCompact_closedBall x₁ (2 * ρ)).exists_bound_of_continuousOn
    ((C_continuousOn_fderiv hU hf).mono hsub)
  have hc1 : Continuous fun θ : ℝ => deriv (circleMap 0 R) θ := by
    have : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I := by
      funext θ; rw [deriv_circleMap]
    rw [this]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hc2 : Continuous fun θ : ℝ => ((circleMap 0 R θ - 0) ^ 2)⁻¹ := by
    refine Continuous.inv₀ (((continuous_circleMap 0 R).sub continuous_const).pow 2) fun θ => ?_
    exact pow_ne_zero 2 (sub_ne_zero.2 (circleMap_ne_center hRpos.ne'))
  have hcF : ∀ x ∈ ball x₁ ρ, Continuous fun θ : ℝ => f (x + circleMap 0 R θ • v) := by
    intro x hx
    refine hf.continuousOn.comp_continuous ?_ fun θ => hsub (hmem x hx _ (hcirc θ))
    exact continuous_const.add ((continuous_circleMap 0 R).smul continuous_const)
  have hcF' : Continuous fun θ : ℝ => fderiv ℂ f (x₁ + circleMap 0 R θ • v) := by
    refine (C_continuousOn_fderiv hU hf).comp_continuous ?_
      fun θ => hsub (hmem x₁ (mem_ball_self hρpos) _ (hcirc θ))
    exact continuous_const.add ((continuous_circleMap 0 R).smul continuous_const)
  have hder : HasFDerivAt (fun x => ∫ θ in (0:ℝ)..2 * Real.pi, deriv (circleMap 0 R) θ •
        (((circleMap 0 R θ - 0) ^ 2)⁻¹ • f (x + circleMap 0 R θ • v)))
      (∫ θ in (0:ℝ)..2 * Real.pi, deriv (circleMap 0 R) θ •
        (((circleMap 0 R θ - 0) ^ 2)⁻¹ • fderiv ℂ f (x₁ + circleMap 0 R θ • v))) x₁ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (F' := fun x θ => deriv (circleMap 0 R) θ •
        (((circleMap 0 R θ - 0) ^ 2)⁻¹ • fderiv ℂ f (x + circleMap 0 R θ • v)))
      (bound := fun θ => ‖deriv (circleMap 0 R) θ‖ * (‖((circleMap 0 R θ - 0) ^ 2)⁻¹‖ * B))
      (ball_mem_nhds x₁ hρpos) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [ball_mem_nhds x₁ hρpos] with x hx
      exact (hc1.smul (hc2.smul (hcF x hx))).aestronglyMeasurable
    · exact (hc1.smul (hc2.smul (hcF x₁ (mem_ball_self hρpos)))).intervalIntegrable _ _
    · exact (hc1.smul (hc2.smul hcF')).aestronglyMeasurable
    · refine Eventually.of_forall fun θ _ x hx => ?_
      rw [norm_smul, norm_smul]
      gcongr
      exact hB _ (hmem x hx _ (hcirc θ))
    · exact (hc1.norm.mul (hc2.norm.mul continuous_const)).intervalIntegrable _ _
    · refine Eventually.of_forall fun θ _ x hx => ?_
      have h1 := (hdf _ (hsub (hmem x hx _ (hcirc θ)))).hasFDerivAt.comp x
        ((hasFDerivAt_id x).add_const (circleMap 0 R θ • v))
      have h2 : HasFDerivAt (fun x => f (x + circleMap 0 R θ • v))
          (fderiv ℂ f (x + circleMap 0 R θ • v)) x := by
        simpa [Function.comp_def] using h1
      exact (h2.const_smul _).const_smul _
  have hev : (fun x => fderiv ℂ f x v) =ᶠ[𝓝 x₁] fun x => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∫ θ in (0:ℝ)..2 * Real.pi, deriv (circleMap 0 R) θ •
        (((circleMap 0 R θ - 0) ^ 2)⁻¹ • f (x + circleMap 0 R θ • v)) := by
    filter_upwards [ball_mem_nhds x₁ hρpos] with x hx
    rw [hform x hx]
    rfl
  exact (hev.differentiableAt_iff).2 (hder.differentiableAt.const_smul _)

theorem holo_contDiffOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn ℂ f U) (n : ℕ) : ContDiffOn ℂ n f U := by
  induction n generalizing f with
  | zero => exact contDiffOn_zero.2 hf.continuousOn
  | succ n ih =>
    have h := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℂ) (n := (n : WithTop ℕ∞)) (f := f) hU).2
      ⟨hf, fun h => absurd h (by simp), contDiffOn_clm_apply.2 fun v =>
        ih (C_differentiableOn_fderiv_apply hU hf v)⟩
    exact_mod_cast h

theorem holo_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (i : ℕ) {f : E → F} {x : E} {δ M : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (Metric.ball x ((i + 1 : ℕ) * δ)))
    (hM : ∀ y ∈ Metric.ball x ((i + 1 : ℕ) * δ), ‖f y‖ ≤ M) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ M / δ ^ i := by
  induction i generalizing f M with
  | zero =>
    rw [norm_iteratedFDeriv_zero, pow_zero, div_one]
    exact hM x (mem_ball_self (by positivity))
  | succ i ih =>
    have hpos : 0 < ((i + 1 + 1 : ℕ) : ℝ) * δ := by positivity
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_ball_self hpos))
    have hdf : ∀ y ∈ ball x (((i + 1 + 1 : ℕ) : ℝ) * δ), DifferentiableAt ℂ f y :=
      fun y hy => (hf y hy).differentiableAt (isOpen_ball.mem_nhds hy)
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
    rw [iteratedFDeriv_succ_apply_right]
    set v := m (Fin.last i) with hv
    have hcd : ContDiffAt ℝ ((i + 1 : ℕ) : WithTop ℕ∞) f x :=
      ((holo_contDiffOn isOpen_ball hf (i + 1)).contDiffAt (ball_mem_nhds x hpos)).restrict_scalars ℝ
    have hcd' : ContDiffAt ℝ (i : WithTop ℕ∞) (fderiv ℝ f) x :=
      hcd.fderiv_right (by exact_mod_cast le_rfl)
    have h1 : iteratedFDeriv ℝ i (fderiv ℝ f) x (Fin.init m) v =
        iteratedFDeriv ℝ i (fun y => fderiv ℝ f y v) x (Fin.init m) := by
      have h := (ContinuousLinearMap.apply ℝ F v).iteratedFDeriv_comp_left hcd' le_rfl
      have h' : iteratedFDeriv ℝ i (fun y => fderiv ℝ f y v) x =
          (ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap
            (iteratedFDeriv ℝ i (fderiv ℝ f) x) := h
      rw [h']
      rfl
    have h2 : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x] fun y => fderiv ℂ f y v := by
      filter_upwards [ball_mem_nhds x hpos] with y hy
      rw [(hdf y hy).fderiv_restrictScalars ℝ]
      rfl
    have hsubb : ball x (((i + 1 : ℕ) : ℝ) * δ) ⊆ ball x (((i + 1 + 1 : ℕ) : ℝ) * δ) := by
      refine ball_subset_ball ?_
      push_cast
      nlinarith
    have h3 := ih (f := fun y => fderiv ℂ f y v) (M := M / δ * ‖v‖)
      ((C_differentiableOn_fderiv_apply isOpen_ball hf v).mono hsubb) (by
        intro y hy
        have hyb : ball y δ ⊆ ball x (((i + 1 + 1 : ℕ) : ℝ) * δ) := by
          refine ball_subset_ball' ?_
          rw [mem_ball] at hy
          push_cast at hy ⊢
          linarith
        have h4 := C_norm_fderiv_le hδ (hf.mono hyb) (fun z hz => hM z (hyb hz))
        exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr))
    rw [h1, (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) h2 i).eq_of_nhds]
    calc ‖iteratedFDeriv ℝ i (fun y => fderiv ℂ f y v) x (Fin.init m)‖
        ≤ ‖iteratedFDeriv ℝ i (fun y => fderiv ℂ f y v) x‖ * ∏ j, ‖Fin.init m j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (M / δ * ‖v‖ / δ ^ i) * ∏ j, ‖Fin.init m j‖ := by gcongr
      _ = M / δ ^ (i + 1) * ∏ j, ‖m j‖ := by
          rw [Fin.prod_univ_castSucc, ← hv, pow_succ]
          simp only [Fin.init]
          field_simp

end Holo

end Formalism.FourierDecayAlt.P.StationaryPhaseModel

end PartC

section PartD

open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix

namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel

noncomputable section

def D_nsq (d : ℕ) (x : Fin d → ℂ) : ℝ := ∑ k, ‖x k‖ ^ 2

def D_gau (d : ℕ) (δ : ℝ) (x : Fin d → ℂ) : ℝ := Real.exp (-δ * ∑ k, ‖x k‖ ^ 2)

theorem D_wt_pos {E : Type*} [NormedAddCommGroup E] {σ : ℝ} (hσ : 0 < σ) (x : E) : 0 < wt σ x := by
  unfold wt; positivity

theorem D_nsq_sym (d N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ Sym (Set.univ : Set (Fin d → ℂ)) (wt 1) 2 N K (D_nsq d) := by
  have hw : ∀ x ∈ (Set.univ : Set (Fin d → ℂ)), 0 < wt (1 : ℝ) x := fun x _ => D_wt_pos one_pos x
  let Lr : Fin d → ((Fin d → ℂ) →L[ℝ] ℝ) := fun k =>
    Complex.reCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) k)
  let Li : Fin d → ((Fin d → ℂ) →L[ℝ] ℝ) := fun k =>
    Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) k)
  have h1 : ∀ k ∈ (Finset.univ : Finset (Fin d)), Sym (Set.univ : Set (Fin d → ℂ)) (wt 1) 2 N
      (2 ^ N * ‖Lr k‖ * ‖Lr k‖ + 2 ^ N * ‖Li k‖ * ‖Li k‖) (fun x => Lr k x * Lr k x + Li k x * Li k x) := by
    intro k _
    exact (Sym.mul hw (Sym.clm (Lr k) one_pos) (Sym.clm (Lr k) one_pos)).add
      (Sym.mul hw (Sym.clm (Li k) one_pos) (Sym.clm (Li k) one_pos))
  refine ⟨∑ k : Fin d, (2 ^ N * ‖Lr k‖ * ‖Lr k‖ + 2 ^ N * ‖Li k‖ * ‖Li k‖), by positivity, ?_⟩
  have h2 := Sym.sum Finset.univ h1
  convert h2 using 2 with x
  unfold D_nsq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Lr, Li, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Complex.reCLM_apply,
    Complex.imCLM_apply]
  rw [Complex.sq_norm, Complex.normSq_apply]

theorem D_norm_sq_le_nsq (d : ℕ) (x : Fin d → ℂ) : ‖x‖ ^ 2 ≤ D_nsq d x := by
  have h0 : 0 ≤ D_nsq d x := by unfold D_nsq; positivity
  have h1 : ‖x‖ ≤ Real.sqrt (D_nsq d x) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro k
    apply Real.le_sqrt_of_sq_le
    unfold D_nsq
    exact Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ k)
  calc ‖x‖ ^ 2 ≤ Real.sqrt (D_nsq d x) ^ 2 := by gcongr
    _ = D_nsq d x := Real.sq_sqrt h0

theorem D_exp_decay (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (1 + s) ^ (2 * n) * Real.exp (-s ^ 2) ≤ 2 ^ n * n.factorial * Real.exp 1 := by
  have h1 : (1 + s) ^ 2 ≤ 2 * (1 + s ^ 2) := by nlinarith [sq_nonneg (1 - s)]
  have h2 : (1 + s ^ 2) ^ n / n.factorial ≤ Real.exp (1 + s ^ 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have h3 : (1 + s ^ 2) ^ n ≤ n.factorial * Real.exp (1 + s ^ 2) := by
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  calc (1 + s) ^ (2 * n) * Real.exp (-s ^ 2) = ((1 + s) ^ 2) ^ n * Real.exp (-s ^ 2) := by rw [pow_mul]
    _ ≤ (2 * (1 + s ^ 2)) ^ n * Real.exp (-s ^ 2) := by gcongr
    _ = 2 ^ n * (1 + s ^ 2) ^ n * Real.exp (-s ^ 2) := by rw [mul_pow]
    _ ≤ 2 ^ n * (n.factorial * Real.exp (1 + s ^ 2)) * Real.exp (-s ^ 2) := by gcongr
    _ = 2 ^ n * n.factorial * (Real.exp (1 + s ^ 2) * Real.exp (-s ^ 2)) := by ring
    _ = 2 ^ n * n.factorial * Real.exp 1 := by rw [← Real.exp_add]; congr 2; ring

theorem D_norm_iter_exp (i : ℕ) (y : ℝ) : ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_of_nonneg (Real.exp_pos y).le]

theorem D_gau_one_eq (d : ℕ) : D_gau d 1 = Real.exp ∘ (fun x => - D_nsq d x) := by
  funext x
  simp [D_gau, D_nsq]

theorem D_gau_one_bound (d n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Fin d → ℂ,
    (1 + ‖x‖) ^ n * ‖iteratedFDeriv ℝ n (D_gau d 1) x‖ ≤ M := by
  obtain ⟨K, hK, hS⟩ := D_nsq_sym d n
  refine ⟨n.factorial * (K + 1) ^ n * (2 ^ n * n.factorial * Real.exp 1), by positivity, fun x => ?_⟩
  have hS' := hS.neg
  have hb : ‖iteratedFDeriv ℝ n (D_gau d 1) x‖ ≤
      n.factorial * Real.exp (- D_nsq d x) * ((K + 1) * (1 + ‖x‖)) ^ n := by
    rw [D_gau_one_eq]
    refine norm_iteratedFDeriv_comp_le (N := (n : ℕ)) Real.contDiff_exp hS'.1 le_rfl x
      (fun i _ => (D_norm_iter_exp i _).le) (fun i hi1 hin => ?_)
    have h1 := hS'.2 x (Set.mem_univ x) i hin
    have hw1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h2 : wt (1 : ℝ) x ^ ((2 : ℤ) - (i : ℤ)) ≤ (1 + ‖x‖) ^ i := by
      have : wt (1 : ℝ) x = 1 + ‖x‖ := by unfold wt; ring
      rw [this, ← zpow_natCast]
      exact zpow_le_zpow_right₀ hw1 (by omega)
    have h3 : K ≤ (K + 1) ^ i := by
      calc K ≤ K + 1 := by linarith
        _ ≤ (K + 1) ^ i := le_self_pow₀ (by linarith) (by omega)
    calc _ ≤ K * wt (1 : ℝ) x ^ ((2 : ℤ) - (i : ℤ)) := h1
      _ ≤ (K + 1) ^ i * (1 + ‖x‖) ^ i := by
        apply mul_le_mul h3 h2 (zpow_nonneg (D_wt_pos one_pos x).le _) (by positivity)
      _ = ((K + 1) * (1 + ‖x‖)) ^ i := by rw [mul_pow]
  have he : Real.exp (- D_nsq d x) ≤ Real.exp (- ‖x‖ ^ 2) :=
    Real.exp_le_exp.2 (neg_le_neg (D_norm_sq_le_nsq d x))
  calc (1 + ‖x‖) ^ n * ‖iteratedFDeriv ℝ n (D_gau d 1) x‖
      ≤ (1 + ‖x‖) ^ n * (n.factorial * Real.exp (- ‖x‖ ^ 2) * ((K + 1) * (1 + ‖x‖)) ^ n) := by
        gcongr
        exact hb.trans (by gcongr)
    _ = n.factorial * (K + 1) ^ n * ((1 + ‖x‖) ^ (2 * n) * Real.exp (- ‖x‖ ^ 2)) := by
        rw [mul_pow, two_mul, pow_add]; ring
    _ ≤ n.factorial * (K + 1) ^ n * (2 ^ n * n.factorial * Real.exp 1) := by
        exact mul_le_mul_of_nonneg_left (D_exp_decay n ‖x‖ (norm_nonneg x)) (by positivity)

theorem D_gau_contDiff (d : ℕ) (δ : ℝ) (n : ℕ) : ContDiff ℝ n (D_gau d δ) := by
  obtain ⟨K, _, hS⟩ := D_nsq_sym d n
  have : D_gau d δ = fun x => Real.exp (-δ * D_nsq d x) := rfl
  rw [this]
  exact Real.contDiff_exp.comp (contDiff_const.mul hS.1)

theorem D_gau_scale (d : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    D_gau d δ = fun x => D_gau d 1 (Real.sqrt δ • x) := by
  funext x
  unfold D_gau
  congr 1
  simp only [Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hδ, ← Finset.mul_sum]
  ring

theorem D_gau_bound (d N : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    (∀ x : Fin d → ℂ, ∀ i ≤ N, ‖iteratedFDeriv ℝ i (D_gau d δ) x‖ ≤ M) ∧
    Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 0 N M (D_gau d δ) := by
  choose c hc0 hc using D_gau_one_bound d
  refine ⟨∑ i ∈ Finset.range (N + 1), c i, Finset.sum_nonneg fun i _ => hc0 i, ?_⟩
  intro δ hδ hδ1 σ hσ hσ1
  have hci : ∀ i ≤ N, c i ≤ ∑ i ∈ Finset.range (N + 1), c i := fun i hi =>
    Finset.single_le_sum (f := c) (fun j _ => hc0 j) (Finset.mem_range.2 (by omega))
  set a := Real.sqrt δ with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 hδ
  have ha1 : a ≤ 1 := Real.sqrt_le_one.2 hδ1
  have hder : ∀ (i : ℕ) (x : Fin d → ℂ), ‖iteratedFDeriv ℝ i (D_gau d δ) x‖ =
      a ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖ := by
    intro i x
    rw [D_gau_scale d δ hδ.le, iteratedFDeriv_comp_const_smul a (D_gau_contDiff d 1 i), norm_smul, norm_pow,
      Real.norm_of_nonneg ha0.le]
  have hkey : ∀ (i : ℕ) (x : Fin d → ℂ), (‖x‖ + σ) ^ i * ‖iteratedFDeriv ℝ i (D_gau d δ) x‖ ≤ c i := by
    intro i x
    rw [hder]
    calc (‖x‖ + σ) ^ i * (a ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖)
        = (a * ‖x‖ + a * σ) ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖ := by
          rw [← mul_assoc, ← mul_pow]; congr 2; ring
      _ ≤ (1 + ‖a • x‖) ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖ := by
          have h5 : a * ‖x‖ + a * σ ≤ 1 + ‖a • x‖ := by
            rw [norm_smul, Real.norm_of_nonneg ha0.le]
            have : a * σ ≤ 1 := by nlinarith
            linarith
          have h6 : 0 ≤ a * ‖x‖ + a * σ := by positivity
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h6 h5 i) (norm_nonneg _)
      _ ≤ c i := hc i _
  refine ⟨fun x i hi => ?_, D_gau_contDiff d δ N, fun x _ i hi => ?_⟩
  · rw [hder]
    have h1 := hc i (a • x)
    have h2 : (1 : ℝ) ≤ (1 + ‖a • x‖) ^ i := one_le_pow₀ (by linarith [norm_nonneg (a • x)])
    have h3 : a ^ i ≤ 1 := pow_le_one₀ ha0.le ha1
    calc a ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖
        ≤ (1 + ‖a • x‖) ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖ := by
          exact mul_le_mul_of_nonneg_right (h3.trans h2) (norm_nonneg _)
      _ ≤ _ := h1.trans (hci i hi)
  · have hw : 0 < wt σ x := D_wt_pos hσ x
    rw [zero_sub, _root_.zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact (hkey i x).trans (hci i hi)

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem D_sym_cast {A : Set E} {w : E → ℝ} {m m' : ℤ} {N : ℕ} {K : ℝ} {f : E → F} (h : m = m')
    (hf : Sym A w m N K f) : Sym A w m' N K f := h ▸ hf

theorem D_sym_univ {A : Set E} {w : E → ℝ} {m : ℤ} {N : ℕ} {K : ℝ} {f : E → F} (hf : Sym A w m N K f)
    (hs : tsupport f ⊆ A) (hK : 0 ≤ K) (hw : ∀ x, 0 < w x) : Sym Set.univ w m N K f := by
  refine ⟨hf.1, fun x _ i hi => ?_⟩
  by_cases hx : x ∈ A
  · exact hf.2 x hx i hi
  · have h1 : x ∉ tsupport (iteratedFDeriv ℝ i f) := fun h => hx (hs (tsupport_iteratedFDeriv_subset i h))
    rw [image_eq_zero_of_notMem_tsupport h1, norm_zero]
    exact mul_nonneg hK (zpow_nonneg (hw x).le _)

theorem D_bdd_sym {N : ℕ} {K : ℝ} {f : E → F} (hf : ContDiff ℝ N f)
    (h : ∀ x, ∀ i ≤ N, ‖iteratedFDeriv ℝ i f x‖ ≤ K) : Sym Set.univ (fun _ : E => (1 : ℝ)) 0 N K f :=
  ⟨hf, fun x _ i hi => by simpa using h x i hi⟩

theorem D_sym_bdd {N : ℕ} {K : ℝ} {f : E → F} (hf : Sym Set.univ (fun _ : E => (1 : ℝ)) 0 N K f) :
    ∀ x, ∀ i ≤ N, ‖iteratedFDeriv ℝ i f x‖ ≤ K :=
  fun x i hi => by simpa using hf.2 x (Set.mem_univ x) i hi

theorem D_dil_sym {N : ℕ} {h : E → F} {ρ₀ M : ℝ} (hh : ContDiff ℝ N h)
    (hs : tsupport h ⊆ Metric.closedBall 0 ρ₀) (hρ₀ : 0 ≤ ρ₀) (hM : ∀ x, ∀ i ≤ N, ‖iteratedFDeriv ℝ i h x‖ ≤ M)
    {R σ : ℝ} (hR : 1 ≤ R) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Sym Set.univ (wt σ) 0 N (M * (ρ₀ + 1) ^ N) (fun x => h (R⁻¹ • x)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0 (Nat.zero_le _))
  have hR0 : 0 < R := by linarith
  refine ⟨hh.comp (contDiff_const_smul _), fun x _ i hi => ?_⟩
  have hw : 0 < wt σ x := D_wt_pos hσ x
  rw [iteratedFDeriv_comp_const_smul R⁻¹ (hh.of_le (by exact_mod_cast hi)), norm_smul, norm_pow,
    Real.norm_of_nonneg (inv_pos.2 hR0).le]
  by_cases hx : R⁻¹ • x ∈ tsupport h
  · have h1 : ‖R⁻¹ • x‖ ≤ ρ₀ := by simpa using hs hx
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hR0).le, inv_mul_le_iff₀ hR0] at h1
    have h2 : wt σ x ≤ (ρ₀ + 1) * R := by unfold wt; nlinarith
    have h3 : R⁻¹ * wt σ x ≤ ρ₀ + 1 := by rw [inv_mul_le_iff₀ hR0]; linarith
    have h4 : (R⁻¹ * wt σ x) ^ i ≤ (ρ₀ + 1) ^ N :=
      (pow_le_pow_left₀ (by positivity) h3 i).trans (pow_le_pow_right₀ (by linarith) hi)
    rw [zero_sub, _root_.zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc R⁻¹ ^ i * ‖iteratedFDeriv ℝ i h (R⁻¹ • x)‖ * wt σ x ^ i
        = ‖iteratedFDeriv ℝ i h (R⁻¹ • x)‖ * (R⁻¹ * wt σ x) ^ i := by rw [mul_pow]; ring
      _ ≤ M * (ρ₀ + 1) ^ N := mul_le_mul (hM _ i hi) h4 (by positivity) hM0
  · have h1 : R⁻¹ • x ∉ tsupport (iteratedFDeriv ℝ i h) := fun h => hx (tsupport_iteratedFDeriv_subset i h)
    rw [image_eq_zero_of_notMem_tsupport h1, norm_zero, mul_zero]
    exact mul_nonneg (by positivity) (zpow_nonneg hw.le _)

end

theorem D_cut_eq (d : ℕ) {ρ : ℝ} (h : 0 < ρ) :
    cutB d ρ = (⟨ρ / 2, ρ, half_pos h, half_lt_self h⟩ : ContDiffBump (0 : Fin d → ℂ)) := by
  funext x
  simp [cutB, h]

theorem D_cut_contDiff (d : ℕ) {ρ : ℝ} (h : 0 < ρ) (n : ℕ) : ContDiff ℝ n (cutB d ρ) := by
  rw [D_cut_eq d h]
  exact ContDiffBump.contDiff (n := (n : ℕ∞)) _

theorem D_cut_tsupport (d : ℕ) {ρ : ℝ} (h : 0 < ρ) : tsupport (cutB d ρ) = Metric.closedBall 0 ρ := by
  rw [D_cut_eq d h]
  exact ContDiffBump.tsupport_eq _

theorem D_cut_compact (d : ℕ) {ρ : ℝ} (h : 0 < ρ) : HasCompactSupport (cutB d ρ) := by
  rw [D_cut_eq d h]
  exact ContDiffBump.hasCompactSupport _

theorem D_cut_one (d : ℕ) {ρ : ℝ} (h : 0 < ρ) {x : Fin d → ℂ} (hx : ‖x‖ ≤ ρ / 2) : cutB d ρ x = 1 := by
  rw [D_cut_eq d h]
  exact ContDiffBump.one_of_mem_closedBall _ (by simpa using hx)

theorem D_cut_nonneg (d : ℕ) {ρ : ℝ} (h : 0 < ρ) (x : Fin d → ℂ) : 0 ≤ cutB d ρ x := by
  rw [D_cut_eq d h]
  exact ContDiffBump.nonneg _

theorem D_cut_le_one (d : ℕ) {ρ : ℝ} (h : 0 < ρ) (x : Fin d → ℂ) : cutB d ρ x ≤ 1 := by
  rw [D_cut_eq d h]
  exact ContDiffBump.le_one _

theorem D_cut_bound (d N : ℕ) {ρ : ℝ} (h : 0 < ρ) : ∃ M : ℝ, ∀ x, ∀ i ≤ N,
    ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ M := by
  have h1 : ∀ i : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ C := fun i =>
    ((D_cut_compact d h).iteratedFDeriv i).exists_bound_of_continuous
      ((D_cut_contDiff d h i).continuous_iteratedFDeriv le_rfl)
  choose c hc using h1
  have hc0 : ∀ i, 0 ≤ c i := fun i => (norm_nonneg _).trans (hc i 0)
  exact ⟨∑ i ∈ Finset.range (N + 1), c i, fun x i hi => (hc i x).trans
    (Finset.single_le_sum (f := c) (fun j _ => hc0 j) (Finset.mem_range.2 (by omega)))⟩

theorem D_amp (d N : ℕ) (hN : 2 ≤ N) {ρ : ℝ} (hρ : 0 < ρ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ R : ℝ, 1 ≤ R →
      Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 2 N K
        (fun x => cutB d 2 (R⁻¹ • x) * (cutB d ρ x - D_gau d δ x)) := by
  obtain ⟨MG, hMG0, hMG⟩ := D_gau_bound d N
  obtain ⟨Mχ, hMχ⟩ := D_cut_bound d N hρ
  obtain ⟨M2, hM2⟩ := D_cut_bound d N (two_pos : (0 : ℝ) < 2)
  have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (hMχ 0 0 (Nat.zero_le _))
  have hM20 : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0 0 (Nat.zero_le _))
  set Kχ := Mχ * (ρ + 1) ^ N with hKχ
  set K1 := 2 ^ N * Kχ * ((1 + MG) * (ρ + 1) ^ N) with hK1
  set K2 := 2 ^ N * (1 + Kχ) * MG / (ρ / 2) ^ 2 with hK2
  refine ⟨2 ^ N * (M2 * ((2 : ℝ) + 1) ^ N) * (K1 + K2), by positivity, ?_⟩
  intro δ hδ hδ1 σ hσ hσ1 R hR
  obtain ⟨hGb, hGs⟩ := hMG δ hδ hδ1 σ hσ hσ1
  have hw : ∀ x : Fin d → ℂ, 0 < wt σ x := fun x => D_wt_pos hσ x
  have hwA : ∀ (A : Set (Fin d → ℂ)), ∀ x ∈ A, 0 < wt σ x := fun _ x _ => hw x

  have hχ : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 0 N Kχ (cutB d ρ) := by
    have := D_dil_sym (D_cut_contDiff d hρ N) (D_cut_tsupport d hρ).le hρ.le hMχ (le_refl (1 : ℝ)) hσ hσ1
    simpa using this
  have hχR : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 0 N (M2 * ((2 : ℝ) + 1) ^ N)
      (fun x => cutB d 2 (R⁻¹ • x)) :=
    D_dil_sym (D_cut_contDiff d two_pos N) (D_cut_tsupport d two_pos).le two_pos.le hM2 hR hσ hσ1

  have h1G : Sym (Metric.closedBall (0 : Fin d → ℂ) ρ) (wt σ) 2 N ((1 + MG) * (ρ + 1) ^ N)
      (fun x => 1 - D_gau d δ x) := by
    have hb : Sym Set.univ (fun _ : Fin d → ℂ => (1 : ℝ)) 0 N (1 + MG) (fun x => 1 - D_gau d δ x) :=
      (Sym.const (1 : ℝ) zero_le_one (fun _ _ => one_pos) (fun _ _ => by simp)).sub
        (D_bdd_sym (D_gau_contDiff d δ N) hGb)
    have hle : ∀ x, D_gau d δ x ≤ 1 := by
      intro x
      unfold D_gau
      rw [Real.exp_le_one_iff]
      have : 0 ≤ ∑ k, ‖x k‖ ^ 2 := by positivity
      nlinarith
    have h00 : D_gau d δ 0 = 1 := by simp [D_gau]
    have hfd : fderiv ℝ (fun x => 1 - D_gau d δ x) 0 = 0 := by
      apply IsLocalMin.fderiv_eq_zero
      refine Filter.Eventually.of_forall fun x => ?_
      simp only [h00]
      linarith [hle x]
    have := Sym.of_vanish (N := N) (σ := σ) (r := ρ) 2 hρ hσ hσ1 hN hb.1
      (fun x _ i hi => D_sym_bdd hb x i hi) (fun i hi => by
        interval_cases i
        · ext m
          simp [h00]
        · ext m
          rw [iteratedFDeriv_one_apply, hfd]
          simp)
    exact this
  have hb1 : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 2 N K1 (fun x => cutB d ρ x * (1 - D_gau d δ x)) := by
    have h := D_sym_cast (m' := 2) (by norm_num) (Sym.mul (hwA _) (hχ.subset (Set.subset_univ _)) h1G)
    refine D_sym_univ (m := 2) h ?_ (by positivity) hw
    rw [← D_cut_tsupport d hρ]
    exact tsupport_mul_subset_left
  have hb2 : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 2 N K2 (fun x => (1 - cutB d ρ x) * D_gau d δ x) := by
    have h1χ : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 0 N (1 + Kχ) (fun x => 1 - cutB d ρ x) :=
      (Sym.const (1 : ℝ) zero_le_one (hwA _) (fun _ _ => by simp)).sub hχ
    have h := (Sym.mul (hwA _) h1χ hGs).subset (Set.subset_univ {x : Fin d → ℂ | ρ / 2 ≤ ‖x‖})
    have h' := D_sym_cast (m' := 2) (by norm_num) (Sym.raise 2 (half_pos hρ) (fun x hx => by
      have : ρ / 2 ≤ ‖x‖ := hx
      unfold wt; linarith) h)
    refine D_sym_univ h' ?_ (by positivity) hw
    refine (tsupport_mul_subset_left).trans ?_
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
    intro x hx
    by_contra hlt
    have hlt' : ‖x‖ ≤ ρ / 2 := by
      have : ¬ ρ / 2 ≤ ‖x‖ := hlt
      linarith
    exact hx (by simp [D_cut_one d hρ hlt'])
  have hb := hb1.sub hb2
  have hfin := D_sym_cast (m' := 2) (by norm_num) (Sym.mul (hwA _) hχR hb)
  convert hfin using 2 with x
  ring

def D_phi (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) : ℝ := (c * (x ⬝ᵥ (H *ᵥ x)) / 2).re

def D_bil (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) : (Fin d → ℂ) →ₗ[ℝ] (Fin d → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x v => (c * (v ⬝ᵥ (H *ᵥ x))).re)
    (fun x x' v => by simp [Matrix.mulVec_add, dotProduct_add, mul_add])
    (fun r x v => by
      rw [Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul, smul_eq_mul, ← Complex.re_ofReal_mul]
      congr 1; ring)
    (fun x v v' => by simp [add_dotProduct, mul_add])
    (fun r x v => by
      rw [smul_dotProduct, Complex.real_smul, smul_eq_mul, ← Complex.re_ofReal_mul]
      congr 1; ring)

theorem D_bil_apply (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (x v : Fin d → ℂ) :
    D_bil d c H x v = (c * (v ⬝ᵥ (H *ᵥ x))).re := rfl

theorem D_mulVec_le (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ) {Γ : ℝ} (hH : ∀ i j, ‖H i j‖ ≤ Γ) (x : Fin d → ℂ)
    (k : Fin d) : ‖(H *ᵥ x) k‖ ≤ d * Γ * ‖x‖ := by
  unfold Matrix.mulVec dotProduct
  calc ‖∑ j, H k j * x j‖ ≤ ∑ j, ‖H k j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, Γ * ‖x‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hH k j) (norm_le_pi_norm x j) (norm_nonneg _) ((norm_nonneg _).trans (hH k j))
    _ = d * Γ * ‖x‖ := by simp; ring

theorem D_bil_bound (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) {Γ : ℝ}
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) (x v : Fin d → ℂ) :
    ‖D_bil d c H x v‖ ≤ (‖c‖ * (d * (d * Γ))) * ‖x‖ * ‖v‖ := by
  rw [D_bil_apply, Real.norm_eq_abs]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul]
  have h1 : ‖v ⬝ᵥ (H *ᵥ x)‖ ≤ d * (‖v‖ * (d * Γ * ‖x‖)) := by
    unfold dotProduct
    calc ‖∑ k, v k * (H *ᵥ x) k‖ ≤ ∑ k, ‖v k * (H *ᵥ x) k‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin d, ‖v‖ * (d * Γ * ‖x‖) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm v k) (D_mulVec_le d H hH x k) (norm_nonneg _) (norm_nonneg _)
      _ = d * (‖v‖ * (d * Γ * ‖x‖)) := by simp
  calc ‖c‖ * ‖v ⬝ᵥ (H *ᵥ x)‖ ≤ ‖c‖ * (d * (‖v‖ * (d * Γ * ‖x‖))) := by gcongr
    _ = _ := by ring

def D_bilC (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (Γ : ℝ) (_hΓ : 0 ≤ Γ) (hH : ∀ i j, ‖H i j‖ ≤ Γ) :
    (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ :=
  (D_bil d c H).mkContinuous₂ (‖c‖ * (d * (d * Γ))) (D_bil_bound d c H hH)

theorem D_bilC_apply (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) (x v : Fin d → ℂ) :
    D_bilC d c H Γ hΓ hH x v = (c * (v ⬝ᵥ (H *ᵥ x))).re := rfl

theorem D_bilC_norm (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) : ‖D_bilC d c H Γ hΓ hH‖ ≤ ‖c‖ * (d * (d * Γ)) :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

theorem D_symm_dot (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ) (hs : H.IsSymm) (x v : Fin d → ℂ) :
    v ⬝ᵥ (H *ᵥ x) = x ⬝ᵥ (H *ᵥ v) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs.eq, dotProduct_comm]

theorem D_phi_eq (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) : D_phi d c H = fun x => (1 / 2 : ℝ) * D_bilC d c H Γ hΓ hH x x := by
  funext x
  rw [D_bilC_apply, D_phi, ← Complex.re_ofReal_mul]
  congr 1
  push_cast
  ring

theorem D_phi_contDiff (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) (n : ℕ) : ContDiff ℝ n (D_phi d c H) := by
  rw [D_phi_eq d c H Γ hΓ hH]
  exact contDiff_const.mul ((D_bilC d c H Γ hΓ hH).contDiff.clm_apply contDiff_id)

theorem D_phi_fderiv (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (hs : H.IsSymm) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) : fderiv ℝ (D_phi d c H) = fun x => D_bilC d c H Γ hΓ hH x := by
  funext x
  have h1 := (((D_bilC d c H Γ hΓ hH).hasFDerivAt (x := x)).clm_apply (hasFDerivAt_id x)).const_mul
    (1 / 2 : ℝ)
  rw [D_phi_eq d c H Γ hΓ hH]
  refine (HasFDerivAt.fderiv h1).trans ?_
  ext v
  simp only [_root_.smul_apply, _root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.id_apply, id_eq, D_bilC_apply, smul_eq_mul]
  rw [D_symm_dot d H hs x v]
  ring

theorem D_dirv_false (d : ℕ) (k : Fin d) (y : Fin d → ℂ) : (dirv (k, false)) ⬝ᵥ y = y k := by
  simp [dirv]

theorem D_dirv_true (d : ℕ) (k : Fin d) (y : Fin d → ℂ) : (dirv (k, true)) ⬝ᵥ y = Complex.I * y k := by
  simp [dirv]

theorem D_phi_lower (d : ℕ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) (H : Matrix (Fin d) (Fin d) ℂ) (hs : H.IsSymm)
    (Γ : ℝ) (hΓ : 0 ≤ Γ) (hH : ∀ i j, ‖H i j‖ ≤ Γ) {Λ : ℝ} (hΛ : 0 < Λ)
    (hlow : ∀ x : Fin d → ℂ, ‖x‖ ≤ Λ * ‖H *ᵥ x‖) (x : Fin d → ℂ) :
    ∃ l : Fin d × Bool, ‖c‖ / (4 * Λ) * ‖x‖ ≤ |fderiv ℝ (D_phi d c H) x (dirv l)| := by
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  by_contra hcon
  push Not at hcon
  have hx0 : 0 < ‖x‖ := by
    have := hcon (⟨0, hd⟩, false)
    have h2 := (abs_nonneg _).trans_lt this
    by_contra h3
    have h4 : ‖x‖ = 0 := le_antisymm (not_lt.1 h3) (norm_nonneg x)
    rw [h4, mul_zero] at h2
    exact lt_irrefl _ h2
  have hk : ∀ k, ‖(H *ᵥ x) k‖ ≤ ‖x‖ / (2 * Λ) := by
    intro k
    have h1 := hcon (k, false)
    have h2 := hcon (k, true)
    rw [D_phi_fderiv d c H hs Γ hΓ hH] at h1 h2
    simp only [D_bilC_apply, D_dirv_false, D_dirv_true] at h1 h2
    have h3 : (c * (Complex.I * (H *ᵥ x) k)).re = - (c * (H *ᵥ x) k).im := by
      have : c * (Complex.I * (H *ᵥ x) k) = Complex.I * (c * (H *ᵥ x) k) := by ring
      rw [this, Complex.I_mul_re]
    rw [h3, abs_neg] at h2
    have h4 : ‖c * (H *ᵥ x) k‖ ≤ |(c * (H *ᵥ x) k).re| + |(c * (H *ᵥ x) k).im| := Complex.norm_le_abs_re_add_abs_im _
    rw [norm_mul] at h4
    have h5 : ‖c‖ * ‖(H *ᵥ x) k‖ ≤ ‖c‖ * (‖x‖ / (2 * Λ)) := by
      have : ‖c‖ * (‖x‖ / (2 * Λ)) = ‖c‖ / (4 * Λ) * ‖x‖ + ‖c‖ / (4 * Λ) * ‖x‖ := by field_simp; ring
      rw [this]
      linarith
    exact le_of_mul_le_mul_left h5 hc0
  have h6 : ‖H *ᵥ x‖ ≤ ‖x‖ / (2 * Λ) := (pi_norm_le_iff_of_nonneg (by positivity)).2 hk
  have h7 := hlow x
  have h8 : Λ * ‖H *ᵥ x‖ ≤ ‖x‖ / 2 := by
    calc Λ * ‖H *ᵥ x‖ ≤ Λ * (‖x‖ / (2 * Λ)) := by gcongr
      _ = ‖x‖ / 2 := by field_simp
  linarith

theorem D_psi_eq_osc (d : ℕ) (β t : ℂ) (ht : t ≠ 0) (H : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) = osc (D_phi d (β * (‖t‖ : ℂ) / t) H) ‖t‖ x := by
  have hn : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
  unfold psi osc D_phi
  congr 3
  rw [eq_div_iff hn, mul_comm, ← Complex.re_ofReal_mul]
  congr 1
  field_simp

theorem D_gau_continuous (d : ℕ) (δ : ℝ) : Continuous (D_gau d δ) := (D_gau_contDiff d δ 0).continuous

theorem D_gau_nonneg (d : ℕ) (δ : ℝ) (x : Fin d → ℂ) : 0 ≤ D_gau d δ x := (Real.exp_pos _).le

theorem D_gau_integrable (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    Integrable (D_gau d δ) (muPi β (Fin d)) := by
  have := isAddHaar_muPi d β hβ
  have h1 : Integrable (D_gau d 1) (muPi β (Fin d)) := by
    have hfin : (Module.finrank ℝ (Fin d → ℂ) : ℝ) < ((2 * (d + 1) : ℕ) : ℝ) := by
      have : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
        simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
      rw [this]
      exact_mod_cast (by omega : 2 * d < 2 * (d + 1))
    have hint := (integrable_one_add_norm (μ := muPi β (Fin d)) hfin).const_mul
      (2 ^ (d + 1) * ((d + 1).factorial : ℝ) * Real.exp 1)
    refine hint.mono' (D_gau_continuous d 1).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (D_gau_nonneg d 1 x), Real.rpow_neg (by positivity), Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    have h2 : D_gau d 1 x ≤ Real.exp (-‖x‖ ^ 2) := by
      have : D_gau d 1 x = Real.exp (- D_nsq d x) := by simp [D_gau, D_nsq]
      rw [this]
      exact Real.exp_le_exp.2 (neg_le_neg (D_norm_sq_le_nsq d x))
    calc (1 + ‖x‖) ^ (2 * (d + 1)) * D_gau d 1 x ≤ (1 + ‖x‖) ^ (2 * (d + 1)) * Real.exp (-‖x‖ ^ 2) := by gcongr
      _ ≤ _ := D_exp_decay (d + 1) ‖x‖ (norm_nonneg x)
  rw [D_gau_scale d δ hδ.le]
  exact h1.comp_smul (Real.sqrt_pos.2 hδ).ne'

theorem D_osc_norm {E : Type*} (φ : E → ℝ) (τ : ℝ) (x : E) : ‖osc φ τ x‖ = 1 := by
  unfold osc
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem D_osc_continuous {E : Type*} [TopologicalSpace E] {φ : E → ℝ} (hφ : Continuous φ) (τ : ℝ) :
    Continuous (osc φ τ) := by
  unfold osc
  fun_prop

theorem D_compare (d : ℕ) (hd : 0 < d) (β : ℂ) (hβ : β ≠ 0) (ρ Γ Λ : ℝ) (hρ : 0 < ρ) (hΓ : 0 < Γ) (hΛ : 0 < Λ) :
    ∃ C : ℝ, ∀ H : Matrix (Fin d) (Fin d) ℂ, H.IsSymm → (∀ i j, ‖H i j‖ ≤ Γ) →
      (∀ x : Fin d → ℂ, ‖x‖ ≤ Λ * ‖H *ᵥ x‖) → ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ 1 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ‖∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d)) -
            gaussInt β d H t δ‖ ≤ C * ‖t‖ ^ (d + 1) := by
  have hβ0 : 0 < ‖β‖ := norm_pos_iff.2 hβ
  obtain ⟨C, hC0, hC⟩ := osc_bound d 1 β hβ (‖β‖ * (d * (d * Γ))) (‖β‖ / (4 * Λ)) (by positivity)
  obtain ⟨K, hK0, hK⟩ := D_amp d (d + 1 + 1) (by omega) hρ
  refine ⟨C * K, ?_⟩
  intro H hs hH hlow t ht ht1 δ hδ hδ1
  have := isAddHaar_muPi d β hβ
  have hτ : 0 < ‖t‖ := norm_pos_iff.2 ht
  set τ := ‖t‖ with hτdef
  set σ := Real.sqrt τ with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hτ
  have hσ1 : σ ≤ 1 := Real.sqrt_le_one.2 ht1
  set c : ℂ := β * (τ : ℂ) / t with hcdef
  have hcn : ‖c‖ = ‖β‖ := by
    rw [hcdef, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le, ← hτdef]
    field_simp
  have hc0 : c ≠ 0 := by rw [← norm_pos_iff, hcn]; exact hβ0
  set φ := D_phi d c H with hφdef
  have hφc : ∀ n : ℕ, ContDiff ℝ n φ := D_phi_contDiff d c H Γ hΓ.le hH
  have hφcont : Continuous φ := (hφc 0).continuous
  have hoscc : Continuous (osc φ τ) := D_osc_continuous hφcont τ
  have hpsi : ∀ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) = osc φ τ x := D_psi_eq_osc d β t ht H
  have hφS : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 1 (d + 1 + 1) (‖β‖ * (d * (d * Γ))) (fderiv ℝ φ) := by
    rw [hφdef, D_phi_fderiv d c H hs Γ hΓ.le hH]
    refine (Sym.clm (D_bilC d c H Γ hΓ.le hH) hσ).mono (fun x _ => D_wt_pos hσ x) le_rfl ?_
    rw [← hcn]
    exact D_bilC_norm d c H Γ hΓ.le hH
  have hφl : ∀ x ∈ (Set.univ : Set (Fin d → ℂ)), ∃ l : Fin d × Bool,
      ‖β‖ / (4 * Λ) * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)| := by
    intro x _
    rw [← hcn]
    exact D_phi_lower d hd c hc0 H hs Γ hΓ.le hH hΛ hlow x

  set b : (Fin d → ℂ) → ℝ := fun x => cutB d ρ x - D_gau d δ x with hbdef
  have hbcont : Continuous b := ((D_cut_contDiff d hρ 0).continuous).sub (D_gau_continuous d δ)
  have hχint : Integrable (cutB d ρ) (muPi β (Fin d)) :=
    ((D_cut_contDiff d hρ 0).continuous).integrable_of_hasCompactSupport (D_cut_compact d hρ)
  have hGint := D_gau_integrable d β hβ δ hδ
  have hbint : Integrable b (muPi β (Fin d)) := hχint.sub hGint
  have hR : ∀ R : ℝ, 1 ≤ R →
      ‖∫ x, osc φ τ x • (((cutB d 2 (R⁻¹ • x) * b x : ℝ)) : ℂ) ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + 1) := by
    intro R hR1
    have hR0 : 0 < R := by linarith
    refine hC Set.univ φ τ hτ (hφc _) hφS hφl ℂ _ K hK0 ?_ (Set.subset_univ _) ?_
    · have h1 : HasCompactSupport (fun x : Fin d → ℂ => cutB d 2 (R⁻¹ • x)) :=
        (D_cut_compact d two_pos).comp_smul (inv_pos.2 hR0).ne'
      have h2 : HasCompactSupport (fun x : Fin d → ℂ => cutB d 2 (R⁻¹ • x) * b x) := h1.mul_right
      exact h2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    · have h1 := (hK δ hδ hδ1 σ hσ hσ1 R hR1).comp_clm Complex.ofRealCLM
      rw [Complex.ofRealCLM_norm, one_mul] at h1
      exact D_sym_cast (by norm_num) h1

  have hlim : Tendsto (fun n : ℕ => ∫ x, osc φ τ x • (((cutB d 2 (((n : ℝ) + 1)⁻¹ • x) * b x : ℝ)) : ℂ)
      ∂(muPi β (Fin d))) atTop (𝓝 (∫ x, osc φ τ x • ((b x : ℝ) : ℂ) ∂(muPi β (Fin d)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖b x‖) (fun n => ?_) hbint.norm (fun n => ?_) ?_
    · refine Continuous.aestronglyMeasurable ?_
      have h2 : Continuous (fun x : Fin d → ℂ => cutB d 2 (((n : ℝ) + 1)⁻¹ • x)) :=
        ((D_cut_contDiff d two_pos 0).continuous).comp (continuous_const_smul _)
      exact hoscc.smul (Complex.continuous_ofReal.comp (h2.mul hbcont))
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_smul, D_osc_norm, one_mul, Complex.norm_real, norm_mul]
      have h3 : ‖cutB d 2 (((n : ℝ) + 1)⁻¹ • x)‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (D_cut_nonneg d two_pos _)]
        exact D_cut_le_one d two_pos _
      calc _ ≤ 1 * ‖b x‖ := by gcongr
        _ = ‖b x‖ := one_mul _
    · refine Filter.Eventually.of_forall fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
      have h4 : ‖x‖ ≤ (n : ℝ) + 1 := by
        have := (Nat.le_ceil ‖x‖).trans (by exact_mod_cast hn : ((⌈‖x‖⌉₊ : ℕ) : ℝ) ≤ (n : ℝ))
        linarith
      have h5 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h6 : ‖((n : ℝ) + 1)⁻¹ • x‖ ≤ 2 / 2 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 h5).le, inv_mul_le_iff₀ h5]
        linarith
      rw [D_cut_one d two_pos h6, one_mul]
  have hmain : ‖∫ x, osc φ τ x • ((b x : ℝ) : ℂ) ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + 1) :=
    le_of_tendsto' hlim.norm (fun n => hR _ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))

  have hI1 : Integrable (fun x : Fin d → ℂ => osc φ τ x * ((cutB d ρ x : ℝ) : ℂ)) (muPi β (Fin d)) := by
    refine hχint.norm.mono' (hoscc.mul (Complex.continuous_ofReal.comp
      (D_cut_contDiff d hρ 0).continuous)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, D_osc_norm, one_mul, Complex.norm_real]
  have hI2 : Integrable (fun x : Fin d → ℂ => ((D_gau d δ x : ℝ) : ℂ) * osc φ τ x) (muPi β (Fin d)) := by
    refine hGint.norm.mono' ((Complex.continuous_ofReal.comp (D_gau_continuous d δ)).mul
      hoscc).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, D_osc_norm, mul_one, Complex.norm_real]
  have hid : ∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d)) -
      gaussInt β d H t δ = ∫ x, osc φ τ x • ((b x : ℝ) : ℂ) ∂(muPi β (Fin d)) := by
    unfold gaussInt
    simp_rw [hpsi]
    refine (integral_sub hI1 hI2).symm.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hbdef, smul_eq_mul, Complex.ofReal_sub, D_gau]
    ring
  rw [hid]
  exact hmain

theorem model (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (ρ Γ Λ : ℝ) (hρ : 0 < ρ) (hΓ : 0 < Γ) (hΛ : 0 < Λ) : ∃ C : ℝ,
    ∀ H : Matrix (Fin d) (Fin d) ℂ, H.IsSymm → (∀ i j, ‖H i j‖ ≤ Γ) → (∀ x : Fin d → ℂ, ‖x‖ ≤ Λ * ‖H *ᵥ x‖) →
      ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ 1 →
        ‖∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d)) -
            ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)‖ ≤ C * ‖t‖ ^ (d + 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, ?_⟩
    intro H _ _ _ t _ _
    have h1 : muPi β (Fin 0) = Measure.dirac (0 : Fin 0 → ℂ) := by
      unfold muPi
      exact Measure.pi_of_empty _ _
    rw [h1, integral_dirac, D_cut_one 0 hρ (by simp; positivity), Matrix.det_isEmpty]
    simp [psi]
  · obtain ⟨C, hC⟩ := D_compare d hd β hβ ρ Γ Λ hρ hΓ hΛ
    refine ⟨C, ?_⟩
    intro H hs hH hlow t ht ht1
    have hdet : H.det ≠ 0 := by
      intro h0
      obtain ⟨v, hv, hHv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      have := hlow v
      rw [hHv, norm_zero, mul_zero] at this
      exact hv (norm_le_zero_iff.1 this)
    have hG := gaussian_multi_integral d β t H hβ ht hs hdet
    have hlim := (tendsto_const_nhds (x := ∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) *
      ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d))).sub hG).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with δ hδ
    exact hC H hs hH hlow t ht ht1 δ hδ.1 hδ.2

end

end Formalism.FourierDecayAlt.P.StationaryPhaseModel

end PartD

section PartE

open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel

section TaylorInS

variable {d : ℕ} {β : ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem norm_oscillatory_factor {E : Type*} (φ : E → ℝ) (τ : ℝ) (x : E) : ‖osc φ τ x‖ = 1 := by
  unfold osc
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_oscillatory_factor {E : Type*} [TopologicalSpace E] {φ : E → ℝ} (hφ : Continuous φ) (τ : ℝ) :
    Continuous (osc φ τ) := by
  unfold osc
  fun_prop

theorem hasDerivAt_exp_linear_phase (a p τ s : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (((a + s * p) / τ : ℝ) : ℂ)))
      ((Complex.I * ((p / τ : ℝ) : ℂ)) * Complex.exp (Complex.I * (((a + s * p) / τ : ℝ) : ℂ))) s := by
  have h1 : HasDerivAt (fun s : ℝ => (a + s * p) / τ) (p / τ) s := by
    have := ((hasDerivAt_id s).mul_const p).const_add a |>.div_const τ
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => (((a + s * p) / τ : ℝ) : ℂ)) ((p / τ : ℝ) : ℂ) s := h1.ofReal_comp
  have h3 := (h2.const_mul Complex.I).cexp
  convert h3 using 1
  ring

theorem hasDerivAt_oscillatory_integral (hβ : β ≠ 0) (φ₀ P : (Fin d → ℂ) → ℝ) (hφ₀ : Continuous φ₀) (hP : Continuous P) (τ : ℝ)
    (c : (Fin d → ℂ) → V) (hc : Continuous c) (hcs : HasCompactSupport c) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, osc (fun y => φ₀ y + s * P y) τ x • c x ∂(muPi β (Fin d)))
      (∫ x, osc (fun y => φ₀ y + s * P y) τ x • ((Complex.I * ((P x / τ : ℝ) : ℂ)) • c x) ∂(muPi β (Fin d))) s := by
  have := isAddHaar_muPi d β hβ
  have hcont : ∀ s : ℝ, Continuous (fun x => osc (fun y => φ₀ y + s * P y) τ x • c x) := fun s =>
    (continuous_oscillatory_factor (by fun_prop) τ).smul hc
  have hcont' : ∀ s : ℝ, Continuous
      (fun x => osc (fun y => φ₀ y + s * P y) τ x • ((Complex.I * ((P x / τ : ℝ) : ℂ)) • c x)) := fun s =>
    (continuous_oscillatory_factor (by fun_prop) τ).smul ((by fun_prop : Continuous fun x => (Complex.I * ((P x / τ : ℝ) : ℂ))).smul hc)
  have hb : Continuous (fun x => ‖P x / τ‖ * ‖c x‖) := by fun_prop
  have hbs : HasCompactSupport (fun x => ‖P x / τ‖ * ‖c x‖) := hcs.norm.mul_left
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muPi β (Fin d)) (𝕜 := ℝ)
    (F := fun (s : ℝ) x => osc (fun y => φ₀ y + s * P y) τ x • c x)
    (F' := fun (s : ℝ) x => osc (fun y => φ₀ y + s * P y) τ x • ((Complex.I * ((P x / τ : ℝ) : ℂ)) • c x))
    (x₀ := s) (s := Set.univ) (bound := fun x => ‖P x / τ‖ * ‖c x‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    ((hcont s).integrable_of_hasCompactSupport hcs.smul_left)
    (hcont' s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x s _ => by
      rw [norm_smul, norm_smul, norm_oscillatory_factor, one_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real])
    (hb.integrable_of_hasCompactSupport hbs)
    (Filter.Eventually.of_forall fun x s _ => by
      have h := (hasDerivAt_exp_linear_phase (φ₀ x) (P x) τ s).smul_const (c x)
      simp only [osc]
      convert h using 1
      rw [smul_smul, mul_comm])
  exact key.2

theorem E_taylor {d : ℕ} {β : ℂ} (hβ : β ≠ 0) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (φ₀ P : (Fin d → ℂ) → ℝ) (hφ₀ : Continuous φ₀) (hP : Continuous P) (τ : ℝ) (hτ : 0 < τ)
    (c : (Fin d → ℂ) → V) (hc : Continuous c) (hcs : HasCompactSupport c) (M : ℝ)
    (hM : ∀ s ∈ Set.Icc (0:ℝ) 1,
      ‖∫ x, osc (fun y => φ₀ y + s * P y) τ x • ((P x * P x) • c x) ∂(muPi β (Fin d))‖ ≤ M) :
    ‖∫ x, osc (fun y => φ₀ y + P y) τ x • c x ∂(muPi β (Fin d)) - ∫ x, osc φ₀ τ x • c x ∂(muPi β (Fin d))
      - (Complex.I / (τ : ℂ)) • ∫ x, osc φ₀ τ x • (P x • c x) ∂(muPi β (Fin d))‖ ≤ M / τ ^ 2 := by
  set μ := muPi β (Fin d) with hμ
  set c₁ : (Fin d → ℂ) → V := fun x => (Complex.I * ((P x / τ : ℝ) : ℂ)) • c x with hc₁def
  have hc₁ : Continuous c₁ := (by fun_prop : Continuous fun x => (Complex.I * ((P x / τ : ℝ) : ℂ))).smul hc
  have hcs₁ : HasCompactSupport c₁ := hcs.smul_left
  set J : ℝ → V := fun s => ∫ x, osc (fun y => φ₀ y + s * P y) τ x • c x ∂μ with hJ
  set J₁ : ℝ → V := fun s => ∫ x, osc (fun y => φ₀ y + s * P y) τ x • c₁ x ∂μ with hJ₁
  set J₂ : ℝ → V := fun s => ∫ x, osc (fun y => φ₀ y + s * P y) τ x •
    ((Complex.I * ((P x / τ : ℝ) : ℂ)) • c₁ x) ∂μ with hJ₂
  have hd0 : ∀ s, HasDerivAt J (J₁ s) s := fun s => hasDerivAt_oscillatory_integral hβ φ₀ P hφ₀ hP τ c hc hcs s
  have hd1 : ∀ s, HasDerivAt J₁ (J₂ s) s := fun s => hasDerivAt_oscillatory_integral hβ φ₀ P hφ₀ hP τ c₁ hc₁ hcs₁ s
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hJ₂eq : ∀ s, J₂ s = (-(1 / (τ : ℂ) ^ 2)) •
      ∫ x, osc (fun y => φ₀ y + s * P y) τ x • ((P x * P x) • c x) ∂μ := by
    intro s
    rw [hJ₂, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hc₁def]
    rw [← Complex.coe_smul (P x * P x) (c x), smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring
  have hJ₂le : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖J₂ s‖ ≤ M / τ ^ 2 := by
    intro s hs
    rw [hJ₂eq, norm_smul, norm_neg, norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg hτ.le,
      div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (hM s hs) (by positivity)
  have hM0 : 0 ≤ M / τ ^ 2 := le_trans (norm_nonneg _) (hJ₂le 0 (by simp))
  have h1 : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖J₁ s - J₁ 0‖ ≤ M / τ ^ 2 * (s - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun s _ => (hd1 s).hasDerivWithinAt)
      (fun s hs => hJ₂le s (Set.Ico_subset_Icc_self hs))
  have h2 : ‖(J 1 - (1:ℝ) • J₁ 0) - (J 0 - (0:ℝ) • J₁ 0)‖ ≤ M / τ ^ 2 := by
    refine norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun s : ℝ => J s - s • J₁ 0)
      (f' := fun s => J₁ s - J₁ 0) (fun s _ => ?_) (fun s hs => ?_)
    · have h := (hd0 s).sub ((hasDerivAt_id s).smul_const (J₁ 0))
      rw [one_smul] at h
      exact h.hasDerivWithinAt
    · have hs' := Set.Ico_subset_Icc_self hs
      refine (h1 s hs').trans ?_
      have : s - 0 ≤ 1 := by linarith [hs'.2]
      calc M / τ ^ 2 * (s - 0) ≤ M / τ ^ 2 * 1 := mul_le_mul_of_nonneg_left this hM0
        _ = M / τ ^ 2 := mul_one _
  have e1 : J 1 = ∫ x, osc (fun y => φ₀ y + P y) τ x • c x ∂μ := by simp only [hJ, one_mul]
  have e0 : J 0 = ∫ x, osc φ₀ τ x • c x ∂μ := by simp only [hJ, zero_mul, add_zero]
  have e2 : J₁ 0 = (Complex.I / (τ : ℂ)) • ∫ x, osc φ₀ τ x • (P x • c x) ∂μ := by
    simp only [hJ₁, zero_mul, add_zero]
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hc₁def]
    rw [← Complex.coe_smul (P x) (c x), smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [e1, e0, e2] at h2
  convert h2 using 2
  rw [one_smul, zero_smul]
  abel

end TaylorInS

section ECut

variable {d : ℕ} {ρ : ℝ}

noncomputable def E_bump (d : ℕ) (ρ : ℝ) (h : 0 < ρ) : ContDiffBump (0 : Fin d → ℂ) :=
  ⟨ρ / 2, ρ, half_pos h, half_lt_self h⟩

theorem E_cut_eq (hρ : 0 < ρ) : cutB d ρ = (E_bump d ρ hρ : (Fin d → ℂ) → ℝ) := by
  funext x
  simp [cutB, hρ, E_bump]

theorem E_cut_contDiff (hρ : 0 < ρ) (n : ℕ) : ContDiff ℝ n (cutB d ρ) := by
  rw [E_cut_eq hρ]
  exact (E_bump d ρ hρ).contDiff

theorem E_cut_one (hρ : 0 < ρ) {x : Fin d → ℂ} (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) (ρ / 2)) :
    cutB d ρ x = 1 := by
  rw [E_cut_eq hρ]
  exact (E_bump d ρ hρ).one_of_mem_closedBall hx

theorem E_cut_tsupport (hρ : 0 < ρ) : tsupport (cutB d ρ) = Metric.closedBall (0 : Fin d → ℂ) ρ := by
  rw [E_cut_eq hρ]
  exact (E_bump d ρ hρ).tsupport_eq

theorem E_cut_compact (hρ : 0 < ρ) : HasCompactSupport (cutB d ρ) := by
  rw [E_cut_eq hρ]
  exact (E_bump d ρ hρ).hasCompactSupport

theorem E_cut_neg (hρ : 0 < ρ) (x : Fin d → ℂ) : cutB d ρ (-x) = cutB d ρ x := by
  rw [E_cut_eq hρ]
  exact (E_bump d ρ hρ).neg x

theorem E_cut_bound (hρ : 0 < ρ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ, i ≤ N → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ C := by
  have h : ∀ i : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ C := fun i =>
    ((E_cut_compact hρ).iteratedFDeriv i).exists_bound_of_continuous
      ((E_cut_contDiff hρ i).continuous_iteratedFDeriv le_rfl)
  choose C hC using h
  refine ⟨∑ i ∈ Finset.range (N + 1), |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i hi x => ?_⟩
  refine (hC i x).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

end ECut

section EQuad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem E_symm {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x y : E) :
    fderiv ℝ (fderiv ℝ φ) 0 x y = fderiv ℝ (fderiv ℝ φ) 0 y x :=
  (hφ.contDiffAt (x := 0)).isSymmSndFDerivAt (by simp) x y

theorem E_quad_hasFDerivAt {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E) :
    HasFDerivAt (quad φ) (fderiv ℝ (fderiv ℝ φ) 0 x) x := by
  have h := (fderiv ℝ (fderiv ℝ φ) 0).hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
  have h2 := (h.const_mul (1 / 2 : ℝ)).const_add (φ 0)
  refine h2.congr_fderiv ?_
  ext v
  simp [E_symm hφ v x]
  ring

theorem E_quad_fderiv {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) :
    fderiv ℝ (quad φ) = fun x => fderiv ℝ (fderiv ℝ φ) 0 x :=
  funext fun x => (E_quad_hasFDerivAt hφ x).fderiv

theorem E_quad_contDiff (φ : E → ℝ) (n : ℕ) : ContDiff ℝ n (quad φ) := by
  unfold quad
  fun_prop

theorem E_quad_neg (φ : E → ℝ) (x : E) : quad φ (-x) = quad φ x := by
  simp [quad]

end EQuad

section EP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def E_P (φ : E → ℝ) (x : E) : ℝ := φ x - quad φ x

noncomputable def E_Pe (φ : E → ℝ) (x : E) : ℝ := (1 / 2 : ℝ) * (E_P φ x + E_P φ (-x))

theorem E_quad_bound {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) {r Γ : ℝ} (hr : 0 < r) (h0 : ‖φ 0‖ ≤ Γ)
    (h2 : ‖fderiv ℝ (fderiv ℝ φ) 0‖ ≤ Γ) (i : ℕ) {x : E} (hx : x ∈ Metric.closedBall (0 : E) r) :
    ‖iteratedFDeriv ℝ i (quad φ) x‖ ≤ Γ * (r + 1) ^ 2 := by
  have hxr : ‖x‖ ≤ r := by simpa using hx
  have hΓ : 0 ≤ Γ := (norm_nonneg _).trans h0
  cases i with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have h1 : ‖fderiv ℝ (fderiv ℝ φ) 0 x x‖ ≤ Γ * r * r := by
      refine ((fderiv ℝ (fderiv ℝ φ) 0 x).le_opNorm x).trans ?_
      refine mul_le_mul (((fderiv ℝ (fderiv ℝ φ) 0).le_opNorm x).trans ?_) hxr (norm_nonneg _) (by positivity)
      exact mul_le_mul h2 hxr (norm_nonneg _) hΓ
    have h3 : ‖quad φ x‖ ≤ ‖φ 0‖ + 1 / 2 * ‖fderiv ℝ (fderiv ℝ φ) 0 x x‖ := by
      unfold quad
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      norm_num
    nlinarith [mul_nonneg hΓ hr.le, mul_nonneg (mul_nonneg hΓ hr.le) hr.le]
  | succ i =>
    rw [← norm_iteratedFDeriv_fderiv, E_quad_fderiv hφ]
    have h := (Sym.clm (A := Set.univ) (N := i) (fderiv ℝ (fderiv ℝ φ) 0) (σ := 1) one_pos).2 x trivial i le_rfl
    refine h.trans ?_
    have hw1 : (1 : ℝ) ≤ wt 1 x := by unfold wt; linarith [norm_nonneg x]
    have hw2 : wt 1 x ≤ r + 1 := by unfold wt; linarith
    have hz : wt 1 x ^ ((1 : ℤ) - (i : ℤ)) ≤ r + 1 := by
      cases i with
      | zero => simpa using hw2
      | succ j =>
        refine (zpow_le_one_of_nonpos₀ hw1 (by push_cast; omega)).trans (by linarith)
    have hz0 : 0 ≤ wt 1 x ^ ((1 : ℤ) - (i : ℤ)) := zpow_nonneg (by linarith) _
    calc ‖fderiv ℝ (fderiv ℝ φ) 0‖ * wt 1 x ^ ((1 : ℤ) - (i : ℤ)) ≤ Γ * (r + 1) :=
          mul_le_mul h2 hz hz0 hΓ
      _ ≤ Γ * (r + 1) ^ 2 := by nlinarith [mul_nonneg hΓ hr.le]

theorem E_P_contDiff {φ : E → ℝ} {n : ℕ} (hφ : ContDiff ℝ n φ) : ContDiff ℝ n (E_P φ) :=
  hφ.sub (E_quad_contDiff φ n)

theorem E_P_fderiv {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) :
    fderiv ℝ (E_P φ) = fun x => fderiv ℝ φ x - fderiv ℝ (fderiv ℝ φ) 0 x := by
  funext x
  exact (((hφ.differentiable (by norm_num)) x).hasFDerivAt.sub (E_quad_hasFDerivAt hφ x)).fderiv

theorem E_P_vanish {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : fderiv ℝ φ 0 = 0) :
    ∀ i : ℕ, i < 3 → iteratedFDeriv ℝ i (E_P φ) 0 = 0 := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (E_P φ)) 0 = 0 := by
    rw [E_P_fderiv hφ]
    have := ((hd 0).hasFDerivAt.sub (fderiv ℝ (fderiv ℝ φ) 0).hasFDerivAt).fderiv
    rw [sub_self] at this
    exact this
  intro i hi
  rw [← norm_eq_zero]
  interval_cases i
  · rw [norm_iteratedFDeriv_zero]
    simp [E_P, quad]
  · rw [norm_iteratedFDeriv_one, E_P_fderiv hφ]
    simp [hc]
  · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, h2, norm_zero]

theorem E_iteratedFDeriv_comp_neg {f : E → F} {n : ℕ} (hf : ContDiff ℝ n f) {i : ℕ} (hi : i ≤ n) (x : E) :
    iteratedFDeriv ℝ i (fun y => f (-y)) x = (-1 : ℝ) ^ i • iteratedFDeriv ℝ i f (-x) := by
  have h := (-(ContinuousLinearMap.id ℝ E)).iteratedFDeriv_comp_right hf x (i := i) (by exact_mod_cast hi)
  have h1 : (f ∘ ⇑(-(ContinuousLinearMap.id ℝ E))) = fun y => f (-y) := by
    funext y; simp
  rw [h1] at h
  rw [h]
  ext v
  have h2 := (iteratedFDeriv ℝ i f (-x)).map_smul_univ (fun _ => (-1 : ℝ)) v
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply]
  rw [← h2]
  simp

end EP

section EP2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem E_hess_le {φ : E → ℝ} {n : ℕ} (h2n : 2 ≤ n) {r Γ : ℝ} (hr : 0 < r)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) :
    ‖fderiv ℝ (fderiv ℝ φ) 0‖ ≤ Γ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact hb 0 (Metric.mem_closedBall_self hr.le) 2 h2n

theorem E_P_bound {φ : E → ℝ} {n : ℕ} (h2n : 2 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ : ℝ} (hr : 0 < r)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) :
    ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n →
      ‖iteratedFDeriv ℝ i (E_P φ) x‖ ≤ Γ + Γ * (r + 1) ^ 2 := by
  intro x hx i hi
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by exact_mod_cast h2n)
  have h0 : ‖φ 0‖ ≤ Γ := by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hb 0 (Metric.mem_closedBall_self hr.le) 0 (Nat.zero_le _)
  have hin : ((i : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast hi
  have he : E_P φ = φ - quad φ := rfl
  rw [he, iteratedFDeriv_sub_apply (hφ.of_le hin).contDiffAt (E_quad_contDiff φ i).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (hb x hx i hi) (E_quad_bound hφ2 hr h0 (E_hess_le h2n hr hb) i hx))

theorem E_P_sym {φ : E → ℝ} {n : ℕ} (h3n : 3 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ σ : ℝ} (hr : 0 < r)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) 3 n ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n) (E_P φ) := by
  have h := Sym.of_vanish (f := E_P φ) 3 hr hσ hσ1 h3n (E_P_contDiff hφ) (E_P_bound (by omega) hφ hr hb)
    (E_P_vanish (hφ.of_le (by exact_mod_cast (by omega : 2 ≤ n))) hc)
  exact_mod_cast h

theorem E_P_fderiv_le {φ : E → ℝ} {n : ℕ} (h3n : 3 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ : ℝ} (hr : 0 < r)
    (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ)
    {x : E} (hx : x ∈ Metric.closedBall (0 : E) r) :
    ‖fderiv ℝ (E_P φ) x‖ ≤ (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n * ‖x‖ ^ 2 := by
  set K := (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n with hK
  have ht : Tendsto (fun σ : ℝ => K * (‖x‖ + σ) ^ 2) (𝓝[>] 0) (𝓝 (K * (‖x‖ + 0) ^ 2)) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact (Continuous.tendsto (by fun_prop) 0)
  rw [add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with σ hσ
  have h := (E_P_sym h3n hφ hr hσ.1 hσ.2 hc hb).2 x hx 1 (by omega)
  rw [norm_iteratedFDeriv_one] at h
  have h2 : wt σ x ^ ((3 : ℤ) - ((1 : ℕ) : ℤ)) = (‖x‖ + σ) ^ 2 := by
    norm_num [wt]
  rwa [h2] at h

theorem E_Pe_contDiff {φ : E → ℝ} {n : ℕ} (hφ : ContDiff ℝ n φ) : ContDiff ℝ n (E_Pe φ) :=
  contDiff_const.mul ((E_P_contDiff hφ).add ((E_P_contDiff hφ).comp contDiff_neg))

theorem E_Pe_iterated {φ : E → ℝ} {n : ℕ} (hφ : ContDiff ℝ n φ) {i : ℕ} (hi : i ≤ n) (x : E) :
    iteratedFDeriv ℝ i (E_Pe φ) x =
      (1 / 2 : ℝ) • (iteratedFDeriv ℝ i (E_P φ) x + (-1 : ℝ) ^ i • iteratedFDeriv ℝ i (E_P φ) (-x)) := by
  have hin : ((i : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast hi
  have hP : ContDiff ℝ i (E_P φ) := (E_P_contDiff hφ).of_le hin
  have he : E_Pe φ = (1 / 2 : ℝ) • (E_P φ + fun y => E_P φ (-y)) := by
    funext y
    simp [E_Pe]
  have hPn : ContDiff ℝ i (fun y => E_P φ (-y)) := hP.comp contDiff_neg
  have hadd : ContDiff ℝ i (E_P φ + fun y => E_P φ (-y)) := hP.add hPn
  rw [he, iteratedFDeriv_const_smul_apply hadd.contDiffAt,
    iteratedFDeriv_add_apply hP.contDiffAt hPn.contDiffAt,
    E_iteratedFDeriv_comp_neg hP le_rfl]

theorem E_Pe_sym {φ : E → ℝ} {n : ℕ} (h4n : 4 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ σ : ℝ} (hr : 0 < r)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) 4 n ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n) (E_Pe φ) := by
  have hv := E_P_vanish (hφ.of_le (by exact_mod_cast (by omega : 2 ≤ n))) hc
  have h := Sym.of_vanish (f := E_Pe φ) (M := Γ + Γ * (r + 1) ^ 2) 4 hr hσ hσ1 h4n (E_Pe_contDiff hφ) ?_ ?_
  · exact_mod_cast h
  · intro x hx i hi
    have hx' : -x ∈ Metric.closedBall (0 : E) r := by simpa using hx
    rw [E_Pe_iterated hφ hi, norm_smul]
    have h1 := E_P_bound (by omega) hφ hr hb x hx i hi
    have h2 := E_P_bound (by omega) hφ hr hb (-x) hx' i hi
    have h3 : ‖iteratedFDeriv ℝ i (E_P φ) x + (-1 : ℝ) ^ i • iteratedFDeriv ℝ i (E_P φ) (-x)‖ ≤
        ‖iteratedFDeriv ℝ i (E_P φ) x‖ + ‖iteratedFDeriv ℝ i (E_P φ) (-x)‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
      simp
    norm_num
    linarith
  · intro i hi
    rw [E_Pe_iterated hφ (by omega), neg_zero]
    by_cases h3 : i < 3
    · rw [hv i h3]; simp
    · have : i = 3 := by omega
      subst this
      norm_num

end EP2

section EPhase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem E_ph_contDiff {φ : E → ℝ} {n : ℕ} (hφ : ContDiff ℝ n φ) (s : ℝ) :
    ContDiff ℝ n (fun y => quad φ y + s * E_P φ y) :=
  (E_quad_contDiff φ n).add (contDiff_const.mul (E_P_contDiff hφ))

theorem E_ph_fderiv {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (s : ℝ) :
    fderiv ℝ (fun y => quad φ y + s * E_P φ y) =
      fun x => (1 - s) • (fderiv ℝ (fderiv ℝ φ) 0 x) + s • fderiv ℝ φ x := by
  funext x
  have hP : HasFDerivAt (E_P φ) (fderiv ℝ φ x - fderiv ℝ (fderiv ℝ φ) 0 x) x :=
    ((hφ.differentiable (by norm_num)) x).hasFDerivAt.sub (E_quad_hasFDerivAt hφ x)
  have h : HasFDerivAt (fun y => quad φ y + s * E_P φ y)
      (fderiv ℝ (fderiv ℝ φ) 0 x + s • (fderiv ℝ φ x - fderiv ℝ (fderiv ℝ φ) 0 x)) x :=
    (E_quad_hasFDerivAt hφ x).add (hP.const_mul s)
  rw [h.fderiv]
  module

theorem E_ph_fderiv' {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (s : ℝ) (x v : E) :
    fderiv ℝ (fun y => quad φ y + s * E_P φ y) x v = fderiv ℝ φ x v - (1 - s) * fderiv ℝ (E_P φ) x v := by
  rw [E_ph_fderiv hφ, E_P_fderiv hφ]
  simp
  ring

theorem E_dphi_sym {φ : E → ℝ} {N : ℕ} (hN : 1 ≤ N) (hφ : ContDiff ℝ (N + 1 : ℕ) φ) {r Γ σ : ℝ} (hr : 0 < r)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ N + 1 → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) 1 N (Γ * (r + 1) ^ N) (fderiv ℝ φ) := by
  have h := Sym.of_vanish (f := fderiv ℝ φ) (M := Γ) 1 hr hσ hσ1 hN
    (hφ.fderiv_right (by exact_mod_cast le_rfl)) ?_ ?_
  · exact_mod_cast h
  · intro x hx i hi
    rw [norm_iteratedFDeriv_fderiv]
    exact hb x hx (i + 1) (by omega)
  · intro i hi
    have : i = 0 := by omega
    subst this
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero, hc, norm_zero]

theorem E_wt_pos {σ : ℝ} (hσ : 0 < σ) (x : E) : 0 < wt σ x := by
  unfold wt
  linarith [norm_nonneg x]

theorem E_ph_sym {φ : E → ℝ} {N : ℕ} (hN : 1 ≤ N) (hφ : ContDiff ℝ (N + 1 : ℕ) φ) {r Γ σ : ℝ} (hr : 0 < r)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ N + 1 → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) 1 N (Γ + Γ * (r + 1) ^ N)
      (fderiv ℝ (fun y => quad φ y + s * E_P φ y)) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by exact_mod_cast (by omega : 2 ≤ N + 1))
  rw [E_ph_fderiv hφ2]
  have h1 := Sym.const_smul (1 - s)
    (Sym.clm (A := Metric.closedBall (0 : E) r) (N := N) (fderiv ℝ (fderiv ℝ φ) 0) hσ)
  have h2 := Sym.const_smul s (E_dphi_sym hN hφ hr hσ hσ1 hc hb)
  have hB := E_hess_le (by omega : 2 ≤ N + 1) hr hb
  have hΓ : 0 ≤ Γ := (norm_nonneg _).trans hB
  refine Sym.mono (fun x _ => E_wt_pos hσ x) (h1.add h2) le_rfl ?_
  have a1 : |1 - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have a2 : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have p : 0 ≤ Γ * (r + 1) ^ N := by positivity
  have e1 : |1 - s| * ‖fderiv ℝ (fderiv ℝ φ) 0‖ ≤ 1 * Γ := mul_le_mul a1 hB (norm_nonneg _) zero_le_one
  have e2 : |s| * (Γ * (r + 1) ^ N) ≤ 1 * (Γ * (r + 1) ^ N) := mul_le_mul_of_nonneg_right a2 p
  linarith

theorem E_norm_dirv {d : ℕ} (l : Fin d × Bool) : ‖(dirv l : Fin d → ℂ)‖ = 1 := by
  unfold dirv
  rw [Pi.norm_single]
  split_ifs <;> simp

theorem E_ph_low {d : ℕ} {φ : (Fin d → ℂ) → ℝ} {n : ℕ} (h3n : 3 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ c₁ ρ : ℝ}
    (hr : 0 < r) (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ)
    (hl : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|)
    (hρr : ρ ≤ r) (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n * ρ ≤ c₁ / 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) ρ, ∃ l : Fin d × Bool,
      c₁ / 2 * ‖x‖ ≤ |fderiv ℝ (fun y => quad φ y + s * E_P φ y) x (dirv l)| := by
  intro x hx
  have hxr : x ∈ Metric.closedBall (0 : Fin d → ℂ) r := Metric.closedBall_subset_closedBall hρr hx
  have hxρ : ‖x‖ ≤ ρ := by simpa using hx
  obtain ⟨l, hl⟩ := hl x hxr
  refine ⟨l, ?_⟩
  rw [E_ph_fderiv' (hφ.of_le (by exact_mod_cast (by omega : 2 ≤ n)))]
  have h1 := E_P_fderiv_le h3n hφ hr hc hb hxr
  set K := (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n with hK
  have hK0 : 0 ≤ K := by
    have hΓ : 0 ≤ Γ := (norm_nonneg _).trans (E_hess_le (by omega : 2 ≤ n) hr hb)
    positivity
  have h2 : |fderiv ℝ (E_P φ) x (dirv l)| ≤ K * ‖x‖ ^ 2 := by
    have := (fderiv ℝ (E_P φ) x).le_opNorm (dirv l)
    rw [E_norm_dirv, mul_one, Real.norm_eq_abs] at this
    exact this.trans h1
  have a1 : |1 - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have h3 : |(1 - s) * fderiv ℝ (E_P φ) x (dirv l)| ≤ K * ‖x‖ ^ 2 := by
    rw [abs_mul]
    calc |1 - s| * |fderiv ℝ (E_P φ) x (dirv l)| ≤ 1 * (K * ‖x‖ ^ 2) :=
          mul_le_mul a1 h2 (abs_nonneg _) zero_le_one
      _ = K * ‖x‖ ^ 2 := one_mul _
  have h4 : K * ‖x‖ ^ 2 ≤ c₁ / 2 * ‖x‖ := by
    have : K * ‖x‖ ≤ c₁ / 2 := (mul_le_mul_of_nonneg_left hxρ hK0).trans hρ
    nlinarith [norm_nonneg x]
  have h5 := abs_sub_abs_le_abs_sub (fderiv ℝ φ x (dirv l)) ((1 - s) * fderiv ℝ (E_P φ) x (dirv l))
  linarith

end EPhase

section EEst

def E_OB (d q : ℕ) (β : ℂ) (Γ c₁ C : ℝ) : Prop :=
  ∀ (A : Set (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ) (τ : ℝ), 0 < τ →
      ContDiff ℝ (d + 2 + q : ℕ) φ →
      Sym A (wt (Real.sqrt τ)) 1 (d + 1 + q) Γ (fderiv ℝ φ) →
      (∀ x ∈ A, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b : (Fin d → ℂ) → V) (K : ℝ),
        0 ≤ K → HasCompactSupport b → tsupport b ⊆ A →
        Sym A (wt (Real.sqrt τ)) (2 * (q : ℤ)) (d + 1 + q) K b →
        ‖∫ x, osc φ τ x • b x ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + q)

theorem E_OB_exists (d q : ℕ) (β : ℂ) (hβ : β ≠ 0) (Γ c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 ≤ C ∧ E_OB d q β Γ c₁ C := osc_bound d q β hβ Γ c₁ hc₁

structure E_Phase (d : ℕ) (r Γ c₁ : ℝ) (φ : (Fin d → ℂ) → ℝ) : Prop where
  smooth : ContDiff ℝ (d + 6 : ℕ) φ
  bd : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∀ i : ℕ, i ≤ d + 6 → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ
  crit : fderiv ℝ φ 0 = 0
  low : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|

variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ : ℝ} {φ : (Fin d → ℂ) → ℝ}

theorem E_sqrt_pos (hτ : 0 < τ) : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ

theorem E_sqrt_le_one (hτ1 : τ ≤ 1) : Real.sqrt τ ≤ 1 := Real.sqrt_le_one.2 hτ1

theorem E_est {q : ℕ} {C : ℝ} (hq : q ≤ 4) (hOB : E_OB d q β (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) C)
    (hr : 0 < r) (hph : E_Phase d r Γ c₁ φ) (hρr : ρ ≤ r)
    (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6) * ρ ≤ c₁ / 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b : (Fin d → ℂ) → V) (K : ℝ)
    (hK : 0 ≤ K) (hbc : HasCompactSupport b) (hbs : tsupport b ⊆ Metric.closedBall (0 : Fin d → ℂ) ρ)
    (hb : Sym (Metric.closedBall (0 : Fin d → ℂ) ρ) (wt (Real.sqrt τ)) (2 * (q : ℤ)) (d + 1 + q) K b) :
    ‖∫ x, osc (fun y => quad φ y + s * E_P φ y) τ x • b x ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + q) := by
  refine hOB (Metric.closedBall (0 : Fin d → ℂ) ρ) _ τ hτ ?_ ?_ ?_ V b K hK hbc hbs hb
  · exact E_ph_contDiff (hph.smooth.of_le (by exact_mod_cast (by omega : d + 2 + q ≤ d + 6))) s
  · have h := E_ph_sym (N := d + 5) (by omega) hph.smooth hr (E_sqrt_pos hτ) (E_sqrt_le_one hτ1) hph.crit
      hph.bd hs
    exact (h.subset (Metric.closedBall_subset_closedBall hρr)).mono (fun x _ => E_wt_pos (E_sqrt_pos hτ) x)
      (by omega) le_rfl
  · exact E_ph_low (by omega) hph.smooth hr hph.crit hph.bd hph.low hρr hρ hs

theorem E_ph_zero (φ : (Fin d → ℂ) → ℝ) : (fun y => quad φ y + 0 * E_P φ y) = quad φ := by
  funext y; simp

theorem E_ph_one (φ : (Fin d → ℂ) → ℝ) : (fun y => quad φ y + E_P φ y) = φ := by
  funext y; simp [E_P]

theorem E_est_u {C : ℝ} (hOB : E_OB d 1 β (Γ * (r + 1) ^ (d + 5)) c₁ C)
    (hr : 0 < r) (hph : E_Phase d r Γ c₁ φ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b : (Fin d → ℂ) → V) (K : ℝ)
    (hK : 0 ≤ K) (hbc : HasCompactSupport b) (hbs : tsupport b ⊆ Metric.closedBall (0 : Fin d → ℂ) r)
    (hb : Sym (Metric.closedBall (0 : Fin d → ℂ) r) (wt (Real.sqrt τ)) 2 (d + 2) K b) :
    ‖∫ x, osc φ τ x • b x ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + 1) := by
  refine hOB (Metric.closedBall (0 : Fin d → ℂ) r) _ τ hτ ?_ ?_ hph.low V b K hK hbc hbs ?_
  · exact hph.smooth.of_le (by exact_mod_cast (by omega : d + 2 + 1 ≤ d + 6))
  · have h := E_dphi_sym (N := d + 5) (by omega) hph.smooth hr (E_sqrt_pos hτ) (E_sqrt_le_one hτ1) hph.crit
      hph.bd
    exact h.mono (fun x _ => E_wt_pos (E_sqrt_pos hτ) x) (by omega) le_rfl
  · exact_mod_cast hb

end EEst

section EAmp

variable {d : ℕ} {β : ℂ} {ρ : ℝ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def constantAmplitude (d : ℕ) (ρ : ℝ) (a₀ : V) (x : Fin d → ℂ) : V := cutB d ρ x • a₀

noncomputable def linearAmplitude (d : ℕ) (ρ : ℝ) (ℓ : (Fin d → ℂ) →L[ℝ] V) (x : Fin d → ℂ) : V := cutB d ρ x • ℓ x

noncomputable def modelAmplitude (d : ℕ) (ρ : ℝ) (a₀ : V) (ℓ : (Fin d → ℂ) →L[ℝ] V) (x : Fin d → ℂ) : V :=
  cutB d ρ x • (a₀ + ℓ x)

theorem modelAmplitude_eq_add (a₀ : V) (ℓ : (Fin d → ℂ) →L[ℝ] V) :
    modelAmplitude d ρ a₀ ℓ = fun x => constantAmplitude d ρ a₀ x + linearAmplitude d ρ ℓ x := by
  funext x
  simp [modelAmplitude, constantAmplitude, linearAmplitude, smul_add]

theorem E_cut_sym (hρ : 0 < ρ) {N : ℕ} {Cχ : ℝ}
    (hC : ∀ i : ℕ, i ≤ N → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ) {r' σ : ℝ} (hr' : 0 < r') (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r') (wt σ) 0 N (Cχ * (r' + 1) ^ N) (cutB d ρ) := by
  have h := Sym.of_vanish (f := cutB d ρ) (M := Cχ) 0 hr' hσ hσ1 (Nat.zero_le _) (E_cut_contDiff hρ N)
    (fun x _ i hi => hC i hi x) (fun i hi => absurd hi (Nat.not_lt_zero _))
  exact_mod_cast h

theorem constant_amplitude_symbol (hρ : 0 < ρ) {N : ℕ} {Cχ : ℝ}
    (hC : ∀ i : ℕ, i ≤ N → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ) {r' σ : ℝ} (hr' : 0 < r') (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) {a₀ : V} {S : ℝ} (ha : ‖a₀‖ ≤ S) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r') (wt σ) 0 N (2 ^ N * (Cχ * (r' + 1) ^ N) * S) (constantAmplitude d ρ a₀) := by
  have hw : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r', 0 < wt σ x := fun x _ => E_wt_pos hσ x
  have h := Sym.smul hw (E_cut_sym hρ hC hr' hσ hσ1)
    (Sym.const (N := N) (m := 0) (K := S) a₀ ((norm_nonneg _).trans ha) hw (fun x _ => by simpa using ha))
  rwa [add_zero] at h

theorem linear_amplitude_symbol (hρ : 0 < ρ) {N : ℕ} {Cχ : ℝ}
    (hC : ∀ i : ℕ, i ≤ N → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ) {r' σ : ℝ} (hr' : 0 < r') (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) {ℓ : (Fin d → ℂ) →L[ℝ] V} {S : ℝ} (hl : ‖ℓ‖ ≤ S) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r') (wt σ) 1 N (2 ^ N * (Cχ * (r' + 1) ^ N) * S) (linearAmplitude d ρ ℓ) := by
  have hw : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r', 0 < wt σ x := fun x _ => E_wt_pos hσ x
  have h := Sym.smul hw (E_cut_sym hρ hC hr' hσ hσ1)
    ((Sym.clm (A := Metric.closedBall (0 : Fin d → ℂ) r') (N := N) ℓ hσ).mono hw le_rfl hl)
  rwa [zero_add] at h

theorem E_wt_le {r' σ : ℝ} (hσ1 : σ ≤ 1) :
    ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r', wt σ x ≤ r' + 1 := by
  intro x hx
  have : ‖x‖ ≤ r' := by simpa using hx
  unfold wt
  linarith

theorem model_amplitude_symbol (hρ : 0 < ρ) {N : ℕ} {Cχ : ℝ}
    (hC : ∀ i : ℕ, i ≤ N → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ) {r' σ : ℝ} (hr' : 0 < r') (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) {a₀ : V} {ℓ : (Fin d → ℂ) →L[ℝ] V} {S : ℝ} (ha : ‖a₀‖ ≤ S) (hl : ‖ℓ‖ ≤ S) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r') (wt σ) 0 N
      (2 ^ N * (Cχ * (r' + 1) ^ N) * (r' + 2) * S) (modelAmplitude d ρ a₀ ℓ) := by
  have hw : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r', 0 < wt σ x := fun x _ => E_wt_pos hσ x
  have h1 : Sym (Metric.closedBall (0 : Fin d → ℂ) r') (wt σ) (0 + ((1 : ℕ) : ℤ)) N
      (2 ^ N * (Cχ * (r' + 1) ^ N) * S) (linearAmplitude d ρ ℓ) := by
    have := linear_amplitude_symbol hρ hC hr' hσ hσ1 hl
    simpa using this
  have h2 := Sym.lower 1 hw (E_wt_le hσ1) h1
  rw [modelAmplitude_eq_add]
  exact ((constant_amplitude_symbol hρ hC hr' hσ hσ1 ha).add h2).mono hw le_rfl (le_of_eq (by ring))

theorem E_cut_smul_tsupport (hρ : 0 < ρ) (g : (Fin d → ℂ) → V) :
    tsupport (fun x => cutB d ρ x • g x) ⊆ Metric.closedBall (0 : Fin d → ℂ) ρ :=
  (tsupport_smul_subset_left _ _).trans (E_cut_tsupport hρ).le

theorem E_cut_smul_compact (hρ : 0 < ρ) (g : (Fin d → ℂ) → V) :
    HasCompactSupport (fun x => cutB d ρ x • g x) :=
  (E_cut_compact hρ).smul_right

theorem E_integral_neg (hβ : β ≠ 0) (f : (Fin d → ℂ) → V) :
    ∫ x, f (-x) ∂(muPi β (Fin d)) = ∫ x, f x ∂(muPi β (Fin d)) := by
  have := isAddHaar_muPi d β hβ
  have h := Measure.integral_comp_smul (muPi β (Fin d)) f (-1)
  simpa [abs_inv, abs_pow] using h

theorem E_integral_odd (hβ : β ≠ 0) (f : (Fin d → ℂ) → V) (hf : ∀ x, f (-x) = - f x) :
    ∫ x, f x ∂(muPi β (Fin d)) = 0 := by
  have h := E_integral_neg hβ f
  simp_rw [hf] at h
  rw [integral_neg] at h
  have h2 : (2 : ℝ) • ∫ x, f x ∂(muPi β (Fin d)) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    simp
  exact (smul_eq_zero.1 h2).resolve_left (by norm_num)

theorem E_osc_quad_neg (φ : (Fin d → ℂ) → ℝ) (τ : ℝ) (x : Fin d → ℂ) :
    osc (quad φ) τ (-x) = osc (quad φ) τ x := by
  simp [osc, E_quad_neg]

end EAmp

section ETerms

variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {a₀ : V} {ℓ : (Fin d → ℂ) →L[ℝ] V}

theorem E_P_sym' (hr : 0 < r) (hph : E_Phase d r Γ c₁ φ) (hρr : ρ ≤ r) (hτ : 0 < τ) (hτ1 : τ ≤ 1) {N : ℕ}
    (hN : N ≤ d + 6) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) ρ) (wt (Real.sqrt τ)) 3 N
      ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) (E_P φ) :=
  ((E_P_sym (by omega) hph.smooth hr (E_sqrt_pos hτ) (E_sqrt_le_one hτ1) hph.crit hph.bd).subset
    (Metric.closedBall_subset_closedBall hρr)).mono (fun x _ => E_wt_pos (E_sqrt_pos hτ) x) hN le_rfl

theorem E_Pe_sym' (hr : 0 < r) (hph : E_Phase d r Γ c₁ φ) (hρr : ρ ≤ r) (hτ : 0 < τ) (hτ1 : τ ≤ 1) {N : ℕ}
    (hN : N ≤ d + 6) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) ρ) (wt (Real.sqrt τ)) 4 N
      ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) (E_Pe φ) :=
  ((E_Pe_sym (by omega) hph.smooth hr (E_sqrt_pos hτ) (E_sqrt_le_one hτ1) hph.crit hph.bd).subset
    (Metric.closedBall_subset_closedBall hρr)).mono (fun x _ => E_wt_pos (E_sqrt_pos hτ) x) hN le_rfl

theorem model_integral_second_error {C : ℝ} (hOB : E_OB d 3 β (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) C)
    (hr : 0 < r) (hΓ : 0 < Γ) (hph : E_Phase d r Γ c₁ φ) (hρ0 : 0 < ρ) (hρr : ρ ≤ r)
    (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6) * ρ ≤ c₁ / 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hCχ : 0 ≤ Cχ) (hC : ∀ i : ℕ, i ≤ d + 6 → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ)
    (ha : ‖a₀‖ ≤ S) (hl : ‖ℓ‖ ≤ S) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖∫ x, osc (fun y => quad φ y + s * E_P φ y) τ x • ((E_P φ x * E_P φ x) • modelAmplitude d ρ a₀ ℓ x)
        ∂(muPi β (Fin d))‖ ≤
      C * (2 ^ (d + 1 + 3) * (2 ^ (d + 1 + 3) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) *
        ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6))) *
        (2 ^ (d + 1 + 3) * (Cχ * (ρ + 1) ^ (d + 1 + 3)) * (ρ + 2) * S)) * τ ^ (d + 3) := by
  have hS : 0 ≤ S := (norm_nonneg _).trans ha
  have hw : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) ρ, 0 < wt (Real.sqrt τ) x :=
    fun x _ => E_wt_pos (E_sqrt_pos hτ) x
  have hP := E_P_sym' (N := d + 1 + 3) hr hph hρr hτ hτ1 (by omega)
  have hA := model_amplitude_symbol (N := d + 1 + 3) (a₀ := a₀) (ℓ := ℓ) hρ0 (fun i hi => hC i (by omega)) hρ0 (E_sqrt_pos hτ)
    (E_sqrt_le_one hτ1) ha hl
  have h := Sym.smul hw (Sym.mul hw hP hP) hA
  have e : ((3 : ℤ) + 3 + 0) = 2 * ((3 : ℕ) : ℤ) := by norm_num
  rw [e] at h
  refine E_est (q := 3) (by norm_num) hOB hr hph hρr hρ hτ hτ1 hs _ _ (by positivity) ?_ ?_ h
  · exact (E_cut_smul_compact hρ0 _).smul_left
  · exact (tsupport_smul_subset_right _ _).trans (E_cut_smul_tsupport hρ0 _)

theorem E_integrable (hβ : β ≠ 0) {ψ : (Fin d → ℂ) → ℝ} (hψ : Continuous ψ) (τ : ℝ) {g : (Fin d → ℂ) → V}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => osc ψ τ x • g x) (muPi β (Fin d)) := by
  have := isAddHaar_muPi d β hβ
  exact ((continuous_oscillatory_factor hψ τ).smul hg).integrable_of_hasCompactSupport hgc.smul_left

theorem E_cut_continuous (hρ0 : 0 < ρ) : Continuous (cutB d ρ) := (E_cut_contDiff hρ0 0).continuous

theorem linear_amplitude_integral_zero (hβ : β ≠ 0) (hρ0 : 0 < ρ) :
    ∫ x, osc (quad φ) τ x • linearAmplitude d ρ ℓ x ∂(muPi β (Fin d)) = 0 := by
  refine E_integral_odd hβ _ fun x => ?_
  rw [E_osc_quad_neg]
  simp [linearAmplitude, E_cut_neg hρ0]

theorem model_integral_first_error {C : ℝ} (hβ : β ≠ 0) (hOB : E_OB d 2 β (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) C)
    (hr : 0 < r) (hΓ : 0 < Γ) (hph : E_Phase d r Γ c₁ φ) (hρ0 : 0 < ρ) (hρr : ρ ≤ r)
    (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6) * ρ ≤ c₁ / 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hCχ : 0 ≤ Cχ) (hC : ∀ i : ℕ, i ≤ d + 6 → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ)
    (ha : ‖a₀‖ ≤ S) (hl : ‖ℓ‖ ≤ S) :
    ‖∫ x, osc (quad φ) τ x • (E_P φ x • modelAmplitude d ρ a₀ ℓ x) ∂(muPi β (Fin d))‖ ≤
      2 * (C * (2 ^ (d + 1 + 2) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) *
        (2 ^ (d + 1 + 2) * (Cχ * (ρ + 1) ^ (d + 1 + 2)) * S)) * τ ^ (d + 2)) := by
  have hS : 0 ≤ S := (norm_nonneg _).trans ha
  have hw : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) ρ, 0 < wt (Real.sqrt τ) x :=
    fun x _ => E_wt_pos (E_sqrt_pos hτ) x
  have hs0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hφc : Continuous φ := hph.smooth.continuous
  have hqc : Continuous (quad φ) := (E_quad_contDiff φ 0).continuous
  have hPc : Continuous (E_P φ) := hφc.sub hqc
  have hPn : Continuous (fun x => E_P φ (-x)) := hPc.comp continuous_neg
  have hPec : Continuous (E_Pe φ) := continuous_const.mul (hPc.add hPn)
  have hχc := E_cut_continuous (d := d) hρ0
  have hb0c : Continuous (constantAmplitude d ρ a₀) := hχc.smul continuous_const
  have hb1c : Continuous (linearAmplitude d ρ ℓ) := hχc.smul ℓ.continuous
  have hb0s : HasCompactSupport (constantAmplitude d ρ a₀) := E_cut_smul_compact hρ0 _
  have hb1s : HasCompactSupport (linearAmplitude d ρ ℓ) := E_cut_smul_compact hρ0 _

  have hPe := E_Pe_sym' (N := d + 1 + 2) hr hph hρr hτ hτ1 (by omega)
  have hP := E_P_sym' (N := d + 1 + 2) hr hph hρr hτ hτ1 (by omega)
  have hB0 := constant_amplitude_symbol (N := d + 1 + 2) (a₀ := a₀) hρ0 (fun i hi => hC i (by omega)) hρ0 (E_sqrt_pos hτ)
    (E_sqrt_le_one hτ1) ha
  have hB1 := linear_amplitude_symbol (N := d + 1 + 2) (ℓ := ℓ) hρ0 (fun i hi => hC i (by omega)) hρ0 (E_sqrt_pos hτ)
    (E_sqrt_le_one hτ1) hl
  have h0 := Sym.smul hw hPe hB0
  have h1 := Sym.smul hw hP hB1
  have e0 : ((4 : ℤ) + 0) = 2 * ((2 : ℕ) : ℤ) := by norm_num
  have e1 : ((3 : ℤ) + 1) = 2 * ((2 : ℕ) : ℤ) := by norm_num
  rw [e0] at h0
  rw [e1] at h1
  have k0 := E_est (q := 2) (by norm_num) hOB hr hph hρr hρ hτ hτ1 hs0 _ _ (by positivity)
    (hb0s.smul_left (f := E_Pe φ)) ((tsupport_smul_subset_right _ _).trans (E_cut_smul_tsupport hρ0 _)) h0
  have k1 := E_est (q := 2) (by norm_num) hOB hr hph hρr hρ hτ hτ1 hs0 _ _ (by positivity)
    (hb1s.smul_left (f := E_P φ)) ((tsupport_smul_subset_right _ _).trans (E_cut_smul_tsupport hρ0 _)) h1
  rw [E_ph_zero] at k0 k1

  have hodd : ∫ x, osc (quad φ) τ x • (((1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))) • constantAmplitude d ρ a₀ x)
      ∂(muPi β (Fin d)) = 0 := by
    refine E_integral_odd hβ _ fun x => ?_
    rw [E_osc_quad_neg]
    simp only [constantAmplitude, E_cut_neg hρ0, neg_neg]
    rw [← smul_neg, ← neg_smul]
    congr 2
    ring
  have hsplit : ∀ x, osc (quad φ) τ x • (E_P φ x • modelAmplitude d ρ a₀ ℓ x) =
      (osc (quad φ) τ x • (E_Pe φ x • constantAmplitude d ρ a₀ x) +
        osc (quad φ) τ x • (((1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))) • constantAmplitude d ρ a₀ x)) +
        osc (quad φ) τ x • (E_P φ x • linearAmplitude d ρ ℓ x) := by
    intro x
    rw [modelAmplitude_eq_add, ← smul_add, ← add_smul, ← smul_add, smul_add (E_P φ x)]
    congr 3
    unfold E_Pe
    ring
  simp_rw [hsplit]
  have i0 : Integrable (fun x => osc (quad φ) τ x • (E_Pe φ x • constantAmplitude d ρ a₀ x)) (muPi β (Fin d)) :=
    E_integrable (τ := τ) hβ hqc (hPec.smul hb0c) (hb0s.smul_left (f := E_Pe φ))
  have i1 : Integrable (fun x => osc (quad φ) τ x • (((1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))) • constantAmplitude d ρ a₀ x))
      (muPi β (Fin d)) := E_integrable (τ := τ) hβ hqc
    ((continuous_const.mul (hPc.sub hPn) : Continuous fun x => (1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))).smul hb0c)
    (hb0s.smul_left (f := fun x => (1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))))
  have i2 : Integrable (fun x => osc (quad φ) τ x • (E_P φ x • linearAmplitude d ρ ℓ x)) (muPi β (Fin d)) :=
    E_integrable (τ := τ) hβ hqc (hPc.smul hb1c) (hb1s.smul_left (f := E_P φ))
  have i01 : Integrable (fun x => osc (quad φ) τ x • (E_Pe φ x • constantAmplitude d ρ a₀ x) +
      osc (quad φ) τ x • (((1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))) • constantAmplitude d ρ a₀ x)) (muPi β (Fin d)) := i0.add i1
  rw [integral_add i01 i2, integral_add i0 i1, hodd, add_zero]
  refine (norm_add_le _ _).trans ?_
  rw [two_mul]
  exact add_le_add k0 k1

end ETerms

section EFinal

variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

noncomputable def E_u (d : ℕ) (ρ : ℝ) (a : (Fin d → ℂ) → V) (x : Fin d → ℂ) : V :=
  a x - modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x

theorem E_a_zero_le {a : (Fin d → ℂ) → V} (hbd : ∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) :
    ‖a 0‖ ≤ S := by
  rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
  exact hbd 0 (Nat.zero_le _) 0

theorem E_a_fderiv_le {a : (Fin d → ℂ) → V} (hbd : ∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) :
    ‖fderiv ℝ a 0‖ ≤ S := by
  rw [← norm_iteratedFDeriv_one]
  exact hbd 1 (by omega) 0

theorem E_u_support (hρ0 : 0 < ρ) (hρr : ρ ≤ r) {a : (Fin d → ℂ) → V}
    (hsupp : Function.support a ⊆ Metric.closedBall 0 r) :
    Function.support (E_u d ρ a) ⊆ Metric.closedBall 0 r := by
  intro x hx
  by_contra hxr
  apply hx
  have h1 : a x = 0 := by
    by_contra h
    exact hxr (hsupp h)
  have h2 : cutB d ρ x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    rw [E_cut_tsupport hρ0]
    exact fun h => hxr (Metric.closedBall_subset_closedBall hρr h)
  simp [E_u, modelAmplitude, h1, h2]

theorem E_u_sym (hr : 0 < r) (hρ0 : 0 < ρ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hCχ : 0 ≤ Cχ)
    (hC : ∀ i : ℕ, i ≤ d + 6 → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ)
    {a : (Fin d → ℂ) → V} (ha : ContDiff ℝ (2 * d + 2 : ℕ) a)
    (hbd : ∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r) (wt (Real.sqrt τ)) 2 (d + 2)
      ((S + 2 ^ (d + 2) * (Cχ * (r + 1) ^ (d + 2)) * (r + 2) * S) * (r + 1) ^ (d + 2)) (E_u d ρ a) := by
  have ha0 := E_a_zero_le hbd
  have hl := E_a_fderiv_le hbd
  have hS : 0 ≤ S := (norm_nonneg _).trans ha0
  have hA1 := model_amplitude_symbol (N := d + 2) hρ0 (fun i hi => hC i (by omega)) hr one_pos le_rfl ha0 hl
  have had : ContDiff ℝ (d + 2 : ℕ) a := ha.of_le (by exact_mod_cast (by omega : d + 2 ≤ 2 * d + 2))
  have hu : E_u d ρ a = a - modelAmplitude d ρ (a 0) (fderiv ℝ a 0) := rfl
  have h := Sym.of_vanish (f := E_u d ρ a) (M := S + 2 ^ (d + 2) * (Cχ * (r + 1) ^ (d + 2)) * (r + 2) * S) 2 hr
    (E_sqrt_pos hτ) (E_sqrt_le_one hτ1) (by omega) (had.sub hA1.1) ?_ ?_
  · exact_mod_cast h
  · intro x hx i hi
    have hin : ((i : ℕ) : WithTop ℕ∞) ≤ (d + 2 : ℕ) := by exact_mod_cast hi
    rw [hu, iteratedFDeriv_sub_apply (had.of_le hin).contDiffAt (hA1.1.of_le hin).contDiffAt]
    refine (norm_sub_le _ _).trans (add_le_add (hbd i (by omega) x) ?_)
    refine (hA1.2 x hx i hi).trans ?_
    have hw1 : (1 : ℝ) ≤ wt 1 x := by unfold wt; linarith [norm_nonneg x]
    have hz : wt 1 x ^ ((0 : ℤ) - (i : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hw1 (by omega)
    have hK : 0 ≤ 2 ^ (d + 2) * (Cχ * (r + 1) ^ (d + 2)) * (r + 2) * S := by positivity
    calc _ ≤ 2 ^ (d + 2) * (Cχ * (r + 1) ^ (d + 2)) * (r + 2) * S * 1 := mul_le_mul_of_nonneg_left hz hK
      _ = _ := mul_one _
  · intro i hi
    have h0 : cutB d ρ (0 : Fin d → ℂ) = 1 := E_cut_one hρ0 (Metric.mem_closedBall_self (by positivity))
    rw [← norm_eq_zero]
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]
      simp [E_u, modelAmplitude, h0]
    · rw [norm_iteratedFDeriv_one]
      have hev : E_u d ρ a =ᶠ[𝓝 0] fun x => a x - (a 0 + fderiv ℝ a 0 x) := by
        filter_upwards [Metric.closedBall_mem_nhds (0 : Fin d → ℂ) (half_pos hρ0)] with x hx
        simp [E_u, modelAmplitude, E_cut_one hρ0 hx]
      rw [hev.fderiv_eq]
      have hda : HasFDerivAt a (fderiv ℝ a 0) 0 :=
        ((had.differentiable (by simp)) 0).hasFDerivAt
      have h3 : HasFDerivAt (fun x => a x - (a 0 + fderiv ℝ a 0 x)) (fderiv ℝ a 0 - fderiv ℝ a 0) 0 :=
        hda.sub ((fderiv ℝ a 0).hasFDerivAt.const_add (a 0))
      rw [h3.fderiv, sub_self, norm_zero]

end EFinal

section ECore

theorem real_core (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (r Γ c₁ : ℝ) (hr : 0 < r) (hΓ : 0 < Γ) (hc₁ : 0 < c₁) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∃ C : ℝ, ∀ (φ : (Fin d → ℂ) → ℝ) (τ : ℝ), 0 < τ → τ ≤ 1 →
      ContDiff ℝ (d + 6 : ℕ) φ →
      (∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∀ i : ℕ, i ≤ d + 6 → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) →
      fderiv ℝ φ 0 = 0 →
      (∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (a : (Fin d → ℂ) → V) (S : ℝ),
        ContDiff ℝ (2 * d + 2 : ℕ) a → Function.support a ⊆ Metric.closedBall 0 r →
        (∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        ‖∫ x, osc φ τ x • a x ∂(muPi β (Fin d)) -
            (∫ x, osc (quad φ) τ x * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d))) • a 0‖ ≤ C * S * τ ^ (d + 1) := by
  have hKP0 : 0 < ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) := by positivity
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (min r (c₁ / (2 * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6))))) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρdef]; exact lt_min hr (by positivity)
  have hρr : ρ ≤ r := by rw [hρdef]; exact min_le_left _ _
  have hρ : ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) * ρ ≤ c₁ / 2 := by
    calc ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) * ρ ≤ ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) * (c₁ / (2 * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)))) :=
          mul_le_mul_of_nonneg_left (by rw [hρdef]; exact min_le_right _ _) hKP0.le
      _ = c₁ / 2 := by field_simp
  obtain ⟨C1, hC1, hOB1⟩ := E_OB_exists d 1 β hβ (Γ * (r + 1) ^ (d + 5)) c₁ hc₁
  obtain ⟨C2, hC2, hOB2⟩ := E_OB_exists d 2 β hβ (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) (half_pos hc₁)
  obtain ⟨C3, hC3, hOB3⟩ := E_OB_exists d 3 β hβ (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) (half_pos hc₁)
  obtain ⟨Cχ, hCχ, hC⟩ := E_cut_bound (d := d) hρ0 (d + 6)
  refine ⟨ρ, hρ0, hρr,
    C1 * ((1 + 2 ^ (d + 2) * (Cχ * (r + 1) ^ (d + 2)) * (r + 2)) * (r + 1) ^ (d + 2)) +
      C3 * (2 ^ (d + 1 + 3) * (2 ^ (d + 1 + 3) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6))) *
        (2 ^ (d + 1 + 3) * (Cχ * (ρ + 1) ^ (d + 1 + 3)) * (ρ + 2))) +
      2 * (C2 * (2 ^ (d + 1 + 2) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) * (2 ^ (d + 1 + 2) * (Cχ * (ρ + 1) ^ (d + 1 + 2))))), ?_⟩
  intro φ τ hτ hτ1 hsm hbdφ hcrit hlow V _ _ _ a S ha hsupp hbd
  have hph : E_Phase d r Γ c₁ φ := ⟨hsm, hbdφ, hcrit, hlow⟩
  have ha0 := E_a_zero_le hbd
  have hl := E_a_fderiv_le hbd
  have hS : 0 ≤ S := (norm_nonneg _).trans ha0
  have hφc : Continuous φ := hsm.continuous
  have hqc : Continuous (quad φ) := (E_quad_contDiff φ 0).continuous
  have hPc : Continuous (E_P φ) := hφc.sub hqc
  have hχc := E_cut_continuous (d := d) hρ0
  have hac : Continuous a := ha.continuous
  have hcc : Continuous (modelAmplitude d ρ (a 0) (fderiv ℝ a 0)) :=
    hχc.smul (continuous_const.add (fderiv ℝ a 0).continuous)
  have hccs : HasCompactSupport (modelAmplitude d ρ (a 0) (fderiv ℝ a 0)) := E_cut_smul_compact hρ0 _
  have huc : Continuous (E_u d ρ a) := hac.sub hcc
  have husupp := E_u_support hρ0 hρr hsupp
  have hucs : HasCompactSupport (E_u d ρ a) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) husupp
  have huts : tsupport (E_u d ρ a) ⊆ Metric.closedBall 0 r := closure_minimal husupp Metric.isClosed_closedBall

  have hTu := E_est_u hOB1 hr hph hτ hτ1 (E_u d ρ a) _ (by positivity) hucs huts
    (E_u_sym hr hρ0 hτ hτ1 hCχ hC ha hbd)
  have hTay := E_taylor hβ (quad φ) (E_P φ) hqc hPc τ hτ (modelAmplitude d ρ (a 0) (fderiv ℝ a 0)) hcc hccs _
    (fun s hs => model_integral_second_error hOB3 hr hΓ hph hρ0 hρr hρ hτ hτ1 hCχ hC ha0 hl hs)
  rw [E_ph_one] at hTay
  have hT1 := model_integral_first_error hβ hOB2 hr hΓ hph hρ0 hρr hρ hτ hτ1 hCχ hC ha0 hl

  have hsplit : ∫ x, osc φ τ x • a x ∂(muPi β (Fin d)) =
      ∫ x, osc φ τ x • E_u d ρ a x ∂(muPi β (Fin d)) +
        ∫ x, osc φ τ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x ∂(muPi β (Fin d)) := by
    rw [← integral_add (E_integrable hβ hφc τ huc hucs) (E_integrable hβ hφc τ hcc hccs)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← smul_add, E_u, sub_add_cancel]
  have hmodel : ∫ x, osc (quad φ) τ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x ∂(muPi β (Fin d)) =
      (∫ x, osc (quad φ) τ x * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d))) • a 0 := by
    have i0 : Integrable (fun x => osc (quad φ) τ x • constantAmplitude d ρ (a 0) x) (muPi β (Fin d)) :=
      E_integrable hβ hqc τ (hχc.smul continuous_const) (E_cut_smul_compact hρ0 _)
    have i1 : Integrable (fun x => osc (quad φ) τ x • linearAmplitude d ρ (fderiv ℝ a 0) x) (muPi β (Fin d)) :=
      E_integrable hβ hqc τ (hχc.smul (fderiv ℝ a 0).continuous) (E_cut_smul_compact hρ0 _)
    simp_rw [modelAmplitude_eq_add, smul_add]
    rw [integral_add i0 i1, linear_amplitude_integral_zero hβ hρ0, add_zero, ← integral_smul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [constantAmplitude]
    rw [mul_smul, Complex.coe_smul]
  have key : ∫ x, osc φ τ x • a x ∂(muPi β (Fin d)) -
      (∫ x, osc (quad φ) τ x * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d))) • a 0 =
      ∫ x, osc φ τ x • E_u d ρ a x ∂(muPi β (Fin d)) +
      (∫ x, osc φ τ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x ∂(muPi β (Fin d)) -
        ∫ x, osc (quad φ) τ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x ∂(muPi β (Fin d)) -
        (Complex.I / (τ : ℂ)) • ∫ x, osc (quad φ) τ x • (E_P φ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x)
          ∂(muPi β (Fin d))) +
      (Complex.I / (τ : ℂ)) • ∫ x, osc (quad φ) τ x • (E_P φ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x)
          ∂(muPi β (Fin d)) := by
    rw [hsplit, ← hmodel]
    abel
  rw [key]
  refine (norm_add₃_le).trans ?_
  have hI : ‖(Complex.I / (τ : ℂ))‖ = 1 / τ := by
    rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  rw [norm_smul, hI]
  have hT1' := mul_le_mul_of_nonneg_left hT1 (by positivity : 0 ≤ 1 / τ)
  refine (add_le_add (add_le_add hTu hTay) hT1').trans (le_of_eq ?_)
  have e3 : τ ^ (d + 3) = τ ^ (d + 1) * τ ^ 2 := by ring
  have e2 : τ ^ (d + 2) = τ ^ (d + 1) * τ := by ring
  rw [e3, e2]
  field_simp

end ECore

end Formalism.FourierDecayAlt.P.StationaryPhaseModel

end PartE

section PartF

open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix

namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel

theorem F_fderiv_single {d : ℕ} {g : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ} {k : Fin d} {D : ℂ}
    (hg : DifferentiableAt ℂ g x) (h : HasDerivAt (fun ξ => g (Function.update x k ξ)) D (x k)) :
    fderiv ℂ g x (Pi.single k 1) = D := by
  have h1 : HasDerivAt (fun ξ => Function.update x k ξ) (Pi.single k (1:ℂ)) (x k) := hasDerivAt_update x k (x k)
  have h2 : HasFDerivAt g (fderiv ℂ g x) (Function.update x k (x k)) := by
    rw [Function.update_eq_self]; exact hg.hasFDerivAt
  exact (h2.comp_hasDerivAt (x k) h1).unique h

theorem F_clm_sum {d : ℕ} (L : (Fin d → ℂ) →L[ℂ] ℂ) (v : Fin d → ℂ) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [map_sum]

theorem F_contDiff_mul_cut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} (hU : IsOpen U)
    {χ f : E → ℝ} {n : WithTop ℕ∞} (hχ : ContDiff ℝ n χ) (hs : tsupport χ ⊆ U) (hf : ContDiffOn ℝ n f U) :
    ContDiff ℝ n (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hs h)
    have h0 : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx'
    refine (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with y hy
    simp [hy]

noncomputable def realPartMulCLM (c : ℂ) : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ c)

theorem F_T_apply (c z : ℂ) : realPartMulCLM c z = (c * z).re := rfl

theorem F_T_norm (c : ℂ) : ‖realPartMulCLM c‖ ≤ ‖c‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  rw [F_T_apply, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (norm_mul_le _ _)

theorem F_norm_single {d : ℕ} (i : Fin d) (z : ℂ) : ‖(Pi.single i z : Fin d → ℂ)‖ = ‖z‖ := by
  exact Pi.norm_single (G := fun _ : Fin d => ℂ) z

section Holo

variable {d : ℕ} {r : ℝ} {g : (Fin d → ℂ) → ℂ}

theorem F_diff_fderiv (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) :
    DifferentiableOn ℂ (fderiv ℂ g) (Metric.ball 0 (2 * r)) := by
  have h2 : ContDiffOn ℂ ((1 : WithTop ℕ∞) + 1) g (Metric.ball 0 (2 * r)) := by
    have := holo_contDiffOn Metric.isOpen_ball hg 2
    simpa [one_add_one_eq_two] using this
  exact ((contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball).1 h2).2.2.differentiableOn (by simp)

theorem F_hasFDerivAt_apply (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (v : Fin d → ℂ) :
    HasFDerivAt (fun y => fderiv ℂ g y v)
      ((ContinuousLinearMap.apply ℂ ℂ v).comp (fderiv ℂ (fderiv ℂ g) 0)) 0 := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.mem_ball_self (by positivity)
  have hB : HasFDerivAt (fderiv ℂ g) (fderiv ℂ (fderiv ℂ g) 0) 0 :=
    ((F_diff_fderiv hg).differentiableAt (Metric.isOpen_ball.mem_nhds h0)).hasFDerivAt
  exact (ContinuousLinearMap.apply ℂ ℂ v).hasFDerivAt.comp 0 hB

theorem F_symm (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (u v : Fin d → ℂ) :
    fderiv ℂ (fderiv ℂ g) 0 u v = fderiv ℂ (fderiv ℂ g) 0 v u := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.mem_ball_self (by positivity)
  have h2 : ContDiffAt ℂ (2 : ℕ) g 0 :=
    (holo_contDiffOn Metric.isOpen_ball hg 2).contDiffAt (Metric.isOpen_ball.mem_nhds h0)
  exact h2.isSymmSndFDerivAt (by simp) u v

variable {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}

theorem F_dg_eq (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    {x : Fin d → ℂ} (hx : x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r)) (k : Fin d) :
    fderiv ℂ g x (Pi.single k 1) = dg x k :=
  F_fderiv_single (hg.differentiableAt (Metric.isOpen_ball.mem_nhds hx)) (hdg x hx k)

theorem F_H_eq (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) (i j : Fin d) :
    fderiv ℂ (fderiv ℂ g) 0 (Pi.single j 1) (Pi.single i 1) = H i j := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.mem_ball_self (by positivity)
  have h1 : HasDerivAt (fun ξ : ℂ => Function.update (0 : Fin d → ℂ) j ξ) (Pi.single j (1:ℂ)) 0 :=
    hasDerivAt_update (0 : Fin d → ℂ) j 0
  have hu0 : Function.update (0 : Fin d → ℂ) j 0 = 0 := by
    simp
  have h2 : HasFDerivAt (fun y => fderiv ℂ g y (Pi.single i 1))
      ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).comp (fderiv ℂ (fderiv ℂ g) 0))
      (Function.update (0 : Fin d → ℂ) j 0) := by
    rw [hu0]; exact F_hasFDerivAt_apply hr hg _
  have h3 := h2.comp_hasDerivAt (0:ℂ) h1
  have hev : (fun ξ => dg (Function.update 0 j ξ) i) =ᶠ[𝓝 (0:ℂ)]
      ((fun y => fderiv ℂ g y (Pi.single i 1)) ∘ fun ξ : ℂ => Function.update (0 : Fin d → ℂ) j ξ) := by
    have hc : ContinuousAt (fun ξ : ℂ => Function.update (0 : Fin d → ℂ) j ξ) 0 := h1.continuousAt
    have : ∀ᶠ ξ in 𝓝 (0:ℂ), Function.update (0 : Fin d → ℂ) j ξ ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) :=
      hc.eventually_mem (by rw [hu0]; exact Metric.isOpen_ball.mem_nhds h0)
    filter_upwards [this] with ξ hξ
    exact (F_dg_eq hg hdg hξ i).symm
  exact (h3.congr_of_eventuallyEq hev).unique (hH i j)

theorem F_B_eq (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) (u v : Fin d → ℂ) :
    fderiv ℂ (fderiv ℂ g) 0 u v = v ⬝ᵥ (H *ᵥ u) := by
  rw [F_clm_sum (fderiv ℂ (fderiv ℂ g) 0 u) v]
  simp only [dotProduct, mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [F_symm hr hg, F_clm_sum (fderiv ℂ (fderiv ℂ g) 0 (Pi.single i 1)) u]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [F_symm hr hg, F_H_eq hr hg hdg hH, mul_comm]

theorem F_H_symm (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) : H.IsSymm := by
  ext i j
  rw [Matrix.transpose_apply, ← F_H_eq hr hg hdg hH, ← F_H_eq hr hg hdg hH, F_symm hr hg]

end Holo

section Holo2

variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ} {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}

theorem F_norm_fderiv_le {f : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (Metric.ball x (2 * δ))) (hM : ∀ y ∈ Metric.ball x (2 * δ), ‖f y‖ ≤ M)
    (v : Fin d → ℂ) : ‖fderiv ℂ f x v‖ ≤ M / δ * ‖v‖ := by
  have h1 := holo_bound 1 (f := f) (x := x) (δ := δ) (M := M) hδ (by simpa [one_add_one_eq_two] using hf)
    (by simpa [one_add_one_eq_two] using hM)
  rw [norm_iteratedFDeriv_one, pow_one] at h1
  have hx : x ∈ Metric.ball x (2 * δ) := Metric.mem_ball_self (by positivity)
  have h2 : fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ :=
    (hf.differentiableAt (Metric.isOpen_ball.mem_nhds hx)).fderiv_restrictScalars ℝ
  have h3 : fderiv ℂ f x v = fderiv ℝ f x v := by rw [h2]; rfl
  rw [h3]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)

theorem F_H_bound (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hb : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ‖g x‖ ≤ Λ)
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) (i j : Fin d) :
    ‖H i j‖ ≤ Λ / (r / 2) / (r / 2) := by
  have hsub : Metric.ball (0 : Fin d → ℂ) (2 * (r / 2)) ⊆ Metric.ball (0 : Fin d → ℂ) (2 * r) :=
    Metric.ball_subset_ball (by linarith)
  have hp : DifferentiableOn ℂ (fun y => fderiv ℂ g y (Pi.single i 1)) (Metric.ball 0 (2 * (r / 2))) := by
    intro y hy
    exact (((F_diff_fderiv hg) y (hsub hy)).clm_apply (differentiableWithinAt_const _)).mono hsub
  have hpb : ∀ y ∈ Metric.ball (0 : Fin d → ℂ) (2 * (r / 2)), ‖fderiv ℂ g y (Pi.single i 1)‖ ≤ Λ / (r / 2) := by
    intro y hy
    have hs : Metric.ball y (2 * (r / 2)) ⊆ Metric.ball (0 : Fin d → ℂ) (2 * r) := by
      intro z hz
      rw [Metric.mem_ball, dist_zero_right] at hy ⊢
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by simpa using norm_add_le (z - y) y
      linarith
    have := F_norm_fderiv_le (half_pos hr) (hg.mono hs) (fun z hz => hb z (hs hz)) (Pi.single i 1)
    simpa [F_norm_single] using this
  have h1 := F_norm_fderiv_le (half_pos hr) hp hpb (Pi.single j 1)
  have h2 : fderiv ℂ (fun y => fderiv ℂ g y (Pi.single i 1)) 0 (Pi.single j 1) = H i j := by
    rw [(F_hasFDerivAt_apply hr hg (Pi.single i 1)).fderiv]
    exact F_H_eq hr hg hdg hH i j
  rw [h2] at h1
  simpa [F_norm_single] using h1

theorem F_H_lower (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hdg0 : ∀ k, dg 0 k = 0)
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0)
    (hgrad : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ‖x‖ ≤ Λ * ‖dg x‖) (x : Fin d → ℂ) :
    ‖x‖ ≤ Λ * ‖H *ᵥ x‖ := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.mem_ball_self (by positivity)
  have hline : HasDerivAt (fun ε : ℝ => ε • x) x 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const x
  have hcl : ContinuousAt (fun ε : ℝ => ε • x) 0 := hline.continuousAt
  have hf : HasDerivAt (fun ε : ℝ => dg (ε • x)) (H *ᵥ x) 0 := by
    rw [hasDerivAt_pi]
    intro i
    have h2 : HasFDerivAt (fun y => fderiv ℂ g y (Pi.single i 1))
        (((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).comp (fderiv ℂ (fderiv ℂ g) 0)).restrictScalars ℝ)
        ((0:ℝ) • x) := by
      rw [zero_smul]; exact (F_hasFDerivAt_apply hr hg _).restrictScalars ℝ
    have h3 := h2.comp_hasDerivAt (0:ℝ) hline
    have hval : (((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).comp
        (fderiv ℂ (fderiv ℂ g) 0)).restrictScalars ℝ) x = (H *ᵥ x) i := by
      show fderiv ℂ (fderiv ℂ g) 0 x (Pi.single i 1) = _
      rw [F_B_eq hr hg hdg hH]
      simp [dotProduct, Pi.single_apply]
    rw [hval] at h3
    refine h3.congr_of_eventuallyEq ?_
    have : ∀ᶠ ε in 𝓝 (0:ℝ), ε • x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) :=
      hcl.eventually_mem (by rw [zero_smul]; exact Metric.isOpen_ball.mem_nhds h0)
    filter_upwards [this] with ε hε
    exact (F_dg_eq hg hdg hε i).symm
  have ht := hf.tendsto_slope_zero_right
  have hd0 : dg ((0:ℝ) • x) = 0 := by rw [zero_smul]; funext k; exact hdg0 k
  have ht2 : Tendsto (fun ε : ℝ => Λ * ‖ε⁻¹ • (dg ((0 + ε) • x) - dg ((0:ℝ) • x))‖) (𝓝[>] 0)
      (𝓝 (Λ * ‖H *ᵥ x‖)) := (ht.norm).const_mul Λ
  refine ge_of_tendsto ht2 ?_
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε • x ∈ Metric.closedBall (0 : Fin d → ℂ) r :=
    (hcl.eventually_mem (by rw [zero_smul]; exact Metric.closedBall_mem_nhds _ hr)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hpos
  have hpos' : (0:ℝ) < ε := hpos
  have h1 := hgrad _ hε
  rw [hd0, sub_zero, zero_add, norm_smul, norm_inv, Real.norm_of_nonneg hpos'.le]
  rw [norm_smul, Real.norm_of_nonneg hpos'.le] at h1
  calc ‖x‖ = ε⁻¹ * (ε * ‖x‖) := by field_simp
    _ ≤ ε⁻¹ * (Λ * ‖dg (ε • x)‖) := by gcongr
    _ = Λ * (ε⁻¹ * ‖dg (ε • x)‖) := by ring

end Holo2

section Phase

noncomputable def F_bump (d : ℕ) (r : ℝ) (x : Fin d → ℂ) : ℝ :=
  if h : 0 < r then (⟨5 * r / 4, 3 * r / 2, by positivity, by linarith⟩ : ContDiffBump (0 : Fin d → ℂ)) x else 0

noncomputable def F_phi (d : ℕ) (r : ℝ) (c : ℂ) (g : (Fin d → ℂ) → ℂ) (x : Fin d → ℂ) : ℝ :=
  F_bump d r x * (c * g x).re

variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ}

theorem F_bump_eq (hr : 0 < r) : F_bump d r =
    ((⟨5 * r / 4, 3 * r / 2, by positivity, by linarith⟩ : ContDiffBump (0 : Fin d → ℂ)) : (Fin d → ℂ) → ℝ) := by
  funext x; simp [F_bump, hr]

theorem F_bump_contDiff (hr : 0 < r) (n : ℕ) : ContDiff ℝ n (F_bump d r) := by
  rw [F_bump_eq hr]
  exact_mod_cast ContDiffBump.contDiff (n := (n : ℕ∞)) _

theorem F_bump_tsupport (hr : 0 < r) : tsupport (F_bump d r) ⊆ Metric.ball 0 (2 * r) := by
  rw [F_bump_eq hr, ContDiffBump.tsupport_eq]
  exact Metric.closedBall_subset_ball (by linarith)

theorem F_bump_one (hr : 0 < r) {x : Fin d → ℂ} (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) (5 * r / 4)) :
    F_bump d r x = 1 := by
  rw [F_bump_eq hr]
  exact ContDiffBump.one_of_mem_closedBall _ hx

theorem F_g_contDiffOn (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (n : ℕ) :
    ContDiffOn ℝ n g (Metric.ball 0 (2 * r)) :=
  (holo_contDiffOn Metric.isOpen_ball hg n).restrict_scalars ℝ

theorem F_phi_contDiff (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (c : ℂ) (n : ℕ) :
    ContDiff ℝ n (F_phi d r c g) := by
  refine F_contDiff_mul_cut Metric.isOpen_ball (F_bump_contDiff hr n) (F_bump_tsupport hr) ?_
  exact (realPartMulCLM c).contDiff.comp_contDiffOn (F_g_contDiffOn hg n)

theorem F_phi_ev (hr : 0 < r) (c : ℂ) {x : Fin d → ℂ} (hx : x ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4)) :
    F_phi d r c g =ᶠ[𝓝 x] (realPartMulCLM c ∘ g) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  simp [F_phi, F_bump_one hr (Metric.ball_subset_closedBall hy), F_T_apply]

theorem F_ball_sub {x : Fin d → ℂ} {s : ℝ} (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) (hs : s ≤ r) :
    Metric.ball x s ⊆ Metric.ball (0 : Fin d → ℂ) (2 * r) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  rw [Metric.mem_ball, dist_zero_right]
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by simpa using norm_add_le (z - x) x
  linarith

theorem F_mem_ball (hr : 0 < r) {x : Fin d → ℂ} (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) :
    x ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4) := by
  rw [Metric.mem_closedBall] at hx
  rw [Metric.mem_ball]
  linarith

theorem F_phi_bound (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hb : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ‖g x‖ ≤ Λ) (c : ℂ) {x : Fin d → ℂ}
    (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) (i : ℕ) {δ : ℝ} (hδ : 0 < δ) (hi : ((i + 1 : ℕ) : ℝ) * δ ≤ r) :
    ‖iteratedFDeriv ℝ i (F_phi d r c g) x‖ ≤ ‖c‖ * (Λ / δ ^ i) := by
  rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) (F_phi_ev (g := g) hr c (F_mem_ball hr hx)) i).eq_of_nhds]
  have hs := F_ball_sub hx hi
  have hx2 : x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := hs (Metric.mem_ball_self (by positivity))
  have h1 := (realPartMulCLM c).norm_iteratedFDeriv_comp_left (n := i)
    ((F_g_contDiffOn hg i).contDiffAt (Metric.isOpen_ball.mem_nhds hx2)) le_rfl
  have h2 := holo_bound i hδ (hg.mono hs) (fun y hy => hb y (hs hy))
  calc _ ≤ ‖realPartMulCLM c‖ * ‖iteratedFDeriv ℝ i g x‖ := h1
    _ ≤ ‖c‖ * (Λ / δ ^ i) := by gcongr; exact F_T_norm c

theorem F_hasFDerivAt_Tg (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (c : ℂ) {x : Fin d → ℂ}
    (hx : x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r)) :
    HasFDerivAt (realPartMulCLM c ∘ g) ((realPartMulCLM c).comp ((fderiv ℂ g x).restrictScalars ℝ)) x :=
  (realPartMulCLM c).hasFDerivAt.comp x
    ((hg.differentiableAt (Metric.isOpen_ball.mem_nhds hx)).hasFDerivAt.restrictScalars ℝ)

theorem F_phi_fderiv (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (c : ℂ) {x : Fin d → ℂ}
    (hx : x ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4)) (v : Fin d → ℂ) :
    fderiv ℝ (F_phi d r c g) x v = (c * fderiv ℂ g x v).re := by
  have hx2 : x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.ball_subset_ball (by linarith) hx
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (F_phi_ev (g := g) hr c hx), (F_hasFDerivAt_Tg hg c hx2).fderiv]
  rfl

theorem F_phi_snd (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (c : ℂ) (u v : Fin d → ℂ) :
    fderiv ℝ (fderiv ℝ (F_phi d r c g)) 0 u v = (c * fderiv ℂ (fderiv ℂ g) 0 u v).re := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4) := Metric.mem_ball_self (by positivity)
  have hφ2 : ContDiff ℝ (2 : ℕ) (F_phi d r c g) := F_phi_contDiff hr hg c 2
  have hd : DifferentiableAt ℝ (fderiv ℝ (F_phi d r c g)) 0 :=
    ((hφ2.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun y => fderiv ℝ (F_phi d r c g) y v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ (F_phi d r c g)) 0)) 0 :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp 0 hd.hasFDerivAt
  have h2 : HasFDerivAt (fun y => realPartMulCLM c (fderiv ℂ g y v))
      ((realPartMulCLM c).comp (((ContinuousLinearMap.apply ℂ ℂ v).comp (fderiv ℂ (fderiv ℂ g) 0)).restrictScalars ℝ)) 0 :=
    (realPartMulCLM c).hasFDerivAt.comp 0 ((F_hasFDerivAt_apply hr hg v).restrictScalars ℝ)
  have hev : (fun y => fderiv ℝ (F_phi d r c g) y v) =ᶠ[𝓝 0] fun y => realPartMulCLM c (fderiv ℂ g y v) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with y hy
    rw [F_phi_fderiv hr hg c hy, F_T_apply]
  have h3 := (h2.congr_of_eventuallyEq hev).unique h1
  have h4 := congrArg (fun L => L u) h3
  exact h4.symm

end Phase

section Final

variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ} {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}

theorem F_norm_psi (β w : ℂ) : ‖psi β w‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

noncomputable def F_c (β t : ℂ) : ℂ := β * (‖t‖ : ℂ) / t

theorem F_c_norm (β : ℂ) {t : ℂ} (ht : t ≠ 0) : ‖F_c β t‖ = ‖β‖ := by
  have : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
  simp only [F_c, norm_div, norm_mul, Complex.norm_real, norm_norm]
  field_simp

theorem F_re_div (β : ℂ) {t : ℂ} (ht : t ≠ 0) (w : ℂ) : (β * (w / t)).re = (F_c β t * w).re / ‖t‖ := by
  have h1 : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ht
  rw [← Complex.div_ofReal_re]
  congr 1
  unfold F_c
  field_simp

theorem F_psi_eq (β : ℂ) {t : ℂ} (ht : t ≠ 0) (w : ℂ) :
    psi β (w / t) = Complex.exp (Complex.I * (((F_c β t * w).re / ‖t‖ : ℝ) : ℂ)) := by
  unfold psi
  rw [F_re_div β ht]

theorem F_osc_phi (hr : 0 < r) (β : ℂ) {t : ℂ} (ht : t ≠ 0) {x : Fin d → ℂ}
    (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) :
    osc (F_phi d r (F_c β t) g) ‖t‖ x = psi β (g x / t) := by
  rw [F_psi_eq β ht]
  unfold osc F_phi
  rw [F_bump_one hr (Metric.closedBall_subset_closedBall (by linarith) hx), one_mul]

theorem F_osc_quad (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0)
    (β : ℂ) {t : ℂ} (ht : t ≠ 0) (x : Fin d → ℂ) :
    osc (quad (F_phi d r (F_c β t) g)) ‖t‖ x = psi β (g 0 / t) * psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.closedBall (0 : Fin d → ℂ) (5 * r / 4) :=
    Metric.mem_closedBall_self (by positivity)
  have e1 : (x ⬝ᵥ (H *ᵥ x)) / (2 * t) = ((x ⬝ᵥ (H *ᵥ x)) / 2) / t := by
    rw [div_div]
  rw [e1, F_psi_eq β ht, F_psi_eq β ht, ← Complex.exp_add]
  unfold osc quad
  rw [F_phi_snd hr hg, F_B_eq hr hg hdg hH]
  congr 1
  rw [← mul_add, ← Complex.ofReal_add]
  congr 2
  have e2 : F_phi d r (F_c β t) g 0 = (F_c β t * g 0).re := by
    unfold F_phi; rw [F_bump_one hr h0, one_mul]
  have e3 : (F_c β t * ((x ⬝ᵥ (H *ᵥ x)) / 2)).re = (1 / 2) * (F_c β t * (x ⬝ᵥ (H *ᵥ x))).re := by
    have : F_c β t * ((x ⬝ᵥ (H *ᵥ x)) / 2) = ((1 / 2 : ℝ) : ℂ) * (F_c β t * (x ⬝ᵥ (H *ᵥ x))) := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  rw [e2, e3]
  ring

theorem F_lower (hd : 0 < d) (hr : 0 < r) (hΛ : 0 < Λ) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hgrad : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ‖x‖ ≤ Λ * ‖dg x‖) {c : ℂ} (hc : c ≠ 0)
    {x : Fin d → ℂ} (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) :
    ∃ l : Fin d × Bool, ‖c‖ / (2 * Λ) * ‖x‖ ≤ |fderiv ℝ (F_phi d r c g) x (dirv l)| := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hx1 := F_mem_ball hr hx
  have hx2 : x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.ball_subset_ball (by linarith) hx1
  by_cases hx0 : ‖x‖ = 0
  · exact ⟨(⟨0, hd⟩, false), by rw [hx0, mul_zero]; exact abs_nonneg _⟩
  have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)
  by_contra hcon
  push Not at hcon
  have hk : ∀ k, ‖dg x k‖ < ‖x‖ / Λ := by
    intro k
    have h1 := hcon (k, false)
    have h2 := hcon (k, true)
    rw [F_phi_fderiv hr hg c hx1] at h1 h2
    have e1 : fderiv ℂ g x (dirv (k, false)) = dg x k := by
      simp only [dirv]; exact F_dg_eq hg hdg hx2 k
    have e2 : fderiv ℂ g x (dirv (k, true)) = Complex.I * dg x k := by
      have : (dirv (k, true) : Fin d → ℂ) = Complex.I • Pi.single k 1 := by
        simp only [dirv]
        rw [← Pi.single_smul]; simp
      rw [this, map_smul, F_dg_eq hg hdg hx2 k, smul_eq_mul]
    rw [e1] at h1
    rw [e2] at h2
    have e3 : (c * (Complex.I * dg x k)).re = -(c * dg x k).im := by
      have : c * (Complex.I * dg x k) = Complex.I * (c * dg x k) := by ring
      rw [this, Complex.I_mul_re]
    rw [e3, abs_neg] at h2
    have h3 : ‖c * dg x k‖ ≤ |(c * dg x k).re| + |(c * dg x k).im| := Complex.norm_le_abs_re_add_abs_im _
    rw [norm_mul] at h3
    have h4 : ‖c‖ * ‖dg x k‖ < ‖c‖ * (‖x‖ / Λ) := by
      calc ‖c‖ * ‖dg x k‖ ≤ _ := h3
        _ < ‖c‖ / (2 * Λ) * ‖x‖ + ‖c‖ / (2 * Λ) * ‖x‖ := add_lt_add h1 h2
        _ = ‖c‖ * (‖x‖ / Λ) := by field_simp; ring
    exact lt_of_mul_lt_mul_left h4 hcpos.le
  have h5 : ‖dg x‖ < ‖x‖ / Λ := (pi_norm_lt_iff (by positivity)).2 hk
  have h6 := hgrad x hx
  have h7 : Λ * ‖dg x‖ < ‖x‖ := by
    calc Λ * ‖dg x‖ < Λ * (‖x‖ / Λ) := by gcongr
      _ = ‖x‖ := by field_simp
  linarith

end Final

theorem F_zero_small (d : ℕ) (hd : 0 < d) (β : ℂ) (hβ : β ≠ 0) (r Λ : ℝ) (hr : 0 < r) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (g : (Fin d → ℂ) → ℂ) (dg : (Fin d → ℂ) → Fin d → ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
      DifferentiableOn ℂ g (Metric.ball 0 (2 * r)) → (∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ‖g x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
        HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k)) →
      (∀ k, dg 0 k = 0) →
      (∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) →
      (∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ‖x‖ ≤ Λ * ‖dg x‖) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (a : (Fin d → ℂ) → V) (S : ℝ),
        ContDiff ℝ (2 * d + 2 : ℕ) a → Function.support a ⊆ Metric.closedBall 0 r →
        (∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ 1 →
          ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) -
              (psi β (g 0 / t) * ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • a 0‖ ≤ C * S * ‖t‖ ^ (d + 1) := by
  have hβpos : 0 < ‖β‖ := norm_pos_iff.2 hβ
  set δ : ℝ := r / ((d : ℝ) + 7) with hδdef
  have hδ : 0 < δ := by positivity
  set Γ : ℝ := ‖β‖ * (Λ * (max 1 δ⁻¹) ^ (d + 6)) with hΓdef
  have hΓ : 0 < Γ := by positivity
  set c₁ : ℝ := ‖β‖ / (2 * Λ) with hc₁def
  have hc₁ : 0 < c₁ := by positivity
  obtain ⟨ρ, hρ, _, CE, hE⟩ := real_core d β hβ r Γ c₁ hr hΓ hc₁
  have hΓH : 0 < Λ / (r / 2) / (r / 2) := by positivity
  obtain ⟨CD, hD⟩ := model d β hβ ρ (Λ / (r / 2) / (r / 2)) Λ hρ hΓH hΛ
  refine ⟨|CE| + |CD|, by positivity, ?_⟩
  intro g dg H hg hb hdg hdg0 hH hgrad V _ _ _ a S ha hsupp hS t ht ht1
  have hτ : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hc0 : F_c β t ≠ 0 := by rw [← norm_pos_iff, F_c_norm β ht]; exact hβpos
  have h00 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4) := Metric.mem_ball_self (by positivity)
  have h02 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.mem_ball_self (by positivity)
  have ha0 : ‖a 0‖ ≤ S := by simpa using hS 0 (Nat.zero_le _) 0
  have hS0 : 0 ≤ S := (norm_nonneg _).trans ha0

  have hφbd : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∀ i : ℕ, i ≤ d + 6 →
      ‖iteratedFDeriv ℝ i (F_phi d r (F_c β t) g) x‖ ≤ Γ := by
    intro x hx i hi
    have hi' : ((i + 1 : ℕ) : ℝ) * δ ≤ r := by
      have h1 : ((i + 1 : ℕ) : ℝ) ≤ (d : ℝ) + 7 := by
        have : i + 1 ≤ d + 7 := by omega
        exact_mod_cast this
      rw [hδdef]
      calc ((i + 1 : ℕ) : ℝ) * (r / ((d : ℝ) + 7)) ≤ ((d : ℝ) + 7) * (r / ((d : ℝ) + 7)) := by gcongr
        _ = r := by field_simp
    have h1 := F_phi_bound hr hg hb (F_c β t) hx i hδ hi'
    rw [F_c_norm β ht] at h1
    refine h1.trans ?_
    rw [hΓdef]
    have h2 : Λ / δ ^ i ≤ Λ * (max 1 δ⁻¹) ^ (d + 6) := by
      rw [div_eq_mul_inv, ← inv_pow]
      have h3 : δ⁻¹ ^ i ≤ (max 1 δ⁻¹) ^ i := pow_le_pow_left₀ (by positivity) (le_max_right _ _) i
      have h4 : (max 1 δ⁻¹) ^ i ≤ (max 1 δ⁻¹) ^ (d + 6) := pow_le_pow_right₀ (le_max_left _ _) hi
      gcongr
      exact h3.trans h4
    gcongr
  have hφ0 : fderiv ℝ (F_phi d r (F_c β t) g) 0 = 0 := by
    ext v
    rw [F_phi_fderiv hr hg _ h00, F_clm_sum]
    simp [F_dg_eq hg hdg h02, hdg0]
  have hlow : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∃ l : Fin d × Bool,
      c₁ * ‖x‖ ≤ |fderiv ℝ (F_phi d r (F_c β t) g) x (dirv l)| := by
    intro x hx
    have := F_lower hd hr hΛ hg hdg hgrad hc0 hx
    rwa [F_c_norm β ht] at this
  have hmain := hE (F_phi d r (F_c β t) g) ‖t‖ hτ ht1 (F_phi_contDiff hr hg _ (d + 6)) hφbd hφ0 hlow V a S ha hsupp hS
  have hmod := hD H (F_H_symm hr hg hdg hH) (F_H_bound hr hg hb hdg hH) (F_H_lower hr hg hdg hdg0 hH hgrad) t ht ht1

  have hint1 : ∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) =
      ∫ x, osc (F_phi d r (F_c β t) g) ‖t‖ x • a x ∂(muPi β (Fin d)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r
    · simp only [F_osc_phi hr β ht hx]
    · have : a x = 0 := by
        by_contra h
        exact hx (hsupp h)
      simp only [this, smul_zero]
  have hint2 : ∫ x, osc (quad (F_phi d r (F_c β t) g)) ‖t‖ x * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d)) =
      psi β (g 0 / t) *
        ∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [F_osc_quad hr hg hdg hH β ht x, mul_assoc]
  rw [hint1]
  rw [hint2] at hmain
  set I1 := ∫ x, osc (F_phi d r (F_c β t) g) ‖t‖ x • a x ∂(muPi β (Fin d))
  set J := ∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d))
  have hsplit : I1 - (psi β (g 0 / t) * ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • a 0 =
      (I1 - (psi β (g 0 / t) * J) • a 0) +
        (psi β (g 0 / t) * (J - ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ))) • a 0 := by
    rw [mul_sub, sub_smul]; abel
  rw [hsplit]
  have hpw : 0 ≤ ‖t‖ ^ (d + 1) := by positivity
  have hsecond : ‖(psi β (g 0 / t) * (J - ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ))) • a 0‖ ≤ |CD| * S * ‖t‖ ^ (d + 1) := by
    rw [norm_smul, norm_mul, F_norm_psi, one_mul]
    calc ‖J - ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)‖ * ‖a 0‖ ≤ (|CD| * ‖t‖ ^ (d + 1)) * S := by
          refine mul_le_mul (hmod.trans ?_) ha0 (norm_nonneg _) (by positivity)
          gcongr
          exact le_abs_self _
      _ = |CD| * S * ‖t‖ ^ (d + 1) := by ring
  have hfirst : ‖I1 - (psi β (g 0 / t) * J) • a 0‖ ≤ |CE| * S * ‖t‖ ^ (d + 1) := by
    refine hmain.trans ?_
    gcongr
    exact le_abs_self _
  calc _ ≤ ‖I1 - (psi β (g 0 / t) * J) • a 0‖ +
        ‖(psi β (g 0 / t) * (J - ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ))) • a 0‖ := norm_add_le _ _
    _ ≤ |CE| * S * ‖t‖ ^ (d + 1) + |CD| * S * ‖t‖ ^ (d + 1) := add_le_add hfirst hsecond
    _ = (|CE| + |CD|) * S * ‖t‖ ^ (d + 1) := by ring

end Formalism.FourierDecayAlt.P.StationaryPhaseModel

open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix

namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel

theorem norm_psi_alt (β w : ℂ) : ‖psi β w‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem cutoff_eq_contDiffBump (d : ℕ) (ρ : ℝ) (h : 0 < ρ) :
    cutB d ρ = fun x => (⟨ρ / 2, ρ, half_pos h, half_lt_self h⟩ : ContDiffBump (0 : Fin d → ℂ)) x := by
  funext x
  simp [cutB, h]

theorem bump_cutoff_spec (d : ℕ) (ρ : ℝ) (h : 0 < ρ) (n : ℕ) :
    ContDiff ℝ n (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) ∧
    HasCompactSupport (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) ∧
    Function.support (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) ⊆ Metric.closedBall 0 ρ ∧
    ((cutB d ρ (0 : Fin d → ℂ) : ℝ) : ℂ) = 1 := by
  rw [cutoff_eq_contDiffBump d ρ h]
  set f : ContDiffBump (0 : Fin d → ℂ) := ⟨ρ / 2, ρ, half_pos h, half_lt_self h⟩ with hf
  have hc : ContDiff ℝ n (fun x : Fin d → ℂ => ((f x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (f.contDiff (n := (n : ℕ∞)))
  have hsupp : Function.support (fun x : Fin d → ℂ => ((f x : ℝ) : ℂ)) = Metric.ball 0 ρ := by
    rw [← f.support_eq]
    ext x
    simp [Function.mem_support]
  refine ⟨hc, ?_, ?_, ?_⟩
  · have : HasCompactSupport (fun x : Fin d → ℂ => f x) := f.hasCompactSupport
    exact this.comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)
  · rw [hsupp]; exact Metric.ball_subset_closedBall
  · have : f 0 = 1 := f.one_of_mem_closedBall (by simpa [hf] using (half_pos h).le)
    simp [this]

theorem bump_cutoff_deriv_bound (d : ℕ) (ρ : ℝ) (h : 0 < ρ) (n : ℕ) : ∃ S : ℝ, ∀ j ≤ n, ∀ x : Fin d → ℂ,
    ‖iteratedFDeriv ℝ j (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) x‖ ≤ S := by
  obtain ⟨hc, hcs, -, -⟩ := bump_cutoff_spec d ρ h n
  have key : ∀ j ≤ n, ∃ S : ℝ, ∀ x : Fin d → ℂ,
      ‖iteratedFDeriv ℝ j (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) x‖ ≤ S := by
    intro j hj
    exact (hcs.iteratedFDeriv j).exists_bound_of_continuous
      (hc.continuous_iteratedFDeriv (by exact_mod_cast hj))
  choose! S hS using key
  refine ⟨∑ j ∈ Finset.range (n + 1), |S j|, fun j hj x => ?_⟩
  refine ((hS j hj x).trans (le_abs_self _)).trans ?_
  exact Finset.single_le_sum (f := fun j => |S j|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 (by omega))

theorem oscillatory_integral_trivial_bound (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (r : ℝ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (u : (Fin d → ℂ) → ℂ) (hu : ∀ x, ‖u x‖ = 1) (a : (Fin d → ℂ) → V) (S : ℝ)
    (hsupp : Function.support a ⊆ Metric.closedBall 0 r) (hS : ∀ x, ‖a x‖ ≤ S) :
    ‖∫ x : Fin d → ℂ, u x • a x ∂(muPi β (Fin d))‖ ≤
      S * (muPi β (Fin d) (Metric.closedBall 0 r)).toReal := by
  have := isAddHaar_muPi d β hβ
  have h1 : ∫ x : Fin d → ℂ, u x • a x ∂(muPi β (Fin d)) =
      ∫ x in Metric.closedBall (0 : Fin d → ℂ) r, u x • a x ∂(muPi β (Fin d)) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : a x = 0 := by
      by_contra hne
      exact hx (hsupp hne)
    rw [this, smul_zero]
  rw [h1]
  refine norm_setIntegral_le_of_norm_le_const (isCompact_closedBall _ _).measure_lt_top ?_
  intro x _
  rw [norm_smul, hu, one_mul]
  exact hS x

theorem F_zero (d : ℕ) (hd : 0 < d) (β : ℂ) (hβ : β ≠ 0) (r Λ : ℝ) (hr : 0 < r) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (g : (Fin d → ℂ) → ℂ) (dg : (Fin d → ℂ) → Fin d → ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
      DifferentiableOn ℂ g (Metric.ball 0 (2 * r)) → (∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ‖g x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
        HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k)) →
      (∀ k, dg 0 k = 0) →
      (∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) →
      (∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ‖x‖ ≤ Λ * ‖dg x‖) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (a : (Fin d → ℂ) → V) (S : ℝ),
        ContDiff ℝ (2 * d + 2 : ℕ) a → Function.support a ⊆ Metric.closedBall 0 r →
        (∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        ∀ t : ℂ, t ≠ 0 →
          ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) -
              (psi β (g 0 / t) * ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • a 0‖ ≤ C * S * ‖t‖ ^ (d + 1) := by
  obtain ⟨C₀, hC₀, h₀⟩ := F_zero_small d hd β hβ r Λ hr hΛ
  obtain ⟨Sχ, hSχ⟩ := bump_cutoff_deriv_bound d r hr (2 * d + 2)
  obtain ⟨hχc, -, hχs, hχ0⟩ := bump_cutoff_spec d r hr (2 * d + 2)
  set M : ℝ := (muPi β (Fin d) (Metric.closedBall 0 r)).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hSχ0 : 0 ≤ Sχ := (norm_nonneg _).trans (hSχ 0 (Nat.zero_le _) 0)
  set D₁ : ℝ := Sχ * M + C₀ * Sχ with hD₁
  have hD₁0 : 0 ≤ D₁ := by positivity
  refine ⟨max C₀ (M + D₁), le_max_of_le_left hC₀, ?_⟩
  intro g dg H hg hb hdg hdg0 hH hgrad V _ _ _ a S ha hsupp hS t ht
  have haS : ∀ x, ‖a x‖ ≤ S := fun x => by
    have := hS 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (haS 0)
  have hτ : 0 < ‖t‖ := norm_pos_iff.2 ht
  rcases le_total ‖t‖ 1 with h1 | h1
  · refine (h₀ g dg H hg hb hdg hdg0 hH hgrad V a S ha hsupp hS t ht h1).trans ?_
    gcongr
    exact le_max_left _ _
  ·
    have hdet : 1 / ‖H.det‖ ≤ D₁ := by
      have h2 := h₀ g dg H hg hb hdg hdg0 hH hgrad ℂ (fun x : Fin d → ℂ => ((cutB d r x : ℝ) : ℂ)) Sχ hχc hχs hSχ 1
        one_ne_zero (by simp)
      have h3 := oscillatory_integral_trivial_bound d β hβ r (fun x => psi β (g x / 1)) (fun x => norm_psi_alt β _)
        (fun x : Fin d → ℂ => ((cutB d r x : ℝ) : ℂ)) Sχ hχs (fun x => by
          have := hSχ 0 (Nat.zero_le _) x
          rwa [norm_iteratedFDeriv_zero] at this)
      have h4 : ‖(psi β (g 0 / 1) * ((‖(1 : ℂ)‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • ((cutB d r (0 : Fin d → ℂ) : ℝ) : ℂ)‖ =
          1 / ‖H.det‖ := by
        rw [hχ0, norm_smul, norm_mul, norm_psi_alt, norm_one, one_pow, Complex.norm_real, mul_one, one_mul,
          Real.norm_of_nonneg (by positivity)]
      rw [← h4]
      have h5 := norm_sub_norm_le
        ((psi β (g 0 / 1) * ((‖(1 : ℂ)‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • ((cutB d r (0 : Fin d → ℂ) : ℝ) : ℂ))
        (∫ x : Fin d → ℂ, psi β (g x / 1) • ((cutB d r x : ℝ) : ℂ) ∂(muPi β (Fin d)))
      rw [norm_sub_rev] at h5
      simp only [norm_one, one_pow, mul_one] at h2 h5 ⊢
      linarith
    have h6 := oscillatory_integral_trivial_bound d β hβ r (fun x => psi β (g x / t)) (fun x => norm_psi_alt β _) a S hsupp haS
    have h7 : ‖(psi β (g 0 / t) * ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • a 0‖ ≤ ‖t‖ ^ d * D₁ * S := by
      rw [norm_smul, norm_mul, norm_psi_alt, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have : ‖t‖ ^ d / ‖H.det‖ = ‖t‖ ^ d * (1 / ‖H.det‖) := by ring
      rw [this]
      gcongr
      exact haS 0
    have h8 : ‖t‖ ^ d ≤ ‖t‖ ^ (d + 1) := pow_le_pow_right₀ h1 (Nat.le_succ d)
    have h9 : (1 : ℝ) ≤ ‖t‖ ^ (d + 1) := one_le_pow₀ h1
    calc _ ≤ S * M + ‖t‖ ^ d * D₁ * S := (norm_sub_le _ _).trans (add_le_add h6 h7)
      _ ≤ S * M * ‖t‖ ^ (d + 1) + ‖t‖ ^ (d + 1) * D₁ * S := by
          refine add_le_add (le_mul_of_one_le_right (by positivity) h9) ?_
          gcongr
      _ = (M + D₁) * S * ‖t‖ ^ (d + 1) := by ring
      _ ≤ max C₀ (M + D₁) * S * ‖t‖ ^ (d + 1) := by
          gcongr
          exact le_max_right _ _

theorem stationary_phase_dim_zero (β : ℂ) (x₀ : Fin 0 → ℂ) (g : (Fin 0 → ℂ) → ℂ) (H : Matrix (Fin 0) (Fin 0) ℂ)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (a : (Fin 0 → ℂ) → V) (t : ℂ) :
    ∫ x : Fin 0 → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin 0)) -
      (psi β (g x₀ / t) * ((‖t‖ ^ 0 / ‖H.det‖ : ℝ) : ℂ)) • a x₀ = 0 := by
  have h1 : muPi β (Fin 0) = Measure.dirac x₀ := by
    unfold muPi
    exact Measure.pi_of_empty _ x₀
  rw [h1, integral_dirac, Matrix.det_isEmpty]
  simp

theorem add_update_eq_update_add {d : ℕ} (x₀ x : Fin d → ℂ) (k : Fin d) (ξ : ℂ) :
    x₀ + Function.update x k ξ = Function.update (x₀ + x) k (x₀ k + ξ) := by
  ext i
  by_cases h : i = k
  · subst h; simp
  · simp [h]

end Formalism.FourierDecayAlt.P.StationaryPhaseModel

theorem Formalism.FourierDecayAlt.P.stationary_phase_holomorphic : Formalism.FourierDecayAlt.G.StationaryPhase := by
  intro d β hβ r Λ hr hΛ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, ?_⟩
    intro x₀ g dg H _ _ _ _ _ _ V _ _ _ a S _ _ _ t _
    rw [Formalism.FourierDecayAlt.P.StationaryPhaseModel.stationary_phase_dim_zero β x₀ g H a t]
    simp
  obtain ⟨C, -, hC⟩ := Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_zero d hd β hβ r Λ hr hΛ
  refine ⟨C, ?_⟩
  intro x₀ g dg H hg hb hdg hdg0 hH hgrad V _ _ _ a S ha hsupp hS t ht
  have := Formalism.FourierDecayAlt.P.StationaryPhaseModel.isAddHaar_muPi d β hβ
  have hball : ∀ (ρ : ℝ) (x : Fin d → ℂ), x ∈ Metric.ball (0 : Fin d → ℂ) ρ → x₀ + x ∈ Metric.ball x₀ ρ := by
    intro ρ x hx
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hcball : ∀ (ρ : ℝ) (x : Fin d → ℂ), x ∈ Metric.closedBall (0 : Fin d → ℂ) ρ →
      x₀ + x ∈ Metric.closedBall x₀ ρ := by
    intro ρ x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have key := hC (fun x => g (x₀ + x)) (fun x => dg (x₀ + x)) H
    (by
      refine hg.comp (f := fun x => x₀ + x) ?_ (fun x hx => hball _ x hx)
      exact (differentiable_id.const_add x₀).differentiableOn)
    (fun x hx => hb _ (hball _ x hx))
    (by
      intro x hx k
      have h1 := hdg (x₀ + x) (hball _ x hx) k
      have h2 : HasDerivAt (fun η => g (Function.update (x₀ + x) k η)) (dg (x₀ + x) k) (x₀ k + x k) := h1
      have h3 := h2.comp_const_add (x₀ k) (x k)
      simpa only [Formalism.FourierDecayAlt.P.StationaryPhaseModel.add_update_eq_update_add] using h3)
    (by intro k; simpa using hdg0 k)
    (by
      intro i j
      have h1 := hH i j
      have h2 : HasDerivAt (fun η => dg (Function.update x₀ j η) i) (H i j) (x₀ j + 0) := by simpa using h1
      have h3 := h2.comp_const_add (x₀ j) 0
      have h4 : ∀ ξ : ℂ, x₀ + Function.update (0 : Fin d → ℂ) j ξ = Function.update x₀ j (x₀ j + ξ) := by
        intro ξ
        rw [Formalism.FourierDecayAlt.P.StationaryPhaseModel.add_update_eq_update_add, add_zero]
      simpa only [h4] using h3)
    (by
      intro x hx
      have h1 := hgrad (x₀ + x) (hcball _ x hx)
      simpa using h1)
    V (fun x => a (x₀ + x)) S
    (ha.comp (contDiff_const.add contDiff_id))
    (by
      intro x hx
      have h1 : x₀ + x ∈ Metric.closedBall x₀ r := hsupp hx
      simpa [Metric.mem_closedBall, dist_eq_norm] using h1)
    (by
      intro j hj x
      rw [iteratedFDeriv_comp_add_left]
      exact hS j hj _)
    t ht
  have hint : ∫ x : Fin d → ℂ, Formalism.FourierDecayAlt.G.psi β (g x / t) • a x ∂(Formalism.FourierDecayAlt.G.muPi β (Fin d)) =
      ∫ x : Fin d → ℂ, Formalism.FourierDecayAlt.G.psi β (g (x₀ + x) / t) • a (x₀ + x) ∂(Formalism.FourierDecayAlt.G.muPi β (Fin d)) :=
    (MeasureTheory.integral_add_left_eq_self (μ := Formalism.FourierDecayAlt.G.muPi β (Fin d))
      (fun x => Formalism.FourierDecayAlt.G.psi β (g x / t) • a x) x₀).symm
  rw [hint]
  simpa using key

end PartF
