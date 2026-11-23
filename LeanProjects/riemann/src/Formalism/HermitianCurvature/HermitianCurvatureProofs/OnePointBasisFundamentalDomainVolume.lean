import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftDegreeLemmas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtMinusW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairingTriangular

namespace Formalism.FourierDecayAlt.P.TBBx5

open Formalism.FourierDecayAlt Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal ComplexOrder

noncomputable section

open Classical

theorem cs_abs {V : Type} [AddCommGroup V] [Module ℂ V] (Dv : V → Prop) (β : V → V → ℂ)
    (hadd : ∀ x y, Dv x → Dv y → Dv (x + y)) (hsmul : ∀ (c : ℂ) x, Dv x → Dv (c • x))
    (hl : ∀ x₁ x₂ y (c : ℂ), Dv x₁ → Dv x₂ → Dv y → β (x₁ + c • x₂) y = β x₁ y + c * β x₂ y)
    (hr : ∀ x y₁ y₂ (c : ℂ), Dv x → Dv y₁ → Dv y₂ → β x (y₁ + c • y₂) = β x y₁ + conj c * β x y₂)
    (hpos : ∀ x, Dv x → 0 ≤ β x x) (x y : V) (hx : Dv x) (hy : Dv y) (hherm : β y x = conj (β x y)) :
    ‖β x y‖ ^ 2 ≤ (β x x).re * (β y y).re := by
  set b := β x y with hb
  set a := (β x x).re
  set c := (β y y).re
  have hc : 0 ≤ c := (Complex.nonneg_iff.1 (hpos y hy)).1
  have ha : 0 ≤ a := (Complex.nonneg_iff.1 (hpos x hx)).1
  have hB : ‖b‖ ^ 2 = Complex.normSq b := by rw [Complex.sq_norm]
  have key : ∀ t : ℝ, 0 ≤ a - 2 * t * Complex.normSq b + t ^ 2 * Complex.normSq b * c := by
    intro t
    set μ : ℂ := -(t : ℂ) * b with hμ
    have e1 : β x (x + μ • y) = β x x + conj μ * b := by rw [hr _ _ _ _ hx hx hy]
    have e2 : β y (x + μ • y) = conj b + conj μ * β y y := by rw [hr _ _ _ _ hy hx hy, hherm]
    have hz2 := hpos (x + μ • y) (hadd _ _ hx (hsmul _ _ hy))
    rw [hl _ _ _ _ hx hy (hadd _ _ hx (hsmul _ _ hy)), e1, e2] at hz2
    have hre := (Complex.nonneg_iff.1 hz2).1
    have : (β x x + conj μ * b + μ * (conj b + conj μ * β y y)).re =
        a - 2 * t * Complex.normSq b + t ^ 2 * Complex.normSq b * c := by
      simp only [hμ, Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, map_mul, map_neg,
        Complex.conj_ofReal, Complex.mul_im, Complex.add_im]
      ring
    linarith [this ▸ hre]
  rw [hB]
  rcases hc.eq_or_lt with hc0 | hc0
  · have hb0 : Complex.normSq b = 0 := by
      by_contra hne
      have hpos' : 0 < Complex.normSq b := lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hne)
      have := key ((a + 1) / (2 * Complex.normSq b))
      rw [← hc0] at this
      field_simp at this
      nlinarith
    rw [hb0, ← hc0]; simp
  · have := key (1 / c)
    field_simp at this
    nlinarith [Complex.normSq_nonneg b]

def FormNonneg {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) : Prop :=
  ∀ (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε →
      (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → 0 ≤ p.form j hj w x x

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem formNonneg_of (hA : P5.ThmPActual) (hFP : PBL.FormPos) (p : KB.Pl P Wp Wq) : FormNonneg p :=
  fun j hj w hw x ε hε hx => hFP hA Wp Wq P p j hj w hw x ε hε hx

theorem form_cs (p : KB.Pl P Wp Wq) (hpos : FormNonneg p) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (hw : KB.CutWord P p.l0 w) {ε : ℝ} (hε : 0 < ε)
    (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.NV (p.T.bs j) ε x) (hy : PBL.NV (p.T.bs j) ε y) :
    ‖p.form j hj w x y‖ ^ 2 ≤ (p.form j hj w x x).re * (p.form j hj w y y).re := by
  let VT := Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)
  have hadd : ∀ x y : VT, PBL.NV (p.T.bs j) ε x → PBL.NV (p.T.bs j) ε y → PBL.NV (p.T.bs j) ε (x + y) :=
    fun _ _ => PBL.nv_add
  have hsmul : ∀ (c : ℂ) (x : VT), PBL.NV (p.T.bs j) ε x → PBL.NV (p.T.bs j) ε (c • x) := fun c _ => PBL.nv_smul c
  have hl : ∀ (x₁ x₂ y : VT) (c : ℂ), PBL.NV (p.T.bs j) ε x₁ → PBL.NV (p.T.bs j) ε x₂ → PBL.NV (p.T.bs j) ε y →
      p.form j hj w (x₁ + c • x₂) y = p.form j hj w x₁ y + c * p.form j hj w x₂ y :=
    fun x₁ x₂ y c h₁ h₂ h₃ => PBL.form_sl p j hj w x₁ x₂ y c h₁ h₂ h₃
  have hr : ∀ (x y₁ y₂ : VT) (c : ℂ), PBL.NV (p.T.bs j) ε x → PBL.NV (p.T.bs j) ε y₁ → PBL.NV (p.T.bs j) ε y₂ →
      p.form j hj w x (y₁ + c • y₂) = p.form j hj w x y₁ + conj c * p.form j hj w x y₂ :=
    fun x y₁ y₂ c h₁ h₂ h₃ => PBL.form_sr p j hj w x y₁ y₂ c h₁ h₂ h₃
  have hp : ∀ x : VT, PBL.NV (p.T.bs j) ε x → 0 ≤ p.form j hj w x x := fun x hx => hpos j hj w hw x ε hε hx
  refine cs_abs (PBL.NV (p.T.bs j) ε) (p.form j hj w) hadd hsmul hl hr hp x y hx hy ?_
  exact PBL.herm_of_nonneg (PBL.NV (p.T.bs j) ε) (p.form j hj w) PBL.nv_zero hadd hsmul hl hr hp x y hx hy

theorem form_re_nonneg (p : KB.Pl P Wp Wq) (hpos : FormNonneg p) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (hw : KB.CutWord P p.l0 w) {ε : ℝ} (hε : 0 < ε)
    (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hx : PBL.NV (p.T.bs j) ε x) :
    0 ≤ (p.form j hj w x x).re :=
  (Complex.nonneg_iff.1 (hpos j hj w hw x ε hε hx)).1

end place

theorem plusW_eq (ys : List ℝ) (w : List C.Letter) :
    KB.plusW ys w = ys.map (fun y => ((true, y) : C.Letter)) ++ w := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [KB.plusW, ih]

theorem minusW_eq (ys : List ℝ) (w : List C.Letter) :
    KB.minusW ys w = ys.map (fun y => ((false, y + 1) : C.Letter)) ++ w := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [KB.minusW, ih]

theorem normC_plusW (nn : ℝ → ℝ) (ys : List ℝ) (w : List C.Letter) :
    TBB.normC nn (KB.plusW ys w) = (ys.map nn).prod * TBB.normC nn w := by
  rw [plusW_eq]
  simp [TBB.normC, List.map_append, List.prod_append, Function.comp_def]

theorem normC_minusW (nn : ℝ → ℝ) (ys : List ℝ) (w : List C.Letter) :
    TBB.normC nn (KB.minusW ys w) = (ys.map fun y => nn (y + 1)).prod * TBB.normC nn w := by
  rw [minusW_eq]
  simp [TBB.normC, List.map_append, List.prod_append, Function.comp_def]

theorem normC_pos (nn : ℝ → ℝ) (hnn : ∀ y, 0 < nn y) (w : List C.Letter) : 0 < TBB.normC nn w := by
  unfold TBB.normC
  exact List.prod_pos fun x hx => by
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
    exact hnn l.2

theorem prod_map_pos (f : ℝ → ℝ) (hf : ∀ y, 0 < f y) (ys : List ℝ) : 0 < (ys.map f).prod := by
  exact List.prod_pos fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
    exact hf y

theorem isExt_self (P : M.Par) (l0 : ℕ) (Y : Finset ℝ) (N m : ℕ) (w : List C.Letter) (hw : TBB.AdmW P l0 Y w)
    (hN : w.length ≤ N) : TBB.IsExt P l0 Y N m w w := ⟨hw.1, hN, [], by simp, by simp, by simp⟩

theorem isExt_plusW (P : M.Par) (l0 : ℕ) (Y : Finset ℝ) (N K : ℕ) (w : List C.Letter) (ys : List ℝ)
    (hN : w.length + K ≤ N) (hK : ys.length = K) (hY : ∀ y ∈ ys, y ∈ Y) (hc : KB.CutWord P l0 (KB.plusW ys w)) :
    TBB.IsExt P l0 Y N K w (KB.plusW ys w) := by
  refine ⟨hc, ?_, ys.map (fun y => ((true, y) : C.Letter)), plusW_eq ys w, by simp [hK], ?_⟩
  · rw [plusW_eq, List.length_append, List.length_map]
    omega
  · intro l hl
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
    exact ⟨y, hY y hy, Or.inl rfl⟩

theorem isExt_minusW (P : M.Par) (l0 : ℕ) (Y : Finset ℝ) (N K : ℕ) (w : List C.Letter) (ys : List ℝ)
    (hN : w.length + K ≤ N) (hK : ys.length = K) (hY : ∀ y ∈ ys, y ∈ Y) (hc : KB.CutWord P l0 (KB.minusW ys w)) :
    TBB.IsExt P l0 Y N K w (KB.minusW ys w) := by
  refine ⟨hc, ?_, ys.map (fun y => ((false, y + 1) : C.Letter)), minusW_eq ys w, by simp [hK], ?_⟩
  · rw [minusW_eq, List.length_append, List.length_map]
    omega
  · intro l hl
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
    exact ⟨y, hY y hy, Or.inr rfl⟩

section grid

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def ysOf {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (n : Fin K → Fin (d + 1)) : List ℝ :=
  List.ofFn fun a => grid a (n a)

def GridOK (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ : ℝ) (K : ℕ) (w : List C.Letter) (d : ℕ)
    (grid : Fin K → Fin (d + 1) → ℝ) : Prop :=
  (∀ a, Function.Injective (grid a)) ∧ (∀ a i, grid a i ∈ Y) ∧
  (∀ n : Fin K → Fin (d + 1), KB.CutWord P p.l0 (KB.plusW (ysOf grid n) w) ∧
    KB.CutWord P p.l0 (KB.minusW (ysOf grid n) w) ∧ (ysOf grid n).Pairwise (fun y y' => 2 < |y - y'|)) ∧
  ∑ n : Fin K → Fin (d + 1), |∏ a, F7.lagCo (grid a) (n a)| *
    Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
      ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) ≤ Λ ^ K

theorem ysOf_length {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (n : Fin K → Fin (d + 1)) :
    (ysOf grid n).length = K := by
  simp [ysOf]

theorem ysOf_mem {K d : ℕ} {Y : Finset ℝ} (grid : Fin K → Fin (d + 1) → ℝ) (hY : ∀ a i, grid a i ∈ Y)
    (n : Fin K → Fin (d + 1)) : ∀ y ∈ ysOf grid n, y ∈ Y := by
  intro y hy
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hy
  exact hY a (n a)

end grid

theorem scal_cs (α α₁ α₂ Pp q Q₁ Q₂ f₁ f₂ : ℝ) (hα : 0 ≤ α) (hαα : α ^ 2 = α₁ * α₂) (h₁ : 0 ≤ α₁) (h₂ : 0 ≤ α₂)
    (hq : 0 < q) (hQ₁ : 0 < Q₁) (hQ₂ : 0 < Q₂) (hP : 0 ≤ Pp) (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂)
    (hcs : Pp ^ 2 * q ≤ f₁ * f₂) :
    α * Pp ≤ Real.sqrt (Q₁ * Q₂ / q) * Real.sqrt ((α₁ * f₁ / Q₁) * (α₂ * f₂ / Q₂)) := by
  have hQ₁' := hQ₁.ne'
  have hQ₂' := hQ₂.ne'
  have hq' := hq.ne'
  rw [← Real.sqrt_mul (div_nonneg (mul_pos hQ₁ hQ₂).le hq.le)]
  have heq : Q₁ * Q₂ / q * ((α₁ * f₁ / Q₁) * (α₂ * f₂ / Q₂)) = α ^ 2 * (f₁ * f₂) / q := by
    rw [hαα]
    field_simp
  rw [heq]
  refine (Real.le_sqrt (mul_nonneg hα hP) (div_nonneg (mul_nonneg (sq_nonneg α) (mul_nonneg hf₁ hf₂)) hq.le)).2 ?_
  rw [le_div_iff₀ hq]
  calc (α * Pp) ^ 2 * q = α ^ 2 * (Pp ^ 2 * q) := by ring
    _ ≤ α ^ 2 * (f₁ * f₂) := mul_le_mul_of_nonneg_left hcs (sq_nonneg α)

theorem sqrt_mul_le_max (a b : ℝ) (ha : 0 ≤ a) (_hb : 0 ≤ b) : Real.sqrt (a * b) ≤ max a b := by
  have hm : 0 ≤ max a b := le_max_of_le_left ha
  calc Real.sqrt (a * b) ≤ Real.sqrt (max a b * max a b) :=
        Real.sqrt_le_sqrt (mul_le_mul (le_max_left a b) (le_max_right a b) _hb hm)
    _ = max a b := Real.sqrt_mul_self hm

theorem sqrt_mul_le_avg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have h0 : 0 ≤ (a + b) / 2 := by linarith
  rw [show (a + b) / 2 = Real.sqrt (((a + b) / 2) ^ 2) from (Real.sqrt_sq h0).symm]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a - b)])

theorem mn_pick (Λ x L E₁ E₂ : ℝ) (K : ℕ) (hx : 0 ≤ x) (h₁ : L ≤ E₁)
    (h₂ : 0 < x → x ^ K * L ≤ Λ ^ K * E₂) :
    L ≤ TBB.mn Λ K x * E₁ ∨ L ≤ TBB.mn Λ K x * E₂ := by
  unfold TBB.mn
  by_cases hx0 : x = 0
  · left
    rw [if_pos hx0, one_mul]
    exact h₁
  · rw [if_neg hx0]
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    by_cases hm : 1 ≤ (Λ / x) ^ K
    · left
      rw [min_eq_left hm, one_mul]
      exact h₁
    · right
      push_neg at hm
      rw [min_eq_right hm.le]
      have h2 := h₂ hxpos
      have hxK : 0 < x ^ K := pow_pos hxpos K
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hxK]
      linarith [h2]

theorem sum_le_max {ι : Type} [Fintype ι] [Nonempty ι] (c g : ι → ℝ) (L : ℝ) (hc : ∀ n, 0 ≤ c n)
    (hg : ∀ n, 0 ≤ g n) (hL : ∑ n, c n ≤ L) : ∃ n₀, ∑ n, c n * g n ≤ L * g n₀ := by
  obtain ⟨n₀, -, hn₀⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
  refine ⟨n₀, ?_⟩
  calc ∑ n, c n * g n ≤ ∑ n, c n * g n₀ :=
        Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hn₀ n (Finset.mem_univ n)) (hc n)
    _ = (∑ n, c n) * g n₀ := by rw [Finset.sum_mul]
    _ ≤ L * g n₀ := mul_le_mul_of_nonneg_right hL (hg n₀)

end

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P.TBBx5

open Formalism.FourierDecayAlt Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

def lp_e : (Fin 1 → ℂ) ≃ₗ[ℝ] ℂ := LinearEquiv.funUnique (Fin 1) ℝ ℂ

theorem lp_e_apply (m : Fin 1 → ℂ) : lp_e m = m 0 := rfl

def onePointRealBasis : Module.Basis (Fin 2) ℝ (Fin 1 → ℂ) := Complex.basisOneI.map lp_e.symm

theorem one_point_basis_repr (m : Fin 1 → ℂ) (i : Fin 2) : onePointRealBasis.repr m i = ![(m 0).re, (m 0).im] i := by
  rw [onePointRealBasis, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, lp_e_apply,
    Complex.coe_basisOneI_repr]

theorem lp_finrank : Module.finrank ℝ (Fin 1 → ℂ) = 2 := by
  rw [lp_e.finrank_eq, Complex.finrank_real_complex]

theorem lp_im (ω₁ ω₂ : ℂ) : (conj ω₁ * ω₂).im = ω₁.re * ω₂.im - ω₁.im * ω₂.re := by
  simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem real_linear_independent_of_im_ne_zero (ω₁ ω₂ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) (s t : ℝ)
    (h0 : (s : ℂ) * ω₁ + (t : ℂ) * ω₂ = 0) : s = 0 ∧ t = 0 := by
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
    Complex.add_im, Complex.mul_im, Complex.zero_im, zero_mul, sub_zero, add_zero] at hre him
  rw [lp_im] at hω
  have hs : s * (ω₁.re * ω₂.im - ω₁.im * ω₂.re) = 0 := by linear_combination ω₂.im * hre - ω₂.re * him
  have ht : t * (ω₁.re * ω₂.im - ω₁.im * ω₂.re) = 0 := by linear_combination ω₁.re * him - ω₁.im * hre
  exact ⟨(mul_eq_zero.1 hs).resolve_right hω, (mul_eq_zero.1 ht).resolve_right hω⟩

theorem lp_li (ω₁ ω₂ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) :
    LinearIndependent ℝ ![(fun _ : Fin 1 => ω₁), (fun _ : Fin 1 => ω₂)] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrFun h 0
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, Complex.real_smul] at h0
  exact real_linear_independent_of_im_ne_zero ω₁ ω₂ hω s t h0

def lp_b (ω₁ ω₂ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) : Module.Basis (Fin 2) ℝ (Fin 1 → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (lp_li ω₁ ω₂ hω) (by rw [lp_finrank]; rfl)

theorem lp_b_apply (ω₁ ω₂ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) :
    ⇑(lp_b ω₁ ω₂ hω) = ![(fun _ : Fin 1 => ω₁), (fun _ : Fin 1 => ω₂)] := by
  exact coe_basisOfLinearIndependentOfCardEqFinrank _ _

theorem one_point_basis_fundamental_domain_volume : (volume : Measure (Fin 1 → ℂ)) (ZSpan.fundamentalDomain onePointRealBasis) = 1 := by
  have hfd : ZSpan.fundamentalDomain onePointRealBasis =
      (MeasurableEquiv.funUnique (Fin 1) ℂ) ⁻¹' {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1} := by
    ext m
    simp [ZSpan.fundamentalDomain, one_point_basis_repr, Fin.forall_fin_two, MeasurableEquiv.funUnique]
  have hsq : {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1} =
      Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z; simp [Complex.measurableEquivRealProd]
  rw [hfd]
  erw [(volume_preserving_funUnique (Fin 1) ℂ).measure_preimage_equiv]
  rw [hsq,
    Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet), Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ico]
  simp

theorem lp_covol (ω₁ ω₂ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) :
    ZLattice.covolume (Submodule.span ℤ (Set.range (lp_b ω₁ ω₂ hω))) volume = |(conj ω₁ * ω₂).im| := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain (lp_b ω₁ ω₂ hω) volume),
    Measure.real, ZSpan.measure_fundamentalDomain (lp_b ω₁ ω₂ hω) volume onePointRealBasis, one_point_basis_fundamental_domain_volume, mul_one,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two, lp_im]
  simp [Module.Basis.toMatrix_apply, one_point_basis_repr, lp_b_apply]
  ring

theorem lp_psi (τ z : Fin 1 → ℂ) : crystallineComparison.psi (τ * z) = P5.fsv (2 * Real.pi * Complex.I * τ 0) (z 0) := by
  unfold crystallineComparison.psi P5.fsv
  congr 1
  simp only [Fin.sum_univ_one, Pi.mul_apply, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem lp_mem (ω₁ ω₂ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) (z : Fin 1 → ℂ) :
    z ∈ Submodule.span ℤ (Set.range (lp_b ω₁ ω₂ hω)) ↔
      ∃ a b : ℤ, z = fun _ => (a : ℂ) * ω₁ + (b : ℂ) * ω₂ := by
  rw [Submodule.mem_span_range_iff_exists_fun, lp_b_apply]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c 0, c 1, ?_⟩
    rw [← hc]
    funext i
    simp [Fin.sum_univ_two, zsmul_eq_mul]
  · rintro ⟨a, b, rfl⟩
    refine ⟨![a, b], ?_⟩
    funext i
    simp [Fin.sum_univ_two, zsmul_eq_mul]

theorem lp_dual (ω₁ ω₂ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) (τ : Fin 1 → ℂ) :
    τ ∈ crystallineComparison.dualSet (Submodule.span ℤ (Set.range (lp_b ω₁ ω₂ hω))) ↔
      TBB.InDual ω₁ ω₂ (2 * Real.pi * Complex.I * τ 0) := by
  unfold crystallineComparison.dualSet TBB.InDual
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h a b
    have := h _ ((lp_mem ω₁ ω₂ hω _).2 ⟨a, b, rfl⟩)
    simpa [lp_psi] using this
  · intro h z hz
    obtain ⟨a, b, rfl⟩ := (lp_mem ω₁ ω₂ hω z).1 hz
    simpa [lp_psi] using h a b

theorem lp_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

def lp_eqv (ω₁ ω₂ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) :
    {σ : ℂ // TBB.InDual ω₁ ω₂ σ} ≃ crystallineComparison.dualSet (Submodule.span ℤ (Set.range (lp_b ω₁ ω₂ hω))) where
  toFun σ := ⟨fun _ => σ.1 / (2 * Real.pi * Complex.I),
    (lp_dual ω₁ ω₂ hω _).2 (by rw [mul_div_cancel₀ _ lp_ne]; exact σ.2)⟩
  invFun τ := ⟨2 * Real.pi * Complex.I * τ.1 0, (lp_dual ω₁ ω₂ hω _).1 τ.2⟩
  left_inv σ := Subtype.ext (mul_div_cancel₀ _ lp_ne)
  right_inv τ := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    show 2 * Real.pi * Complex.I * τ.1 0 / (2 * Real.pi * Complex.I) = τ.1 0
    rw [mul_div_cancel_left₀ _ lp_ne]

theorem lp_fourier (E : ℂ → ℝ) (τ : Fin 1 → ℂ) :
    crystallineComparison.fourier (fun z => E (z 0)) τ = ∫ c : ℂ, P5.fsv (2 * Real.pi * Complex.I * τ 0) c * (E c : ℂ) := by
  unfold crystallineComparison.fourier
  simp_rw [lp_psi]
  have h := (volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
    (fun c : ℂ => P5.fsv (2 * Real.pi * Complex.I * τ 0) c * (E c : ℂ))
  rw [← h]
  congr 1
  funext z
  simp [MeasurableEquiv.funUnique, mul_comm]

theorem lp_inj (ω₁ ω₂ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) (z₀ : ℂ) :
    Function.Injective (fun ab : ℤ × ℤ => (fun _ : Fin 1 => z₀ + (ab.1 : ℂ) * ω₁ + (ab.2 : ℂ) * ω₂)) := by
  intro ab ab' h
  have h0 := congrFun h 0
  simp only at h0
  obtain ⟨hs, ht⟩ := real_linear_independent_of_im_ne_zero ω₁ ω₂ hω ((ab.1 - ab'.1 : ℤ) : ℝ) ((ab.2 - ab'.2 : ℤ) : ℝ)
    (by push_cast; linear_combination h0)
  have h1 : ab.1 - ab'.1 = 0 := by exact_mod_cast hs
  have h2 : ab.2 - ab'.2 = 0 := by exact_mod_cast ht
  exact Prod.ext (by omega) (by omega)

theorem lattice_poisson (E : ℂ → ℝ) (hE0 : ∀ z, 0 ≤ E z) (hEl : LowerSemicontinuous E) (hEi : Integrable E)
    (ω₁ ω₂ z₀ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) :
    ENNReal.ofReal (|(conj ω₁ * ω₂).im| / Real.pi) *
        ∑' ab : ℤ × ℤ, ENNReal.ofReal (E (z₀ + (ab.1 : ℂ) * ω₁ + (ab.2 : ℂ) * ω₂)) ≤
      ∑' σ : {σ : ℂ // TBB.InDual ω₁ ω₂ σ},
        (‖(Real.pi⁻¹ : ℂ) * ∫ z : ℂ, P5.fsv σ.1 z * (E z : ℂ)‖₊ : ℝ≥0∞) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hN0 : ∀ z : crystallineComparison.V 1, 0 ≤ (fun z : crystallineComparison.V 1 => E (z 0)) z := fun z => hE0 _
  have hNl : LowerSemicontinuous (fun z : crystallineComparison.V 1 => E (z 0)) :=
    LowerSemicontinuous.comp (f := E) (g := fun z : crystallineComparison.V 1 => z 0) hEl (continuous_apply 0)
  have hNi : Integrable (fun z : crystallineComparison.V 1 => E (z 0)) := by
    have h := (volume_preserving_funUnique (Fin 1) ℂ).integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding _) (g := E)
    exact h.2 hEi
  have hPD : crystallineComparison.PDOn (crystallineComparison.dualSet (Submodule.span ℤ (Set.range (lp_b ω₁ ω₂ hω)))) (fun _ => (0 : ℂ)) := by
    intro S c _
    simp
  set J : ℂ → ℂ := fun σ => ∫ z : ℂ, P5.fsv σ z * (E z : ℂ) with hJ
  have hF : ∀ τ : crystallineComparison.dualSet (Submodule.span ℤ (Set.range (lp_b ω₁ ω₂ hω))),
      ‖crystallineComparison.fourier (fun z : crystallineComparison.V 1 => E (z 0)) τ + (fun _ => (0 : ℂ)) (τ : crystallineComparison.V 1)‖ =
        (fun σ : {σ : ℂ // TBB.InDual ω₁ ω₂ σ} => ‖J σ.1‖) ((lp_eqv ω₁ ω₂ hω).symm τ) := by
    intro τ
    simp only [add_zero, hJ]
    rw [lp_fourier]
    rfl
  by_cases hs : Summable (fun σ : {σ : ℂ // TBB.InDual ω₁ ω₂ σ} => ‖J σ.1‖)
  · have hs' : Summable (fun τ : crystallineComparison.dualSet (Submodule.span ℤ (Set.range (lp_b ω₁ ω₂ hω))) =>
        ‖crystallineComparison.fourier (fun z : crystallineComparison.V 1 => E (z 0)) τ + (fun _ => (0 : ℂ)) (τ : crystallineComparison.V 1)‖) := by
      simp_rw [hF]
      exact (lp_eqv ω₁ ω₂ hω).symm.summable_iff.2 hs
    have hR : ∀ T : Finset (ℤ × ℤ), |(conj ω₁ * ω₂).im| * ∑ ab ∈ T, E (z₀ + (ab.1 : ℂ) * ω₁ + (ab.2 : ℂ) * ω₂) ≤
        ∑' σ : {σ : ℂ // TBB.InDual ω₁ ω₂ σ}, ‖J σ.1‖ := by
      intro T
      have h1 := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement 1 (Submodule.span ℤ (Set.range (lp_b ω₁ ω₂ hω)))
        (fun z : crystallineComparison.V 1 => E (z 0)) (fun _ => 0) hN0 hNl hNi hPD hs' (fun _ => z₀)
        (T.image (fun ab : ℤ × ℤ => (fun _ : Fin 1 => z₀ + (ab.1 : ℂ) * ω₁ + (ab.2 : ℂ) * ω₂))) (by
          intro z hz
          obtain ⟨ab, -, rfl⟩ := Finset.mem_image.1 hz
          refine (lp_mem ω₁ ω₂ hω _).2 ⟨ab.1, ab.2, ?_⟩
          funext i
          simp only [Pi.sub_apply]
          ring)
      rw [lp_covol, Finset.sum_image (fun x _ y _ h => lp_inj ω₁ ω₂ hω z₀ h)] at h1
      simp_rw [hF] at h1
      rw [(lp_eqv ω₁ ω₂ hω).symm.tsum_eq (fun σ : {σ : ℂ // TBB.InDual ω₁ ω₂ σ} => ‖J σ.1‖)] at h1
      exact h1
    have hrhs : ∑' σ : {σ : ℂ // TBB.InDual ω₁ ω₂ σ},
        (‖(Real.pi⁻¹ : ℂ) * ∫ z : ℂ, P5.fsv σ.1 z * (E z : ℂ)‖₊ : ℝ≥0∞) =
          ENNReal.ofReal (Real.pi⁻¹ * ∑' σ : {σ : ℂ // TBB.InDual ω₁ ω₂ σ}, ‖J σ.1‖) := by
      rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (hs.mul_left _)]
      congr 1
      funext σ
      rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, norm_mul]
      simp [hJ, abs_of_pos hpi]
    rw [hrhs, ENNReal.tsum_eq_iSup_sum, ENNReal.mul_iSup]
    refine iSup_le fun T => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hE0 _), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_eq_inv_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hR T) (by positivity)
  · have htop : ∑' σ : {σ : ℂ // TBB.InDual ω₁ ω₂ σ},
        (‖(Real.pi⁻¹ : ℂ) * ∫ z : ℂ, P5.fsv σ.1 z * (E z : ℂ)‖₊ : ℝ≥0∞) = ⊤ := by
      by_contra hne
      apply hs
      have h2 := ENNReal.tsum_coe_ne_top_iff_summable.1 hne
      have h3 : Summable (fun σ : {σ : ℂ // TBB.InDual ω₁ ω₂ σ} =>
          ‖(Real.pi⁻¹ : ℂ) * ∫ z : ℂ, P5.fsv σ.1 z * (E z : ℂ)‖) := by
        rw [← NNReal.summable_coe] at h2
        simpa using h2
      have h4 := h3.mul_left Real.pi
      refine h4.congr fun σ => ?_
      rw [norm_mul]
      simp [hJ, abs_of_pos hpi, hpi.ne']
    rw [htop]
    exact le_top

end

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P.TBBx5

open Formalism.FourierDecayAlt Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal ComplexOrder

noncomputable section

open Classical

section lift

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def LiftGrid (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) : Prop :=
  ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → b + s - 1 ≤ P.r → ∀ w, TBB.AdmW P p.l0 Y w → w.length + K ≤ N →
    ∃ grid : Fin K → Fin (2 * (b + s - 1 - s) + s + 1) → ℝ, GridOK p nn Y Λ K w (2 * (b + s - 1 - s) + s) grid

theorem li_locPt (h : C.LPt) (b s : ℕ) (t : ℂ) (hb : 1 ≤ b) (hs : 1 ≤ s) (hh : D.IsLocPt h (b - 1))
    (ht : t ≠ 0) : D.IsLocPt (h ++ [(s, t)]) (b + s - 1) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact hh.1 x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hs, ht⟩
  · have h2 := hh.2
    unfold D.ptSize at h2 ⊢
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem li_ew (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
    (w' : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a j) :
    TBB.Ew p nn F j w' a = (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) /
      TBB.normC nn w') * (p.form j hj w' (KB.slv p.T F j hj w' a ha.2) (KB.slv p.T F j hj w' a ha.2)).re := by
  unfold TBB.Ew TBB.NP
  rw [Complex.re_ofReal_mul, PBL.rr_eq_form p F j hj w' a a ha ha]

theorem li_np (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
    (w : List C.Letter) (a a' : C.LPt) (ha : D.IsLocPt a j) (ha' : D.IsLocPt a' j) :
    TBB.NP p nn F j w a a' = ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) *
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a') / TBB.normC nn w : ℝ) : ℂ) *
        p.form j hj w (KB.slv p.T F j hj w a ha.2) (KB.slv p.T F j hj w a' ha'.2) := by
  unfold TBB.NP
  rw [PBL.rr_eq_form p F j hj w a a' ha ha']

theorem integral_four_at_place_of_parts (hA : P5.ThmPActual) (hSS : KB.SizeStd) (hDL : KB.DegLift) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (hpos : FormNonneg p)
    (hF : KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (hgrid : LiftGrid p nn Y Λ K N) :
    TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N := by
  intro b s hb hs hbs h hh w hw hN t t' ht ht'
  set j := b + s - 1 with hjdef
  have hj : j ≤ P.r := hbs
  obtain ⟨grid, hinj, hY, hcut, hsum⟩ := hgrid b s hb hs hbs w hw hN
  simp only [ysOf] at hsum hcut
  have ha := li_locPt h b s t hb hs hh ht
  have ha' := li_locPt h b s t' hb hs hh ht'
  set u := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) with hudef
  set u' := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) with hu'def
  set n := TBB.normC nn w with hndef
  have hn : 0 < n := normC_pos nn hnn w
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu' : 0 ≤ u' := Real.sqrt_nonneg _
  have hα : 0 ≤ u * u' / n := by positivity
  set x := KB.slv p.T F j hj w _ ha.2 with hxdef
  set x' := KB.slv p.T F j hj w _ ha'.2 with hx'def
  have hNP : ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ = (u * u' / n) * ‖p.form j hj w x x'‖ := by
    rw [li_np p nn F j hj w _ _ ha ha', norm_mul, Complex.norm_real, Real.norm_of_nonneg hα]

  have c1 : ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤
      (TBB.Ew p nn F j w (h ++ [(s, t)]) + TBB.Ew p nn F j w (h ++ [(s, t')])) / 2 := by
    obtain ⟨ε₁, hε₁, hx⟩ := PBL.slv_nv p hF j hj w _ ha
    obtain ⟨ε₂, hε₂, hx'⟩ := PBL.slv_nv p hF j hj w _ ha'
    have hxm := PBL.nv_mono hx (min_le_left ε₁ ε₂)
    have hx'm := PBL.nv_mono hx' (min_le_right ε₁ ε₂)
    have hcs := form_cs p hpos j hj w hw.1 (lt_min hε₁ hε₂) x x' hxm hx'm
    have hf := form_re_nonneg p hpos j hj w hw.1 hε₁ x hx
    have hf' := form_re_nonneg p hpos j hj w hw.1 hε₂ x' hx'
    have key := scal_cs (u * u' / n) (u * u / n) (u' * u' / n) ‖p.form j hj w x x'‖ 1 1 1
      (p.form j hj w x x).re (p.form j hj w x' x').re hα (by field_simp) (by positivity) (by positivity)
      one_pos one_pos one_pos (norm_nonneg _) hf hf' (by rw [mul_one]; exact hcs)
    rw [hNP, li_ew p nn F j hj w _ ha, li_ew p nn F j hj w _ ha']
    refine key.trans ?_
    simp only [mul_one, div_one, Real.sqrt_one, one_mul]
    exact sqrt_mul_le_avg _ _ (mul_nonneg (by positivity) hf) (mul_nonneg (by positivity) hf')

  have hEnn : ∀ (w' : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a j), KB.CutWord P p.l0 w' →
      0 ≤ TBB.Ew p nn F j w' a := by
    intro w' a ha hw'
    rw [li_ew p nn F j hj w' a ha]
    obtain ⟨ε, hε, hxa⟩ := PBL.slv_nv p hF j hj w' a ha
    exact mul_nonneg (div_nonneg (mul_self_nonneg _) (normC_pos nn hnn w').le)
      (form_re_nonneg p hpos j hj w' hw' hε _ hxa)

  have hdeg := hDL Wp Wq P p F j s hj w h h t t' ha ha' K grid hF hinj
  rw [PBL.rr_eq_form p F j hj w _ _ ha ha'] at hdeg
  have hper : ∀ m : Fin K → Fin (2 * (j - s) + s + 1),
      (u * u' / n) * ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
          (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) _ ha.2)
          (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) _ ha'.2)‖ ≤
        Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
          ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
          ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
        ((TBB.Ew p nn F j (KB.plusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t)]) +
          TBB.Ew p nn F j (KB.minusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t')])) / 2) := by
    intro m
    set ys := List.ofFn fun a => grid a (m a) with hys
    obtain ⟨hqpos, hSSm⟩ := hSS hA Wp Wq P p j hj w ys (hcut m).1 (hcut m).2.1 (hcut m).2.2
    obtain ⟨ε₁, hε₁, hx⟩ := PBL.slv_nv p hF j hj (KB.plusW ys w) _ ha
    obtain ⟨ε₂, hε₂, hx'⟩ := PBL.slv_nv p hF j hj (KB.minusW ys w) _ ha'
    have hxm := PBL.nv_mono hx (min_le_left ε₁ ε₂)
    have hx'm := PBL.nv_mono hx' (min_le_right ε₁ ε₂)
    have hcs := hSSm _ _ _ (lt_min hε₁ hε₂) hxm hx'm
    set fp := (p.form j hj (KB.plusW ys w) (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, t)]) ha.2)
      (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, t)]) ha.2)).re with hfp
    set fm := (p.form j hj (KB.minusW ys w) (KB.slv p.T F j hj (KB.minusW ys w) (h ++ [(s, t')]) ha'.2)
      (KB.slv p.T F j hj (KB.minusW ys w) (h ++ [(s, t')]) ha'.2)).re with hfm
    have hf : 0 ≤ fp := form_re_nonneg p hpos j hj _ (hcut m).1 hε₁ _ hx
    have hf' : 0 ≤ fm := form_re_nonneg p hpos j hj _ (hcut m).2.1 hε₂ _ hx'
    have hq : 0 < (ys.map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod := by
      refine List.prod_pos fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      exact hqpos y hy
    have hQ₁ := prod_map_pos nn hnn ys
    have hQ₂ := prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) ys
    have key := scal_cs (u * u' / n) (u * u / n) (u' * u' / n) _ _ _ _ fp fm hα (by field_simp) (by positivity)
      (by positivity) hq hQ₁ hQ₂ (norm_nonneg _) hf hf' hcs
    refine key.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [li_ew p nn F j hj _ _ ha, li_ew p nn F j hj _ _ ha', normC_plusW, normC_minusW, ← hfp, ← hfm]
    have e₁ : u * u / n * fp / (ys.map nn).prod = u * u / ((ys.map nn).prod * n) * fp := by
      field_simp
    have e₂ : u' * u' / n * fm / (ys.map fun y => nn (y + 1)).prod =
        u' * u' / ((ys.map fun y => nn (y + 1)).prod * n) * fm := by
      field_simp
    rw [e₁, e₂]
    exact sqrt_mul_le_avg _ _ (by positivity) (by positivity)
  set g : (Fin K → Fin (2 * (j - s) + s + 1)) → ℝ := fun m =>
    (TBB.Ew p nn F j (KB.plusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t)]) +
      TBB.Ew p nn F j (KB.minusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t')])) / 2 with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m =>
    div_nonneg (add_nonneg (hEnn _ _ ha (hcut m).1) (hEnn _ _ ha' (hcut m).2.1)) zero_le_two
  obtain ⟨m₀, hm₀⟩ := sum_le_max (fun m => |∏ a, F7.lagCo (grid a) (m a)| *
      Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
        ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod))
    g (Λ ^ K) (fun m => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hg0 hsum
  have c2 : ‖t⁻¹ - t'⁻¹‖ ^ K * ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤ Λ ^ K * g m₀ := by
    have hn1 : ‖((-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) ^ K * p.form j hj w x x'‖ =
        ‖t⁻¹ - t'⁻¹‖ ^ K * ‖p.form j hj w x x'‖ := by
      rw [norm_mul, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [hNP]
    calc ‖t⁻¹ - t'⁻¹‖ ^ K * (u * u' / n * ‖p.form j hj w x x'‖)
        = u * u' / n * ‖((-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) ^ K * p.form j hj w x x'‖ := by rw [hn1]; ring
      _ ≤ u * u' / n * ∑ m : Fin K → Fin (2 * (j - s) + s + 1), ‖((∏ a, F7.lagCo (grid a) (m a) : ℝ) : ℂ)‖ *
          ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
            (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) _ ha.2)
            (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) _ ha'.2)‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hα
          rw [hdeg]
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun m _ => norm_mul _ _
      _ = ∑ m : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          (u * u' / n * ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
            (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) _ ha.2)
            (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) _ ha'.2)‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
          ring
      _ ≤ ∑ m : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          (Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
            ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
            ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            g m) :=
          Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hper m) (abs_nonneg _)
      _ = ∑ m : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
            ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
            ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            g m := Finset.sum_congr rfl fun m _ => by ring
      _ ≤ Λ ^ K * g m₀ := hm₀
  rcases mn_pick Λ ‖t⁻¹ - t'⁻¹‖ _ _ (g m₀) K (norm_nonneg _) c1 (fun _ => c2) with hc | hc
  · exact ⟨w, w, isExt_self P p.l0 Y N K w hw (by omega), isExt_self P p.l0 Y N K w hw (by omega), hc⟩
  · refine ⟨KB.plusW (List.ofFn fun a => grid a (m₀ a)) w, KB.minusW (List.ofFn fun a => grid a (m₀ a)) w,
      isExt_plusW P p.l0 Y N K w _ hN (by simp) (ysOf_mem grid hY m₀) (hcut m₀).1,
      isExt_minusW P p.l0 Y N K w _ hN (by simp) (ysOf_mem grid hY m₀) (hcut m₀).2.1, hc⟩

end lift

end

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P.TBBx5

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal ComplexOrder

noncomputable section

open Classical

section wave

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def WaveGrid (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) : Prop :=
  ∀ j, j ≤ P.r → ∀ w, TBB.AdmW P p.l0 Y w → w.length + K ≤ N →
    ∃ grid : Fin K → Fin (2 * j + 1) → ℝ, GridOK p nn Y Λ K w (2 * j) grid

theorem wv_nPt (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j) :
    TBB.nPt P.k P.r (TBB.TTp p) h = C.nAux P.k P.r 0 (fun _ _ => 1) 1 h := by
  unfold TBB.nPt
  exact Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)

theorem weighted_auxiliary_norm_nonneg (P : M.Par) (j : ℕ) (hj : j ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j) :
    0 ≤ C.nAux P.k P.r 0 (fun _ _ => 1) 1 h :=
  Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl (by rw [hh.2]; omega)

theorem wv_np (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
    (h : C.LPt) (hh : D.IsLocPt h j) (w : List C.Letter) (c : ℂ) :
    ((C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w : ℝ) : ℂ) *
        ((KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])) =
      TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) := by
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef
  have hA : 0 ≤ A := weighted_auxiliary_norm_nonneg P j hj h hh
  have hn : TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(1, c)]) =
      A * C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] := by
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hh.2, hAdef,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)]
  unfold TBB.NP
  rw [hn]
  by_cases hjr : j = P.r
  · subst hjr
    by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
    · have h0 : p.RR F (P.r + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = 0 :=
        Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w h _ c hh.2 hc2
      rw [h0]
      simp
    · push Not at hc2
      have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
      have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
      have hlast : D.ptGG (TBB.TTp p) (h ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
        simp [D.ptGG, D.ptLast]
      have hTT : TBB.TTp p = P.T * P.T' := by
        unfold TBB.TTp
        rw [hT, hT']
      have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
          KB.levW P (P.r + 1) c := by
        rw [hlast, hTT]
        rw [hT, hT'] at hc2
        simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
        rw [if_pos ⟨by omega, trivial⟩]
        simp
      have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
        rw [← hfac, hlast]
        simp only [C.nAux]
        rw [if_pos ⟨by omega, trivial⟩]
        have : 0 ≤ Complex.normSq c - TBB.TTp p := by
          unfold TBB.TTp; linarith
        simpa using pow_nonneg this _
      rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
      push_cast
      ring
  · have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] =
        KB.levW P (j + 1) c := by
      simp only [C.nAux, KB.levW]
      rw [if_neg (by omega), if_neg (by omega)]
      have e : 1 + j + 1 - 1 = j + 1 := by omega
      rw [e]
      simp only [one_mul, mul_one, Nat.cast_one]
      congr 1
      ring
    have hlev : 0 ≤ KB.levW P (j + 1) c := by
      simp only [KB.levW]
      rw [if_neg (by omega)]
      exact zpow_nonneg (norm_nonneg _) _
    rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
    push_cast
    ring

theorem wv_ew (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
    (w' : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j) :
    TBB.Ew p nn F j w' h = (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w') *
      (p.form j hj w' (KB.slv p.T F j hj w' h hh.2) (KB.slv p.T F j hj w' h hh.2)).re := by
  rw [li_ew p nn F j hj w' h hh, wv_nPt p j hj h hh, Real.mul_self_sqrt (weighted_auxiliary_norm_nonneg P j hj h hh)]

theorem integral_three_at_place_of_parts (hA : P5.ThmPActual) (hPS : KB.PStd) (hVI : KB.VIso) (hSS : KB.SizeStd) (hDW : KB.DegWave)
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hpos : FormNonneg p) (hF : KB.CptCoef p.T.base F)
    (hnn : ∀ y, 0 < nn y) (hgrid : WaveGrid p nn Y Λ K N) : TBB.KernelFourierIntegralBound p nn F Y Λ K N := by
  intro j hj h hh w hw hN s
  obtain ⟨grid, hinj, hY, hcut, hsum⟩ := hgrid j hj w hw hN
  simp only [ysOf] at hsum hcut
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef
  have hA0 : 0 ≤ A := weighted_auxiliary_norm_nonneg P j hj h hh
  set n := TBB.normC nn w with hndef
  have hn : 0 < n := normC_pos nn hnn w
  have hα : 0 ≤ A / n := div_nonneg hA0 hn.le
  set x := KB.slv p.T F j hj w h hh.2 with hxdef
  obtain ⟨φ, -, -, hφ, hφs⟩ := hPS hA Wp Wq P p F j hj w h h hh hh Cb hCb hF hw.1

  have hint : ∫ c : ℂ, P5.fsv s c * TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) =
      ((A / n : ℝ) : ℂ) * p.form j hj w (KB.waveG (p.T.bs j) s w x) x := by
    rw [← hφs s, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [PBL.ae_ne_zero_complex] with c hc
    rw [← wv_np p nn F j hj h hh w c, ← hφ c hc]
    ring
  set I := ‖∫ c : ℂ, P5.fsv s c * TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ with hIdef
  have hI : I = A / n * ‖p.form j hj w (KB.waveG (p.T.bs j) s w x) x‖ := by
    rw [hIdef, hint, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα]

  have hEnn : ∀ w' : List C.Letter, KB.CutWord P p.l0 w' → 0 ≤ TBB.Ew p nn F j w' h := by
    intro w' hw'
    rw [wv_ew p nn F j hj w' h hh]
    obtain ⟨ε, hε, hxa⟩ := PBL.slv_nv p hF j hj w' h hh
    exact mul_nonneg (div_nonneg hA0 (normC_pos nn hnn w').le) (form_re_nonneg p hpos j hj w' hw' hε _ hxa)

  have c1 : I ≤ TBB.Ew p nn F j w h := by
    obtain ⟨ε, hε, hx⟩ := PBL.slv_nv p hF j hj w h hh
    obtain ⟨hVn, hVeq⟩ := hVI hA Wp Wq P p j hj w hw.1 s x x ε hε hx hx
    have hcs := form_cs p hpos j hj w hw.1 hε (KB.waveG (p.T.bs j) s w x) x hVn hx
    rw [hVeq] at hcs
    have hf := form_re_nonneg p hpos j hj w hw.1 hε x hx
    have key := scal_cs (A / n) (A / n) (A / n) ‖p.form j hj w (KB.waveG (p.T.bs j) s w x) x‖ 1 1 1
      (p.form j hj w x x).re (p.form j hj w x x).re hα (by ring) hα hα one_pos one_pos one_pos (norm_nonneg _)
      hf hf (by rw [mul_one]; exact hcs)
    rw [hI, wv_ew p nn F j hj w h hh]
    refine key.trans (le_of_eq ?_)
    simp only [mul_one, div_one, Real.sqrt_one, one_mul]
    exact Real.sqrt_mul_self (mul_nonneg hα hf)

  have hdeg := hDW Wp Wq P p F j hj w h h hh hh K grid s LinearMap.id (fun ε x hx => hx) hF hinj
  simp only [PBL.onOld_id] at hdeg
  simp only [LinearMap.id_coe, id] at hdeg
  have hper : ∀ m : Fin K → Fin (2 * j + 1),
      (A / n) * ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
          (KB.waveG (p.T.bs j) s (KB.plusW (List.ofFn fun a => grid a (m a)) w)
            (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) h hh.2))
          (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) h hh.2)‖ ≤
        Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
          ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
          ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
        max (TBB.Ew p nn F j (KB.plusW (List.ofFn fun a => grid a (m a)) w) h)
          (TBB.Ew p nn F j (KB.minusW (List.ofFn fun a => grid a (m a)) w) h) := by
    intro m
    set ys := List.ofFn fun a => grid a (m a) with hys
    obtain ⟨hqpos, hSSm⟩ := hSS hA Wp Wq P p j hj w ys (hcut m).1 (hcut m).2.1 (hcut m).2.2
    obtain ⟨ε₁, hε₁, hx⟩ := PBL.slv_nv p hF j hj (KB.plusW ys w) h hh
    obtain ⟨ε₂, hε₂, hx'⟩ := PBL.slv_nv p hF j hj (KB.minusW ys w) h hh
    obtain ⟨hVn, hVeq⟩ := hVI hA Wp Wq P p j hj (KB.plusW ys w) (hcut m).1 s _ _ ε₁ hε₁ hx hx
    have hxm := PBL.nv_mono hVn (min_le_left ε₁ ε₂)
    have hx'm := PBL.nv_mono hx' (min_le_right ε₁ ε₂)
    have hcs := hSSm _ _ _ (lt_min hε₁ hε₂) hxm hx'm
    rw [hVeq] at hcs
    set fp := (p.form j hj (KB.plusW ys w) (KB.slv p.T F j hj (KB.plusW ys w) h hh.2)
      (KB.slv p.T F j hj (KB.plusW ys w) h hh.2)).re with hfp
    set fm := (p.form j hj (KB.minusW ys w) (KB.slv p.T F j hj (KB.minusW ys w) h hh.2)
      (KB.slv p.T F j hj (KB.minusW ys w) h hh.2)).re with hfm
    have hf : 0 ≤ fp := form_re_nonneg p hpos j hj _ (hcut m).1 hε₁ _ hx
    have hf' : 0 ≤ fm := form_re_nonneg p hpos j hj _ (hcut m).2.1 hε₂ _ hx'
    have hq : 0 < (ys.map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod := by
      refine List.prod_pos fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      exact hqpos y hy
    have hQ₁ := prod_map_pos nn hnn ys
    have hQ₂ := prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) ys
    have key := scal_cs (A / n) (A / n) (A / n) _ _ _ _ fp fm hα (by ring) hα hα hq hQ₁ hQ₂ (norm_nonneg _)
      hf hf' hcs
    refine key.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [wv_ew p nn F j hj _ h hh, wv_ew p nn F j hj _ h hh, normC_plusW, normC_minusW, ← hfp, ← hfm]
    have e₁ : A / n * fp / (ys.map nn).prod = A / ((ys.map nn).prod * n) * fp := by
      field_simp
    have e₂ : A / n * fm / (ys.map fun y => nn (y + 1)).prod =
        A / ((ys.map fun y => nn (y + 1)).prod * n) * fm := by
      field_simp
    rw [e₁, e₂]
    exact sqrt_mul_le_max _ _ (by positivity) (by positivity)
  set g : (Fin K → Fin (2 * j + 1)) → ℝ := fun m =>
    max (TBB.Ew p nn F j (KB.plusW (List.ofFn fun a => grid a (m a)) w) h)
      (TBB.Ew p nn F j (KB.minusW (List.ofFn fun a => grid a (m a)) w) h) with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m => le_max_of_le_left (hEnn _ (hcut m).1)
  obtain ⟨m₀, hm₀⟩ := sum_le_max (fun m => |∏ a, F7.lagCo (grid a) (m a)| *
      Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
        ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod))
    g (Λ ^ K) (fun m => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hg0 hsum
  have c2 : ‖s‖ ^ K * I ≤ Λ ^ K * g m₀ := by
    rw [hI]
    calc ‖s‖ ^ K * (A / n * ‖p.form j hj w (KB.waveG (p.T.bs j) s w x) x‖)
        = A / n * ‖s ^ K * p.form j hj w (KB.waveG (p.T.bs j) s w x) x‖ := by
          rw [norm_mul, norm_pow]; ring
      _ ≤ A / n * ∑ m : Fin K → Fin (2 * j + 1), ‖((∏ a, F7.lagCo (grid a) (m a) : ℝ) : ℂ)‖ *
          ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
            (KB.waveG (p.T.bs j) s (KB.plusW (List.ofFn fun a => grid a (m a)) w)
              (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) h hh.2))
            (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) h hh.2)‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hα
          rw [hxdef, hdeg]
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun m _ => norm_mul _ _
      _ = ∑ m : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          (A / n * ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
            (KB.waveG (p.T.bs j) s (KB.plusW (List.ofFn fun a => grid a (m a)) w)
              (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) h hh.2))
            (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) h hh.2)‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
          ring
      _ ≤ ∑ m : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          (Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
            ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
            ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            g m) :=
          Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hper m) (abs_nonneg _)
      _ = ∑ m : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
            ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
            ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            g m := Finset.sum_congr rfl fun m _ => by ring
      _ ≤ Λ ^ K * g m₀ := hm₀
  rcases mn_pick Λ ‖s‖ I _ (g m₀) K (norm_nonneg _) c1 (fun _ => c2) with hc | hc
  · exact ⟨w, isExt_self P p.l0 Y N K w hw (by omega), hc⟩
  · rcases le_total (TBB.Ew p nn F j (KB.minusW (List.ofFn fun a => grid a (m₀ a)) w) h)
      (TBB.Ew p nn F j (KB.plusW (List.ofFn fun a => grid a (m₀ a)) w) h) with hle | hle
    · refine ⟨KB.plusW (List.ofFn fun a => grid a (m₀ a)) w,
        isExt_plusW P p.l0 Y N K w _ hN (by simp) (ysOf_mem grid hY m₀) (hcut m₀).1, ?_⟩
      have : g m₀ = TBB.Ew p nn F j (KB.plusW (List.ofFn fun a => grid a (m₀ a)) w) h := max_eq_left hle
      rw [← this]; exact hc
    · refine ⟨KB.minusW (List.ofFn fun a => grid a (m₀ a)) w,
        isExt_minusW P p.l0 Y N K w _ hN (by simp) (ysOf_mem grid hY m₀) (hcut m₀).2.1, ?_⟩
      have : g m₀ = TBB.Ew p nn F j (KB.minusW (List.ofFn fun a => grid a (m₀ a)) w) h := max_eq_right hle
      rw [← this]; exact hc

end wave

end

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P.TBBx5

open Formalism.FourierDecayAlt Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal ComplexOrder

noncomputable section

open Classical

section germ

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def GermAt (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) :
    Prop :=
  ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r + 1 → ∀ h : C.LPt, D.IsLocPt h (b - 1) → ∀ w, TBB.AdmW P p.l0 Y w →
    w.length + K ≤ N →
    (∀ w', TBB.IsExt P p.l0 Y N K w w' →
      BddAbove (Set.range fun t : {t : ℂ // t ≠ 0} => TBB.Ew p nn F (b + s - 2) w' (h ++ [(s - 1, t.1)]))) →
    ContinuousOn (fun z : ℂ => TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)])) {0}ᶜ ∧
    Integrable (fun z : ℂ => TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)])) ∧
    ∀ σ : ℂ, (‖(Real.pi⁻¹ : ℂ) * ∫ z : ℂ, P5.fsv σ z * (TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) : ℂ)‖₊ :
        ℝ≥0∞) ≤
      limsup (fun t : ℂ =>
        (‖TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, (t⁻¹ + σ)⁻¹)])‖₊ : ℝ≥0∞)) (𝓝[≠] 0)

theorem gm_ew_zero (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ)
    (w : List C.Letter) (h : C.LPt) (s : ℕ) : TBB.Ew p nn F i w (h ++ [(s, 0)]) = 0 := by
  have hn : ¬ (D.IsLocPt (h ++ [(s, 0)]) i ∧ D.IsLocPt (h ++ [(s, 0)]) i) := by
    rintro ⟨⟨h1, -⟩, -⟩
    exact (h1 (s, 0) (List.mem_append_right _ (List.mem_singleton_self _))).2 rfl
  unfold TBB.Ew TBB.NP KB.Pl.RR D.RRplace
  rw [dif_neg hn]
  simp

theorem integral_five_at_place_of_parts (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (K N : ℕ) (hP : TBB.PosAt p nn F Y N) (hG : GermAt p nn F Y K N) : TBB.BlockGrowthBound p nn F Y K N := by
  intro b s hb hs hbs h hh w hw hN hBdd ω₁ ω₂ z₀ hω
  obtain ⟨hcont, hint, htr⟩ := hG b s hb hs hbs h hh w hw hN hBdd
  set E : ℂ → ℝ := fun z => TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) with hEdef
  have hE0 : ∀ z, 0 ≤ E z := fun z => hP (b + s - 1) w (h ++ [(s, z)]) hw (by omega)
  have hEz : E 0 = 0 := gm_ew_zero p nn F (b + s - 1) w h s
  have hlsc : LowerSemicontinuous E := by
    intro z
    by_cases hz : z = 0
    · subst hz
      intro y hy
      rw [hEz] at hy
      exact Filter.Eventually.of_forall fun z' => lt_of_lt_of_le hy (hE0 z')
    · exact (hcont.continuousAt (isOpen_compl_singleton.mem_nhds hz)).lowerSemicontinuousAt
  refine ⟨fun σ => (Real.pi⁻¹ : ℂ) * ∫ z : ℂ, P5.fsv σ z * (E z : ℂ), ?_, fun σ _ => htr σ⟩
  exact lattice_poisson E hE0 hlsc hint ω₁ ω₂ z₀ hω

end germ

end

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P.TBBx5

open Formalism.FourierDecayAlt

def CurvatureIntegralOfParts : Prop :=
  P5.ThmPActual → KB.PStd → KB.VIso → KB.SizeStd → KB.DegWave → PBL.FormPos →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → WaveGrid p nn Y Λ K N →
    TBB.KernelFourierIntegralBound p nn F Y Λ K N

def IntegralFourFromComponents : Prop :=
  P5.ThmPActual → KB.SizeStd → KB.DegLift → PBL.FormPos →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ),
    KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → LiftGrid p nn Y Λ K N → TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N

def IntegralFiveFromComponents : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ),
    TBB.PosAt p nn F Y N → GermAt p nn F Y K N → TBB.BlockGrowthBound p nn F Y K N

theorem integral_three_of_parts_holds : CurvatureIntegralOfParts := by
  intro hA hPS hVI hSS hDW hFP Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N Cb hCb hF hnn hgrid
  exact integral_three_at_place_of_parts hA hPS hVI hSS hDW p nn F Y Λ K N Cb hCb (formNonneg_of hA hFP p) hF hnn hgrid

theorem integral_four_of_parts_holds : IntegralFourFromComponents := by
  intro hA hSS hDL hFP Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hF hnn hgrid
  exact integral_four_at_place_of_parts hA hSS hDL p nn F Y Λ K N (formNonneg_of hA hFP p) hF hnn hgrid

theorem integral_five_of_parts_holds : IntegralFiveFromComponents := by
  intro Wp Wq _ _ _ _ _ _ P p nn F Y K N hP hG
  exact integral_five_at_place_of_parts p nn F Y K N hP hG

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem integral_three_at_place (hA : P5.ThmPActual) (hPS : KB.PStd) (hVI : KB.VIso) (hSS : KB.SizeStd)
    (hDW : KB.DegWave) (hFP : PBL.FormPos) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y)
    (hgrid : TBBx5.WaveGrid p nn Y Λ K N) : Formalism.FourierDecayAlt.TBB.KernelFourierIntegralBound p nn F Y Λ K N := TBBx5.integral_three_of_parts_holds hA hPS hVI hSS hDW hFP Wp Wq P p nn F Y Λ K N Cb hCb hF hnn hgrid

theorem integral_four_at_place (hA : P5.ThmPActual) (hSS : KB.SizeStd) (hDL : KB.DegLift) (hFP : PBL.FormPos)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (hF : KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (hgrid : TBBx5.LiftGrid p nn Y Λ K N) :
    Formalism.FourierDecayAlt.TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N := TBBx5.integral_four_of_parts_holds hA hSS hDL hFP Wp Wq P p nn F Y Λ K N hF hnn hgrid

theorem integral_five_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (hP : Formalism.FourierDecayAlt.TBB.PosAt p nn F Y N)
    (hG : TBBx5.GermAt p nn F Y K N) : Formalism.FourierDecayAlt.TBB.BlockGrowthBound p nn F Y K N := TBBx5.integral_five_of_parts_holds Wp Wq P p nn F Y K N hP hG

end Formalism.FourierDecayAlt.P
