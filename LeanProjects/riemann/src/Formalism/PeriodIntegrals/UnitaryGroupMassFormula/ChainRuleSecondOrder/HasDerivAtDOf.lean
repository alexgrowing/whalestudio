import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

open Matrix Filter Topology

noncomputable section

namespace PI.ComplexConjugateDerivative

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

variable {k r : ℕ}

def sgI (k r : ℕ) (i : ℕ) : ℕ := if i < r ∨ r + k < i then 2 * r + k - i else i

lemma hpk_apply (i l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if l.val = sgI k r i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hl := l.isLt
  simp only [Hpk, sgI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | norm_num

lemma sgI_lt (i : Fin (2 * r + k + 1)) : sgI k r i.val < 2 * r + k + 1 := by
  have hi := i.isLt
  unfold sgI
  split_ifs <;> omega

lemma sgI_sgI (i : Fin (2 * r + k + 1)) : sgI k r (sgI k r i.val) = i.val := by
  have hi := i.isLt
  unfold sgI
  split_ifs <;> omega

lemma sgI_eq_iff (i : Fin (2 * r + k + 1)) : sgI k r i.val = r + k ↔ i.val = r + k := by
  have hi := i.isLt
  unfold sgI
  split_ifs <;> constructor <;> intro h <;> omega

theorem hpk_mul_self : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨sgI k r i.val, sgI_lt i⟩ : Fin (2 * r + k + 1))]
  · rw [hpk_apply, hpk_apply]
    simp only [Fin.val_mk, sgI_sgI, sgI_eq_iff, eq_self_iff_true, if_true]
    by_cases hij : i = j
    · subst hij
      simp only [eq_self_iff_true, if_true]
      split_ifs <;> norm_num
    · have hji : j.val ≠ i.val := fun h => hij (Fin.ext h).symm
      simp [hij, hji]
  · intro l _ hl
    rw [hpk_apply i l, if_neg, zero_mul]
    intro h
    exact hl (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem hpk_det_ne : (Hpk k r).det ≠ 0 := by
  intro h
  have e := congrArg Matrix.det (hpk_mul_self (k := k) (r := r))
  rw [Matrix.det_mul, Matrix.det_one, h, zero_mul] at e
  exact zero_ne_one e

theorem hpk_ne_zero : Hpk k r ≠ 0 := by
  intro h
  have e := hpk_det_ne (k := k) (r := r)
  rw [h, Matrix.det_zero] at e
  exact e rfl

theorem mul_mem_GV {a b : B.Mat k r} (ha : a ∈ B.GV k r) (hb : b ∈ B.GV k r) : a * b ∈ B.GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul,
    show bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b by simp only [Matrix.mul_assoc],
    ha', hb']

theorem inLie_neg {X : B.Mat k r} (hX : B.inLie k r X) : B.inLie k r (-X) := by
  unfold B.inLie at *
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX, neg_zero]

theorem exp_mem_GV {X : B.Mat k r} (hX : B.inLie k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ B.GV k r := by
  have hH2 : Hpk k r * Hpk k r = 1 := hpk_mul_self
  have hU : IsUnit (Hpk k r) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hpk_det_ne)
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hH2
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have e1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX'
  have hXa : Xᴴ = -(Hpk k r * X * Hpk k r) := by
    calc Xᴴ = Xᴴ * (Hpk k r * Hpk k r) := by rw [hH2, Matrix.mul_one]
      _ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc]
      _ = -(Hpk k r * X * Hpk k r) := by rw [e1, Matrix.neg_mul]
  have hAa : ((t : ℂ) • X)ᴴ = Hpk k r * (-((t : ℂ) • X)) * (Hpk k r)⁻¹ := by
    rw [hinv, Matrix.conjTranspose_smul, hXa, Complex.star_def, Complex.conj_ofReal]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_neg, Matrix.mul_neg, Matrix.neg_mul]
  have hE : (NormedSpace.exp ((t : ℂ) • X))ᴴ =
      Hpk k r * NormedSpace.exp (-((t : ℂ) • X)) * (Hpk k r)⁻¹ := by
    rw [← Matrix.exp_conjTranspose, hAa, Matrix.exp_conj _ _ hU]
  have hN : NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
    have hc : Commute (-((t : ℂ) • X)) ((t : ℂ) • X) := (Commute.refl _).neg_left
    rw [← Matrix.exp_add_of_commute _ _ hc, neg_add_cancel, NormedSpace.exp_zero]
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r
  rw [hE, hinv]
  calc Hpk k r * NormedSpace.exp (-((t : ℂ) • X)) * Hpk k r * Hpk k r * NormedSpace.exp ((t : ℂ) • X)
      = Hpk k r * (NormedSpace.exp (-((t : ℂ) • X)) * (Hpk k r * Hpk k r) *
          NormedSpace.exp ((t : ℂ) • X)) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hH2, Matrix.mul_one, hN, Matrix.mul_one]

section gN

open scoped Matrix.Norms.Frobenius

theorem gN_eq_frob (g : B.Mat k r) : B.gN g = ‖g‖ := by
  rw [Matrix.frobenius_norm_def]
  unfold B.gN
  rw [Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

theorem one_le_gN {g : B.Mat k r} (hg : g ∈ B.GV k r) : 1 ≤ B.gN g := by
  rw [gN_eq_frob]
  have hH : (0 : ℝ) < ‖Hpk k r‖ := norm_pos_iff.mpr hpk_ne_zero
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 : ‖Hpk k r‖ ≤ ‖g‖ * ‖Hpk k r‖ * ‖g‖ := by
    calc ‖Hpk k r‖ = ‖gᴴ * Hpk k r * g‖ := by rw [h1]
      _ ≤ ‖gᴴ * Hpk k r‖ * ‖g‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖gᴴ‖ * ‖Hpk k r‖ * ‖g‖ := by
          gcongr
          exact Matrix.frobenius_norm_mul _ _
      _ = ‖g‖ * ‖Hpk k r‖ * ‖g‖ := by rw [Matrix.frobenius_norm_conjTranspose]
  have h3 : 1 ≤ ‖g‖ * ‖g‖ := by nlinarith
  nlinarith [norm_nonneg g]

end gN

section Deriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simp only [Complex.coe_smul]
  exact this

theorem exp_deriv (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have : HasDerivAt (fun t : ℝ => (fun i j => (NormedSpace.exp ((t : ℂ) • X)) i j : Fin n → Fin n → ℂ))
      (fun i j => X i j) 0 := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry X i j
  exact this

def mulL (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)

def mulR (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ a)

theorem mulL_apply (a x : Matrix (Fin n) (Fin n) ℂ) : mulL a x = a * x := rfl
theorem mulR_apply (a x : Matrix (Fin n) (Fin n) ℂ) : mulR a x = x * a := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def cv : Bool → B.Mat k r → B.Mat k r → ℝ → B.Mat k r
  | true, X, g, t => NormedSpace.exp (-((t : ℂ) • X)) * g
  | false, X, g, t => g * NormedSpace.exp ((t : ℂ) • X)

def vel : Bool → B.Mat k r → B.Mat k r → B.Mat k r
  | true, X, g => -(X * g)
  | false, X, g => g * X

def D : Bool → B.Mat k r → (B.Mat k r → E) → (B.Mat k r → E)
  | true, X, f => B.LdV X f
  | false, X, f => Formalism.REAL.RdV X f

theorem D_eq (b : Bool) (X : B.Mat k r) (f : B.Mat k r → E) (g : B.Mat k r) :
    D b X f g = deriv (fun t : ℝ => f (cv b X g t)) 0 := by
  cases b <;> rfl

theorem cv_zero (b : Bool) (X g : B.Mat k r) : cv b X g 0 = g := by
  cases b <;> simp [cv]

theorem cv_mem {b : Bool} {X g : B.Mat k r} (hg : g ∈ B.GV k r) (hX : B.inLie k r X) (t : ℝ) :
    cv b X g t ∈ B.GV k r := by
  cases b with
  | true =>
    show NormedSpace.exp (-((t : ℂ) • X)) * g ∈ B.GV k r
    rw [← smul_neg]
    exact mul_mem_GV (exp_mem_GV (inLie_neg hX) t) hg
  | false =>
    show g * NormedSpace.exp ((t : ℂ) • X) ∈ B.GV k r
    exact mul_mem_GV hg (exp_mem_GV hX t)

theorem cv_deriv (b : Bool) (X g : B.Mat k r) : HasDerivAt (cv b X g) (vel b X g) 0 := by
  cases b with
  | true =>
    show HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g) (-(X * g)) 0
    have h := (mulR g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (exp_deriv (-X))
    have e1 : (⇑(mulR g) ∘ fun t : ℝ => NormedSpace.exp ((t : ℂ) • -X)) =
        fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g := by
      funext t
      simp only [Function.comp, mulR_apply, smul_neg]
    have e2 : (mulR g) (-X) = -(X * g) := by
      rw [mulR_apply]
      exact neg_mul X g
    rw [e1] at h
    exact h.congr_deriv e2
  | false =>
    show HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0
    have h := (mulL g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (exp_deriv X)
    have e1 : (⇑(mulL g) ∘ fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) =
        fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X) := by
      funext t
      rfl
    rw [e1] at h
    exact h.congr_deriv (mulL_apply g X)

theorem contDiff_vel (b : Bool) (X : B.Mat k r) {m : WithTop ℕ∞} :
    ContDiff ℝ m (fun h : B.Mat k r => vel b X h) := by
  cases b with
  | true =>
    show ContDiff ℝ m (fun h : B.Mat k r => -(X * h))
    exact (mulL X).contDiff.neg
  | false =>
    show ContDiff ℝ m (fun h : B.Mat k r => h * X)
    exact (mulR X).contDiff

theorem vel_sum (b : Bool) {N : ℕ} (c : Fin N → ℝ) (e : Fin N → B.Mat k r) (g : B.Mat k r) :
    vel b (∑ i, c i • e i) g = ∑ i, c i • vel b (e i) g := by
  cases b with
  | true =>
    simp only [vel, Finset.sum_mul, smul_mul_assoc, ← Finset.sum_neg_distrib, smul_neg]
  | false =>
    simp only [vel, Finset.mul_sum, mul_smul_comm]

theorem hasDerivAt_D {b : Bool} {X g : B.Mat k r} {f f' : B.Mat k r → E} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hgU : g ∈ U) (hgG : g ∈ B.GV k r) (hfe : ∀ h ∈ U, h ∈ B.GV k r → f h = f' h)
    (hd : DifferentiableAt ℝ f' g) (hX : B.inLie k r X) :
    HasDerivAt (fun t : ℝ => f (cv b X g t)) (fderiv ℝ f' g (vel b X g)) 0 := by
  have hc := cv_deriv b X g
  have h0 : cv b X g 0 = g := cv_zero b X g
  have hf' : HasFDerivAt f' (fderiv ℝ f' g) (cv b X g 0) := by
    rw [h0]
    exact hd.hasFDerivAt
  have h1 := hf'.comp_hasDerivAt (0 : ℝ) hc
  refine h1.congr_of_eventuallyEq ?_
  have hU' : cv b X g ⁻¹' U ∈ nhds (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU.mem_nhds hgU)
  filter_upwards [hU'] with t ht
  exact hfe _ ht (cv_mem hgG hX t)

theorem D_eq_fderiv {b : Bool} {X g : B.Mat k r} {f f' : B.Mat k r → E} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hgU : g ∈ U) (hgG : g ∈ B.GV k r) (hfe : ∀ h ∈ U, h ∈ B.GV k r → f h = f' h)
    (hd : DifferentiableAt ℝ f' g) (hX : B.inLie k r X) :
    D b X f g = fderiv ℝ f' g (vel b X g) := by
  rw [D_eq]
  exact (hasDerivAt_D hU hgU hgG hfe hd hX).deriv

abbrev SS (k r : ℕ) (f : B.Mat k r → E) : Prop := B.CkOn (⊤ : ℕ∞) (B.GV k r) f

theorem ss_rep {f : B.Mat k r → E} (hf : SS k r f) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    ∃ (U : Set (B.Mat k r)) (f' : B.Mat k r → E), IsOpen U ∧ g ∈ U ∧ DifferentiableAt ℝ f' g ∧
      ∀ h ∈ U, h ∈ B.GV k r → f h = f' h := by
  obtain ⟨U, f', hU, hgU, hcd, hfe⟩ := hf g hg
  exact ⟨U, f', hU, hgU, (hcd.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp), hfe⟩

theorem ss_D {b : Bool} {X : B.Mat k r} {f : B.Mat k r → E} (hf : SS k r f) (hX : B.inLie k r X) :
    SS k r (D b X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, hfe⟩ := hf g₀ hg₀
  refine ⟨U, fun h => fderiv ℝ f' h (vel b X h), hU, hgU, ?_, ?_⟩
  · exact (hcd.fderiv_of_isOpen hU (by simp)).clm_apply (contDiff_vel b X).contDiffOn
  · intro h hU' hG
    exact D_eq_fderiv hU hU' hG hfe
      ((hcd.contDiffAt (hU.mem_nhds hU')).differentiableAt (by simp)) hX

theorem hasDerivAt_D_of {b : Bool} {X g : B.Mat k r} {f : B.Mat k r → E} (hf : SS k r f)
    (hg : g ∈ B.GV k r) (hX : B.inLie k r X) :
    HasDerivAt (fun t : ℝ => f (cv b X g t)) (D b X f g) 0 := by
  obtain ⟨U, f', hU, hgU, hd, hfe⟩ := ss_rep hf hg
  rw [D_eq_fderiv hU hgU hg hfe hd hX]
  exact hasDerivAt_D hU hgU hg hfe hd hX

theorem D_congr {b : Bool} {X g : B.Mat k r} {f₁ f₂ : B.Mat k r → E}
    (h : ∀ y ∈ B.GV k r, f₁ y = f₂ y) (hg : g ∈ B.GV k r) (hX : B.inLie k r X) :
    D b X f₁ g = D b X f₂ g := by
  rw [D_eq, D_eq]
  congr 1
  funext t
  exact h _ (cv_mem hg hX t)

theorem D_add {b : Bool} {X g : B.Mat k r} {f₁ f₂ : B.Mat k r → E} (h₁ : SS k r f₁) (h₂ : SS k r f₂)
    (hg : g ∈ B.GV k r) (hX : B.inLie k r X) :
    D b X (f₁ + f₂) g = D b X f₁ g + D b X f₂ g := by
  rw [D_eq]
  exact ((hasDerivAt_D_of h₁ hg hX).add (hasDerivAt_D_of h₂ hg hX)).deriv

theorem D_smul {b : Bool} {X g : B.Mat k r} (c : ℝ) {f : B.Mat k r → E} (hf : SS k r f)
    (hg : g ∈ B.GV k r) (hX : B.inLie k r X) :
    D b X (c • f) g = c • D b X f g := by
  rw [D_eq]
  exact ((hasDerivAt_D_of hf hg hX).const_smul c).deriv

theorem D_letter {b : Bool} {N : ℕ} {e : Fin N → B.Mat k r} {c : Fin N → ℝ} {X g : B.Mat k r}
    {f : B.Mat k r → E} (hf : SS k r f) (hg : g ∈ B.GV k r) (he : ∀ i, B.inLie k r (e i))
    (hX : B.inLie k r X) (hXe : X = ∑ i, c i • e i) :
    D b X f g = ∑ i, c i • D b (e i) f g := by
  obtain ⟨U, f', hU, hgU, hd, hfe⟩ := ss_rep hf hg
  rw [D_eq_fderiv hU hgU hg hfe hd hX, hXe, vel_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, D_eq_fderiv hU hgU hg hfe hd (he i)]

theorem ss_add {f₁ f₂ : B.Mat k r → E} (h₁ : SS k r f₁) (h₂ : SS k r f₂) : SS k r (f₁ + f₂) := by
  intro g₀ hg₀
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := h₁ g₀ hg₀
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := h₂ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun h => f₁' h + f₂' h, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · exact (hc₁.mono Set.inter_subset_left).add (hc₂.mono Set.inter_subset_right)
  · intro g hg hG
    simp only [Pi.add_apply, he₁ g hg.1 hG, he₂ g hg.2 hG]

theorem ss_smul (c : ℝ) {f : B.Mat k r → E} (hf : SS k r f) : SS k r (c • f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg₀
  refine ⟨U, fun h => c • f' h, hU, hgU, hc.const_smul c, ?_⟩
  intro g hg hG
  simp only [Pi.smul_apply, he g hg hG]

theorem ss_zero : SS k r (0 : B.Mat k r → E) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

end Deriv

end PI.ComplexConjugateDerivative
