import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothModule

variable {n : ℕ} {ε : Fin n → Bool}

theorem J_mul_J (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext a; split_ifs <;> simp

theorem J_conj (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp

theorem J_J_mul (X : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * X) = X := by
  rw [← Matrix.mul_assoc, J_mul_J, Matrix.one_mul]

theorem inG_iff {X : Matrix (Fin n) (Fin n) ℂ} : inG ε X ↔ thetaJ ε X = X := by
  change Xᴴ * Jm ε + Jm ε * X = 0 ↔ _
  unfold thetaJ
  constructor
  · intro h
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h, Matrix.mul_neg, neg_neg, J_J_mul]
  · intro h
    have : Jm ε * X = -(Xᴴ * Jm ε) := by
      conv_lhs => rw [← h]
      rw [Matrix.mul_neg, Matrix.mul_assoc, J_J_mul]
    rw [this, add_neg_cancel]

theorem theta_add (X Y : Matrix (Fin n) (Fin n) ℂ) : thetaJ ε (X + Y) = thetaJ ε X + thetaJ ε Y := by
  simp only [thetaJ, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, neg_add]

theorem theta_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : thetaJ ε (X - Y) = thetaJ ε X - thetaJ ε Y := by
  simp only [thetaJ, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]; abel

theorem theta_smul (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    thetaJ ε (c • X) = (starRingEnd ℂ c) • thetaJ ε X := by
  simp only [thetaJ, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]; rfl

theorem theta_theta (X : Matrix (Fin n) (Fin n) ℂ) : thetaJ ε (thetaJ ε X) = X := by
  simp only [thetaJ, conjTranspose_neg, conjTranspose_mul, J_conj, conjTranspose_conjTranspose,
    Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, J_J_mul, J_mul_J, Matrix.mul_one]

theorem theta_mul (X Y : Matrix (Fin n) (Fin n) ℂ) : thetaJ ε (X * Y) = -(thetaJ ε Y * thetaJ ε X) := by
  simp only [thetaJ, conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, J_J_mul]

theorem theta_single (a b : Fin n) :
    thetaJ ε (single a b 1) = (-(Formalism.REAL.sgn ε a b : ℂ)) • single b a 1 := by
  ext i j
  simp only [thetaJ, Jm, conjTranspose_single, Matrix.neg_apply, mul_diagonal, diagonal_mul, Matrix.smul_apply,
    Formalism.REAL.sgn, single_apply]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ε a <;> cases ε b <;> simp
  · simp [h]

theorem inG_add {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) : inG ε (X + Y) := by
  rw [inG_iff] at *; rw [theta_add, hX, hY]

theorem inG_smul (s : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : inG ε ((s : ℂ) • X) := by
  rw [inG_iff] at *; rw [theta_smul, hX, Complex.conj_ofReal]

theorem inG_comm {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    inG ε (X * Y - Y * X) := by
  rw [inG_iff] at *; rw [theta_sub, theta_mul, theta_mul, hX, hY]; abel

def re (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Y + thetaJ ε Y)

def im (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I)) • (Y - thetaJ ε Y)

theorem inv_two_I : (1 / (2 * Complex.I) : ℂ) = -(1 / 2) * Complex.I := by
  have := Complex.I_ne_zero
  field_simp
  simp

theorem inG_re (Y : Matrix (Fin n) (Fin n) ℂ) : inG ε (re ε Y) := by
  rw [inG_iff, re, theta_smul, theta_add, theta_theta, add_comm]
  congr 1
  simp [Complex.conj_ofNat]

theorem inG_im (Y : Matrix (Fin n) (Fin n) ℂ) : inG ε (im ε Y) := by
  rw [inG_iff, im, theta_smul, theta_sub, theta_theta, ← neg_sub Y, smul_neg, ← neg_smul, inv_two_I]
  congr 1
  simp [Complex.conj_ofNat]

theorem re_add_im (Y : Matrix (Fin n) (Fin n) ℂ) : re ε Y + Complex.I • im ε Y = Y := by
  rw [re, im, inv_two_I, smul_smul]
  have : Complex.I * (-(1 / 2) * Complex.I) = 1 / 2 := by
    linear_combination (-(1 / 2) : ℂ) * Complex.I_mul_I
  rw [this]; module

theorem theta_pair {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    thetaJ ε (A + Complex.I • B) = A - Complex.I • B := by
  rw [theta_add, theta_smul, inG_iff.1 hA, inG_iff.1 hB, Complex.conj_I, neg_smul, sub_eq_add_neg]

theorem re_pair {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    re ε (A + Complex.I • B) = A := by
  rw [re, theta_pair hA hB]; module

theorem im_pair {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    im ε (A + Complex.I • B) = B := by
  rw [im, theta_pair hA hB, inv_two_I]
  have h : A + Complex.I • B - (A - Complex.I • B) = (2 * Complex.I) • B := by module
  have : (-(1 / 2) * Complex.I) * (2 * Complex.I) = 1 := by
    linear_combination (-1 : ℂ) * Complex.I_mul_I
  rw [h, smul_smul, this, one_smul]

theorem UJ_left_inv {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : Jm ε * gᴴ * Jm ε * g = 1 := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, J_mul_J]

theorem UJ_inv {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : g⁻¹ = Jm ε * gᴴ * Jm ε :=
  inv_eq_left_inv (UJ_left_inv hg)

theorem UJ_isUnit {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : IsUnit g :=
  (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_det_of_left_inverse (UJ_left_inv hg))

theorem UJ_inv_mem {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : g⁻¹ ∈ UJset ε := by
  change (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε
  have h := mul_eq_one_comm.1 (UJ_left_inv hg)
  rw [UJ_inv hg]
  simp only [conjTranspose_mul, J_conj, conjTranspose_conjTranspose, Matrix.mul_assoc, J_J_mul] at h ⊢
  rw [h, Matrix.mul_one]

theorem UJ_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  have h1 : gᴴ * Jm ε * g = Jm ε := hg
  have h2 : hᴴ * Jm ε * h = Jm ε := hh
  change (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, h2]

theorem inG_conj {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hX : inG ε X) :
    inG ε (g * X * g⁻¹) := by
  rw [inG_iff] at *
  conv_rhs => rw [← hX]
  rw [UJ_inv hg]
  simp only [thetaJ, conjTranspose_mul, J_conj, conjTranspose_conjTranspose, Matrix.mul_assoc, J_J_mul,
    Matrix.mul_neg, Matrix.neg_mul]

theorem exp_mem {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : NormedSpace.exp X ∈ UJset ε := by
  change (NormedSpace.exp X)ᴴ * Jm ε * NormedSpace.exp X = Jm ε
  have hu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, J_mul_J ε, J_mul_J ε⟩, rfl⟩
  have hinv : (Jm ε)⁻¹ = Jm ε := inv_eq_left_inv (J_mul_J ε)
  have h1 : Xᴴ = Jm ε * (-X) * (Jm ε)⁻¹ := by
    conv_rhs => rw [← inG_iff.1 hX]
    rw [hinv]
    simp only [thetaJ, neg_neg, Matrix.mul_assoc, J_J_mul, J_mul_J, Matrix.mul_one]
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hu, hinv, Matrix.exp_neg, Matrix.mul_assoc _ (Jm ε) (Jm ε),
    J_mul_J, Matrix.mul_one, Matrix.mul_assoc,
    nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp X)), Matrix.mul_one]

theorem conj_single (g h : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    g * single a b 1 * h = ∑ c, ∑ d, (g c a * h b d) • single c d (1 : ℂ) := by
  conv_lhs => rw [matrix_eq_sum_single (g * single a b 1 * h)]
  refine sum_congr rfl fun c _ => sum_congr rfl fun d _ => ?_
  rw [smul_single, smul_eq_mul, mul_one]
  congr 1
  simp [Matrix.mul_apply, single_apply, ite_and]

def cext {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool) (d : Matrix (Fin n) (Fin n) ℂ → M)
    (hadd : ∀ X Y, inG ε X → inG ε Y → d (X + Y) = d X + d Y)
    (hsmul : ∀ (s : ℝ) X, inG ε X → d ((s : ℂ) • X) = (s : ℂ) • d X) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M where
  toFun Y := d (re ε Y) + Complex.I • d (im ε Y)
  map_add' Y Z := by
    have h1 : re ε (Y + Z) = re ε Y + re ε Z := by simp only [re, theta_add]; module
    have h2 : im ε (Y + Z) = im ε Y + im ε Z := by simp only [im, theta_add]; module
    rw [h1, h2, hadd _ _ (inG_re _) (inG_re _), hadd _ _ (inG_im _) (inG_im _)]
    module
  map_smul' c Y := by
    have hA := inG_re (ε := ε) Y
    have hB := inG_im (ε := ε) Y
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    have hI : ∀ {N : Type _} [AddCommGroup N] [Module ℂ N] (a b : N), c • (a + Complex.I • b) =
        ((c.re : ℂ) • a + ((-c.im : ℝ) : ℂ) • b) + Complex.I • ((c.im : ℂ) • a + (c.re : ℂ) • b) := by
      intro N _ _ a b
      conv_lhs => rw [hc]
      push_cast
      match_scalars
      · ring
      · linear_combination (c.im : ℂ) * Complex.I_mul_I
    have h : c • Y = ((c.re : ℂ) • re ε Y + ((-c.im : ℝ) : ℂ) • im ε Y) +
        Complex.I • ((c.im : ℂ) • re ε Y + (c.re : ℂ) • im ε Y) := by
      conv_lhs => rw [← re_add_im (ε := ε) Y, hc]
      push_cast
      match_scalars
      · ring
      · linear_combination (c.im : ℂ) * Complex.I_mul_I
    have h1 := inG_add (inG_smul c.re hA) (inG_smul (-c.im) hB)
    have h2 := inG_add (inG_smul c.im hA) (inG_smul c.re hB)
    rw [h, re_pair h1 h2, im_pair h1 h2, hadd _ _ (inG_smul _ hA) (inG_smul _ hB),
      hadd _ _ (inG_smul _ hA) (inG_smul _ hB), hsmul _ _ hA, hsmul _ _ hA, hsmul _ _ hB, hsmul _ _ hB,
      RingHom.id_apply, hI]

theorem cext_apply {M : Type*} [AddCommGroup M] [Module ℂ M] (d : Matrix (Fin n) (Fin n) ℂ → M)
    (hadd : ∀ X Y, inG ε X → inG ε Y → d (X + Y) = d X + d Y)
    (hsmul : ∀ (s : ℝ) X, inG ε X → d ((s : ℂ) • X) = (s : ℂ) • d X) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cext ε d hadd hsmul Y = d (re ε Y) + Complex.I • d (im ε Y) := rfl

theorem cext_of_inG {M : Type*} [AddCommGroup M] [Module ℂ M] (d : Matrix (Fin n) (Fin n) ℂ → M)
    (hadd : ∀ X Y, inG ε X → inG ε Y → d (X + Y) = d X + d Y)
    (hsmul : ∀ (s : ℝ) X, inG ε X → d ((s : ℂ) • X) = (s : ℂ) • d X) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) : cext ε d hadd hsmul X = d X := by
  have h0 : d 0 = 0 := by simpa using hsmul 0 X hX
  have h1 : re ε X = X := by rw [re, inG_iff.1 hX]; module
  have h2 : im ε X = 0 := by rw [im, inG_iff.1 hX, sub_self, smul_zero]
  rw [cext_apply, h1, h2, h0, smul_zero, add_zero]

theorem bracket_ext {R : Type*} [Ring R] [Algebra ℂ R] (C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] R)
    (h : ∀ X Y, inG ε X → inG ε Y → C X * C Y - C Y * C X = C (X * Y - Y * X))
    (Y Z : Matrix (Fin n) (Fin n) ℂ) : C Y * C Z - C Z * C Y = C (Y * Z - Z * Y) := by
  rw [← re_add_im (ε := ε) Y, ← re_add_im (ε := ε) Z]
  have h1 := h _ _ (inG_re Y) (inG_re Z)
  have h2 := h _ _ (inG_re Y) (inG_im Z)
  have h3 := h _ _ (inG_im Y) (inG_re Z)
  have h4 := h _ _ (inG_im Y) (inG_im Z)
  simp only [map_sub, map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm] at *
  linear_combination (norm := module) h1 + Complex.I • h2 + Complex.I • h3 +
    Complex.I • Complex.I • h4

theorem glRel_of_bracket {R : Type*} [Ring R] [Algebra ℂ R] (C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] R)
    (h : ∀ Y Z, C Y * C Z - C Z * C Y = C (Y * Z - Z * Y)) :
    Formalism.REAL.GlRel fun a b => C (single a b 1) := by
  intro a b c d
  have key : ∀ a b c d : Fin n, C (single a b 1 * single c d 1) = if b = c then C (single a d 1) else 0 := by
    intro a b c d
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, map_zero]
  rw [h, map_sub, key, key]

theorem adj_ext {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ V)
    (h : ∀ X, inG ε X → ∀ x y, ⟪C X x, y⟫_ℂ = -⟪x, C X y⟫_ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) (x y : V) :
    ⟪C Y x, y⟫_ℂ = -⟪x, C (thetaJ ε Y) y⟫_ℂ := by
  rw [← re_add_im (ε := ε) Y, theta_pair (inG_re Y) (inG_im Y)]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right, h _ (inG_re Y), h _ (inG_im Y),
    Complex.conj_I]
  ring

section Analytic

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem inner_rep (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (v w : H) :
    ⟪σ g v, σ g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  (⟨(σ g : H →ₗ[ℂ] H), hσ.2.1 g hg⟩ : H →ₗᵢ[ℂ] H).inner_map_map v w

theorem skew (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v w v' w' : H}
    (hv : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0)
    (hw : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) w) w' 0) :
    ⟪v', w⟫_ℂ = -⟪v, w'⟫_ℂ := by
  have h := HasDerivAt.inner ℂ hv hw
  simp only [inner_rep hσ (exp_mem (inG_smul _ hX)), Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero,
    hσ.1.1, one_apply_eq_self] at h
  have := h.unique (hasDerivAt_const _ _)
  linear_combination this

theorem conj_deriv (hσ : IsURepOn (UJset ε) σ) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (hg : g ∈ UJset ε) {v v' : H}
    (hv : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g v)) (σ g v') 0 := by
  have h := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hv
  refine HasDerivAt.congr_of_eventuallyEq h (Filter.Eventually.of_forall fun t => ?_)
  have he := exp_mem (inG_smul t hX)
  have h1 : (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have h2 := hσ.1.2 _ (UJ_mul (UJ_mul hg he) (UJ_inv_mem hg)) g hg
  rw [Matrix.mul_assoc _ g⁻¹ g, nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (UJ_isUnit hg)),
    Matrix.mul_one, hσ.1.2 _ hg _ he] at h2
  beta_reduce
  rw [h1, Matrix.exp_conj _ _ (UJ_isUnit hg)]
  exact (congrArg (fun T : H →L[ℂ] H => T v) h2).symm

end Analytic

theorem smMod (hL : CompanionTheory.D.DSIC.SmLin) (hB : CompanionTheory.D.DSIC.SmBracket) : CompanionTheory.D.DSIC.SmMod := by
  classical
  intro n ε H _ _ σ hσ
  obtain ⟨h0, hadd, hsm, hst, hd, hlin⟩ := hL n ε H σ hσ
  have hbr := hB n ε H σ hσ
  let S : Submodule ℂ H :=
    { carrier := smoothVecs (Jm ε) σ
      add_mem' := fun {a b} ha hb => hadd a ha b hb
      zero_mem' := h0
      smul_mem' := fun c {x} hx => hsm c x hx }
  let D : ∀ X, inG ε X → Module.End ℂ S := fun X hX =>
    { toFun := fun v => ⟨dsig σ X v, (hd X hX v v.2).1⟩
      map_add' := fun v w => Subtype.ext <| by
        have h1 := (hd X hX _ (v + w).2).2
        simp only [Submodule.coe_add, map_add] at h1
        exact h1.unique ((hd X hX v v.2).2.add (hd X hX w w.2).2)
      map_smul' := fun c v => Subtype.ext <| by
        have h1 := (hd X hX _ (c • v).2).2
        simp only [Submodule.coe_smul, map_smul] at h1
        exact h1.unique ((hd X hX v v.2).2.const_smul c) }
  let d : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ S := fun X => if hX : inG ε X then D X hX else 0
  have hdv : ∀ X, inG ε X → ∀ v : S, (d X v : H) = dsig σ X v := by
    intro X hX v
    simp only [d, dif_pos hX]
    rfl
  have dadd : ∀ X Y, inG ε X → inG ε Y → d (X + Y) = d X + d Y := by
    intro X Y hX hY
    ext v
    rw [LinearMap.add_apply, Submodule.coe_add, hdv _ (inG_add hX hY), hdv _ hX, hdv _ hY]
    exact (hlin X Y hX hY v v.2).1
  have dsmul : ∀ (s : ℝ) X, inG ε X → d ((s : ℂ) • X) = (s : ℂ) • d X := by
    intro s X hX
    ext v
    rw [LinearMap.smul_apply, Submodule.coe_smul, hdv _ (inG_smul s hX), hdv _ hX]
    exact (hlin X X hX hX v v.2).2 s
  obtain ⟨C, hC, hCX⟩ : ∃ C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ S,
      (∀ Y (v : S), (C Y v : H) = dsigC ε σ Y v) ∧ ∀ X, inG ε X → ∀ v : S, (C X v : H) = dsig σ X v := by
    refine ⟨cext ε d dadd dsmul, fun Y v => ?_, fun X hX v => ?_⟩
    · rw [cext_apply, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
        hdv _ (inG_re Y), hdv _ (inG_im Y)]
      rfl
    · rw [cext_of_inG _ _ _ hX, hdv _ hX]
  have hder : ∀ X, inG ε X → ∀ v : S,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (C X v : H) 0 := by
    intro X hX v
    rw [hCX X hX]
    exact (hd X hX v v.2).2
  refine ⟨S, fun a b => C (single a b 1), fun v => Iff.rfl, fun a b v => hC _ v, fun X hX v => ?_, ?_, ?_,
    hst, ?_⟩
  · have h : X = ∑ a, ∑ b, X a b • single a b (1 : ℂ) := by
      simp only [smul_single, smul_eq_mul, mul_one]
      exact matrix_eq_sum_single X
    have h2 : (C X v : H) = ∑ a, ∑ b, X a b • (C (single a b 1) v : H) := by
      conv_lhs => rw [h]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
        Submodule.coe_smul]
    rw [← h2]
    exact hder X hX v
  · refine glRel_of_bracket C (bracket_ext (ε := ε) C fun X Y hX hY => ?_)
    ext v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hCX _ hX, hCX _ hY,
      hCX _ (inG_comm hX hY)]
    exact hbr X Y hX hY v v.2
  · intro a b x y
    rw [adj_ext (ε := ε) C (fun X hX x y => skew hσ hX (hder X hX x) (hder X hX y)), theta_single]
    simp only [map_smul, LinearMap.smul_apply, inner_smul_right]
    ring
  · intro g hg a b v w hw
    have h1 : ∀ X, inG ε X → σ g (C X v) = C (g * X * g⁻¹) w := by
      intro X hX
      have h := hder _ (inG_conj hg hX) w
      rw [hw] at h
      exact (conj_deriv hσ hX hg (hder X hX v)).unique h
    have h2 : ∀ Y, σ g (C Y v) = C (g * Y * g⁻¹) w := by
      intro Y
      rw [← re_add_im (ε := ε) Y]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
        h1 _ (inG_re Y), h1 _ (inG_im Y)]
    rw [h2, conj_single]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
      Submodule.coe_smul]

end GlobalTheory.CompanionTheory.SmoothModule
