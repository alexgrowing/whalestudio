import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma onep_skew {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : Xᴴ = -X := by
  unfold inK inG at hX
  obtain ⟨h1, h2⟩ := hX
  have hJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have h3 : Xᴴ * Jm ε = -(X * Jm ε) := by
    rw [h2]
    exact eq_neg_of_add_eq_zero_left h1
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJ, mul_one]
    _ = -(X * Jm ε) * Jm ε := by rw [h3]
    _ = -X := by rw [neg_mul, mul_assoc, hJ, mul_one]

lemma onep_exp_conjT {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp (-((t : ℂ) • X)) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, onep_skew hX]
  have hs : (star (t : ℂ)) = t := Complex.conj_ofReal t
  rw [hs, smul_neg]

lemma onep_exp_neg_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl A).neg_left)]
  simp

lemma onep_exp_mul_neg (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl A).neg_right)]
  simp

lemma onep_commJ {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    Commute (Jm ε) (NormedSpace.exp ((t : ℂ) • X)) := (Commute.smul_right (show Commute (Jm ε) X from (show inG ε X ∧ X * Jm ε = Jm ε * X from hX).2.symm)
    (t : ℂ)).exp_right

lemma onep_inUJ {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
  unfold inUJ
  rw [onep_exp_conjT hX t, mul_assoc, (onep_commJ hX t).eq, ← mul_assoc, onep_exp_neg_mul, one_mul]

lemma onep_Kset {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
  unfold Kset
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, (onep_commJ hX t).eq.symm⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, onep_exp_conjT hX t, onep_exp_mul_neg]

def onepCurve (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) : KG ε :=
  ⟨⟨(Matrix.isUnit_exp ((t : ℂ) • X)).unit, by
      show inUJ ε ((Matrix.isUnit_exp ((t : ℂ) • X)).unit : Matrix (Fin n) (Fin n) ℂ)
      rw [IsUnit.unit_spec]
      exact onep_inUJ hX t⟩, by
    show ((Matrix.isUnit_exp ((t : ℂ) • X)).unit : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε
    rw [IsUnit.unit_spec]
    exact onep_Kset hX t⟩

lemma toMK_onepCurve (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    toMK (onepCurve ε hX t) = NormedSpace.exp ((t : ℂ) • X) :=
  IsUnit.unit_spec _

theorem exists_curve (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    ∃ γ : ℝ → KG ε, ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X) := ⟨onepCurve ε hX, toMK_onepCurve ε hX⟩

lemma onep_KG_ext {ε : Fin n → Bool} {g h : KG ε} (hgh : toMK g = toMK h) : g = h := by
  unfold toMK at hgh
  first
    | exact Subtype.ext (Subtype.ext hgh)
    | exact Subtype.ext (Subtype.ext (Units.ext hgh))
    | (unfold toM at hgh; done)

theorem KType.op_curve {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    T.op (γ t) = NormedSpace.exp ((t : ℂ) • T.dτ X) := by
  set A := T.dτ X with hAdef
  set F : ℝ → T.V →L[ℂ] T.V := fun s => T.op (γ s) with hFdef
  have hmul : ∀ s u : ℝ, γ (s + u) = γ s * γ u := by
    intro s u
    apply onep_KG_ext
    show toMK (γ (s + u)) = toMK (γ s) * toMK (γ u)
    rw [hγ, hγ, hγ, show (((s + u : ℝ) : ℂ) • X) = (s : ℂ) • X + (u : ℂ) • X by push_cast; exact add_smul _ _ _]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have h0 : γ 0 = 1 := by
    apply onep_KG_ext
    rw [hγ]
    show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
    simp
  have hF : ∀ s u : ℝ, F (s + u) = F s * F u := by
    intro s u
    simp only [hFdef, KType.op, hmul, map_mul]
    rfl
  have hF0 : F 0 = 1 := by
    simp only [hFdef, KType.op, h0, map_one]
    rfl
  have hd0 : HasDerivAt F A 0 := T.hasDeriv X hX γ hγ
  have hd : ∀ s, HasDerivAt F (F s * A) s := by
    intro s
    have h1 : HasDerivAt (fun u => F s * F (u - s)) (F s * A) s := by
      have h2 := hd0.const_mul (F s)
      rw [← sub_self s] at h2
      exact HasDerivAt.comp_sub_const (f := fun y => F s * F y) s s h2
    convert h1 using 1
    funext u
    rw [← hF, add_sub_cancel]
  set E : ℝ → T.V →L[ℂ] T.V := fun u => NormedSpace.exp (u • (-A)) with hEdef
  have hE : ∀ u, HasDerivAt E (E u * (-A)) u := fun u => hasDerivAt_exp_smul_const (-A) u
  have hcomm : ∀ u, A * E u = E u * A := fun u =>
    (((Commute.refl A).neg_right.smul_right u).exp_right).eq
  have hG : ∀ u, HasDerivAt (F * E) 0 u := by
    intro u
    refine ((hd u).mul (hE u)).congr_deriv ?_
    simp only [mul_neg, mul_assoc, hcomm u, add_neg_cancel]
  have hGc : ∀ u, (F * E) u = (F * E) 0 := fun u =>
    is_const_of_deriv_eq_zero (fun v => (hG v).differentiableAt) (fun v => (hG v).deriv) u 0
  have hG0 : (F * E) 0 = 1 := by
    show F 0 * NormedSpace.exp ((0 : ℝ) • (-A)) = 1
    rw [hF0, zero_smul, NormedSpace.exp_zero, one_mul]
  show F t = _
  have hs : ((t : ℂ) • A) = t • A := by
    exact Complex.coe_smul t A
  rw [hs]
  have hc : Commute (t • (-A)) (t • A) := (((Commute.refl A).neg_left).smul_left t).smul_right t
  calc F t = F t * E t * NormedSpace.exp (t • A) := by
        rw [mul_assoc, hEdef, ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc
          ((NormedSpace.expSeries_radius_eq_top ℝ (T.V →L[ℂ] T.V)).symm ▸ edist_lt_top _ _)
          ((NormedSpace.expSeries_radius_eq_top ℝ (T.V →L[ℂ] T.V)).symm ▸ edist_lt_top _ _), smul_neg, neg_add_cancel,
          NormedSpace.exp_zero, mul_one]
    _ = NormedSpace.exp (t • A) := by
        rw [show F t * E t = (F * E) t from rfl, hGc, hG0, one_mul]

end ReciprocityTheory.ChartRestriction.DS.HW
