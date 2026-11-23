import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace TDAux

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem inv_eq {x : Mat k r} (hx : Formalism.REAL.inUJ ε x) : x⁻¹ = Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε :=
  Matrix.inv_eq_left_inv (Formalism.REAL.indefinite_unitary_inv_closed _ ε x hx).2

theorem mul_inv_self' {x : Mat k r} (hx : Formalism.REAL.inUJ ε x) : x * x⁻¹ = 1 := by
  rw [inv_eq hx]; exact (Formalism.REAL.indefinite_unitary_inv_closed _ ε x hx).1

theorem inv_mem {x : Mat k r} (hx : Formalism.REAL.inUJ ε x) : Formalism.REAL.inUJ ε x⁻¹ := by
  have hxx := mul_inv_self' hx
  unfold Formalism.REAL.inUJ at hx ⊢
  calc (x⁻¹)ᴴ * Formalism.REAL.Jm ε * x⁻¹ = (x⁻¹)ᴴ * (xᴴ * Formalism.REAL.Jm ε * x) * x⁻¹ := by rw [hx]
    _ = (x * x⁻¹)ᴴ * Formalism.REAL.Jm ε * (x * x⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hxx]; simp

theorem actM_add {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M)
    (X Y : Mat k r) : actM E (X + Y) = actM E X + actM E Y := by
  simp only [actM, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem actM_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M)
    (c : ℂ) (X : Mat k r) : actM E (c • X) = c • actM E X := by
  simp only [actM, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem actM_single {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M)
    (a b : Fin (2 * r + k + 1)) : actM E (Matrix.single a b (1 : ℂ)) = E a b := by
  classical
  simp only [actM, Matrix.single_apply]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb; simp [Ne.symm hb]
    · simp
  · intro a' _ ha; simp [Ne.symm ha]
  · simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem coefX_add_smul (σ : Mat k r → (H →L[ℂ] H)) (x₀ : Mat k r) (w m₁ m₂ : H) (c : ℂ) (g : Mat k r) :
    coefX σ x₀ w (m₁ + c • m₂) g = coefX σ x₀ w m₁ g + c * coefX σ x₀ w m₂ g := by
  simp only [coefX, map_add, map_smul, inner_add_right, inner_smul_right]

theorem coefX_sub (σ : Mat k r → (H →L[ℂ] H)) (x₀ : Mat k r) (w m₁ m₂ : H) (g : Mat k r) :
    coefX σ x₀ w (m₁ - m₂) g = coefX σ x₀ w m₁ g - coefX σ x₀ w m₂ g := by
  simp only [coefX, map_sub, inner_sub_right]

end TDAux

namespace TDAux
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem coefX_hasDeriv {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hE : IsDerivedOn ε σ D E) {x₀ g X : Mat k r}
    (hx₀ : Formalism.REAL.inUJ ε x₀) (hg : Formalism.REAL.inUJ ε g) (hX : Formalism.REAL.inG ε X) (w : H) (m : D) :
    HasDerivAt (fun t : ℝ => coefX σ x₀ w (m : H) (g * NormedSpace.exp ((t : ℂ) • X)))
      (coefX σ x₀ w ((actM E X m : D) : H) g) 0 := by
  have hy : Formalism.REAL.inUJ ε (x₀⁻¹ * g) := Formalism.REAL.indefinite_unitary_mul_mem ε (inv_mem hx₀) hg
  have he : ∀ t : ℝ, σ (x₀⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X))) =
      (σ (x₀⁻¹ * g)).comp (σ (NormedSpace.exp ((t : ℂ) • X))) := by
    intro t
    rw [← Matrix.mul_assoc]
    exact hσ.1.2 _ hy _ (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX t)
  have hd := hE.deriv X hX m
  set Lm : H →L[ℂ] ℂ := (innerSL ℂ w).comp (σ (x₀⁻¹ * g)) with hLm
  have h2 := (Lm.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have e : (fun t : ℝ => coefX σ x₀ w (m : H) (g * NormedSpace.exp ((t : ℂ) • X))) =
      (⇑(Lm.restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (m : H)) := by
    funext t
    simp only [coefX, Function.comp_apply, he t, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.comp_apply, hLm, innerSL_apply_apply]
  have e2 : coefX σ x₀ w ((actM E X m : D) : H) g = (Lm.restrictScalars ℝ) ((actM E X m : D) : H) := by
    simp only [coefX, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply, hLm,
      innerSL_apply_apply]
  rw [e, e2]
  exact h2

theorem coefX_Eab {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hE : IsDerivedOn ε σ D E) {x₀ g : Mat k r}
    (hx₀ : Formalism.REAL.inUJ ε x₀) (hg : Formalism.REAL.inUJ ε g) (w : H) (m : D) (a b : Fin (2 * r + k + 1)) :
    Formalism.REAL.Eab ε a b (coefX σ x₀ w (m : H)) g = coefX σ x₀ w ((E a b m : D) : H) g := by
  rw [Formalism.REAL.lie_derivative_def]
  unfold Formalism.REAL.Rd
  rw [(coefX_hasDeriv hσ hE hx₀ hg (Formalism.REAL.real_part_single_mem ε a b) w m).deriv,
    (coefX_hasDeriv hσ hE hx₀ hg (Formalism.REAL.imaginary_part_single_mem ε a b) w m).deriv, ← coefX_add_smul]
  congr 1
  have hZ := (Formalism.REAL.complex_parts_mem_lie_algebra_holds _ ε (Matrix.single a b (1 : ℂ))).2.2.1
  conv_rhs => rw [← actM_single E a b, hZ, actM_add, actM_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul]

end TDAux

namespace TDAux

section Words
variable {n : ℕ} {ε : Fin n → Bool}

theorem eword_congr {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (e : ∀ x, Formalism.REAL.inUJ ε x → f x = h x) :
    ∀ (wd : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε wd f g = Formalism.REAL.Eword ε wd h g
  | [], g, hg => e g hg
  | p :: wd, _, hg => Formalism.REAL.lie_derivative_congr p.1 p.2 (fun x hx => eword_congr e wd x hx) hg

theorem rd_left (X x : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Rd X (fun y => F (x * y)) g = Formalism.REAL.Rd X F (x * g) := by
  simp only [Formalism.REAL.Rd, Matrix.mul_assoc]

theorem eab_left (a b : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Formalism.REAL.Eab ε a b (fun y => F (x * y)) = fun g => Formalism.REAL.Eab ε a b F (x * g) := by
  funext g
  simp only [Formalism.REAL.Eab, Formalism.REAL.Ec, rd_left]

theorem eword_left (x : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    ∀ wd : List (Fin n × Fin n),
      Formalism.REAL.Eword ε wd (fun y => F (x * y)) = fun g => Formalism.REAL.Eword ε wd F (x * g)
  | [] => rfl
  | p :: wd => by
      simp only [Formalism.REAL.Eword]
      rw [eword_left x F wd]
      exact eab_left p.1 p.2 x _

def Ewd {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    List (Fin n × Fin n) → M → M
  | [] => id
  | p :: w => fun m => E p.1 p.2 (Ewd E w m)

end Words

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem coefX_Eword {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hE : IsDerivedOn ε σ D E) {x₀ : Mat k r}
    (hx₀ : Formalism.REAL.inUJ ε x₀) (w : H) (m : D) :
    ∀ (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (g : Mat k r), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε wd (coefX σ x₀ w (m : H)) g = coefX σ x₀ w ((Ewd E wd m : D) : H) g
  | [], _, _ => rfl
  | p :: wd, g, hg => by
      show Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε wd (coefX σ x₀ w (m : H))) g = _
      rw [Formalism.REAL.lie_derivative_congr p.1 p.2 (fun x hx => coefX_Eword hσ hE hx₀ w m wd x hx) hg]
      exact coefX_Eab hσ hE hx₀ hg w _ p.1 p.2

theorem jX {g X : Mat k r} (hX : Formalism.REAL.inG ε X) :
    Formalism.REAL.Jm ε * (g * X)ᴴ * Formalism.REAL.Jm ε = -(X * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε)) := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  have h2 : Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε = -X := by
    rw [Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  calc Formalism.REAL.Jm ε * (g * X)ᴴ * Formalism.REAL.Jm ε =
        (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJ, Matrix.one_mul]
    _ = _ := by rw [h2, Matrix.neg_mul]

def cL (ε : Fin (2 * r + k + 1) → Bool) (x₁ β : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : ℂ :=
  β ⬝ᵥ ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ x₁)

theorem cJd_eq (x₁ β : Fin (2 * r + k + 1) → ℂ) {g : Mat k r} (hg : Formalism.REAL.inUJ ε g) :
    cJd x₁ β g = cL ε x₁ β g := by
  rw [cJd, cL, inv_eq hg]

def cLlin (ε : Fin (2 * r + k + 1) → Bool) (x₁ β : Fin (2 * r + k + 1) → ℂ) : Mat k r →ₗ[ℝ] ℂ where
  toFun := cL ε x₁ β
  map_add' g h := by
    simp only [cL, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec,
      dotProduct_add]
  map_smul' c g := by
    simp only [cL, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mulVec, dotProduct_smul, RingHom.id_apply]

end TDAux

namespace TDAux

section Smooth
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

def cLclm (ε : Fin (2 * r + k + 1) → Bool) (x₁ β : Fin (2 * r + k + 1) → ℂ) : Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (cLlin ε x₁ β)

theorem cLclm_apply (x₁ β : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : cLclm ε x₁ β g = cL ε x₁ β g := rfl

theorem cJd_smooth (x₁ β : Fin (2 * r + k + 1) → ℂ) : Formalism.REAL.SmoothOnG ε (cJd x₁ β) := by
  intro g₀ _
  refine ⟨Set.univ, cLclm ε x₁ β, isOpen_univ, trivial, (cLclm ε x₁ β).contDiff.contDiffOn, ?_⟩
  intro g _ hg
  rw [cLclm_apply]
  exact cJd_eq x₁ β hg

theorem cJd_hasDeriv (x₁ β : Fin (2 * r + k + 1) → ℂ) {g X : Mat k r} (hg : Formalism.REAL.inUJ ε g)
    (hX : Formalism.REAL.inG ε X) :
    HasDerivAt (fun t : ℝ => cJd x₁ β (g * NormedSpace.exp ((t : ℂ) • X)))
      (-(β ⬝ᵥ (X *ᵥ ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ x₁)))) 0 := by
  have h1 := (cLclm ε x₁ β).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X)
  have e : (fun t : ℝ => cJd x₁ β (g * NormedSpace.exp ((t : ℂ) • X))) =
      (⇑(cLclm ε x₁ β) ∘ fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [Function.comp_apply, cLclm_apply]
    exact cJd_eq x₁ β (Formalism.REAL.curve_mem_indefinite_unitary hg hX t)
  have e2 : cLclm ε x₁ β (g * X) = -(β ⬝ᵥ (X *ᵥ ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ x₁))) := by
    rw [cLclm_apply, cL, jX hX, Matrix.neg_mulVec, dotProduct_neg, Matrix.mulVec_mulVec]
  rw [e, ← e2]
  exact h1

theorem smooth_left {F : Mat k r → ℂ} (hF : Formalism.REAL.SmoothOnG ε F) {x : Mat k r}
    (hx : Formalism.REAL.inUJ ε x) : Formalism.REAL.SmoothOnG ε (fun y => F (x * y)) := by
  intro g₀ hg₀
  obtain ⟨U, G, hU, hgU, hG, hFG⟩ := hF (x * g₀) (Formalism.REAL.indefinite_unitary_mul_mem ε hx hg₀)
  set Lx : Mat k r →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x) with hLx
  have hLxa : ∀ y, Lx y = x * y := fun y => rfl
  refine ⟨Lx ⁻¹' U, fun y => G (Lx y), hU.preimage Lx.continuous, by simpa [hLxa] using hgU,
    hG.comp Lx.contDiff.contDiffOn (fun y hy => hy), ?_⟩
  intro g hg hgJ
  simp only [hLxa]
  exact hFG _ (by simpa [hLxa] using hg) (Formalism.REAL.indefinite_unitary_mul_mem ε hx hgJ)

theorem psi_smooth {lam : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ)
    (hμ : S7.IsMu lam μ) (u₁ u₂ : T.V) :
    Formalism.REAL.SmoothOnG ε (fun y => ⟪u₂, S7.PsiM T μ y u₁⟫_ℂ) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hPF⟩ := S7.psiM_smooth T μ hμ g₀ hg₀
  set Φ : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := (innerSL ℂ u₂).comp (ContinuousLinearMap.apply ℂ T.V u₁) with hΦ
  refine ⟨U, fun y => Φ (F y), hU, hgU, (Φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
  intro g hg hgJ
  simp only [hΦ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply]
  rw [hPF g hg hgJ]

end Smooth

end TDAux

namespace TDAux

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem coefX_cp (σ : Mat k r → (H →L[ℂ] H)) {D : Submodule ℂ H}
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) (x₀ g : Mat k r) (w : H) (m : D)
    (a b : Fin (2 * r + k + 1)) :
    coefX σ x₀ w ((actM E (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) m : D) : H) g +
      Complex.I * coefX σ x₀ w ((actM E (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) m : D) : H) g =
      coefX σ x₀ w ((E a b m : D) : H) g := by
  rw [← coefX_add_smul]
  congr 1
  have hZ := (Formalism.REAL.complex_parts_mem_lie_algebra_holds _ ε (Matrix.single a b (1 : ℂ))).2.2.1
  conv_rhs => rw [← actM_single E a b, hZ, actM_add, actM_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul]

theorem tMapD_hasDeriv {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hE : IsDerivedOn ε σ D E) {x₀ g X : Mat k r}
    (hx₀ : Formalism.REAL.inUJ ε x₀) (hg : Formalism.REAL.inUJ ε g) (hX : Formalism.REAL.inG ε X)
    (x₁ : Fin (2 * r + k + 1) → ℂ) (w : H) (f : Fin (2 * r + k + 1) → D) :
    HasDerivAt (fun t : ℝ => tMapD σ x₁ x₀ w (fun c => (f c : H)) (g * NormedSpace.exp ((t : ℂ) • X)))
      (∑ c, (-(Pi.single c 1 ⬝ᵥ (X *ᵥ ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ x₁))) *
          coefX σ x₀ w (f c : H) g +
        cJd x₁ (Pi.single c 1) g * coefX σ x₀ w ((actM E X (f c) : D) : H) g)) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun c _ =>
    (cJd_hasDeriv (ε := ε) x₁ (Pi.single c 1) hg hX).mul (coefX_hasDeriv hσ hE hx₀ hg hX w (f c)))
  simp only [Formalism.REAL.mul_exp_zero_smul_eq] at h
  exact h

theorem tensVd_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (a b : Fin (2 * r + k + 1))
    (f : Fin (2 * r + k + 1) → M) (c : Fin (2 * r + k + 1)) :
    LemK.tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [LemK.tensVd, LemK.prj, h]

theorem tMapD_Eab {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hE : IsDerivedOn ε σ D E) {x₀ g : Mat k r}
    (hx₀ : Formalism.REAL.inUJ ε x₀) (hg : Formalism.REAL.inUJ ε g)
    (x₁ : Fin (2 * r + k + 1) → ℂ) (w : H) (f : Fin (2 * r + k + 1) → D) (a b : Fin (2 * r + k + 1)) :
    Formalism.REAL.Eab ε a b (tMapD σ x₁ x₀ w (fun c => (f c : H))) g =
      tMapD σ x₁ x₀ w (fun c => ((LemK.tensVd E a b f c : D) : H)) g := by
  rw [Formalism.REAL.lie_derivative_def]
  unfold Formalism.REAL.Rd
  rw [(tMapD_hasDeriv hσ hE hx₀ hg (Formalism.REAL.real_part_single_mem ε a b) x₁ w f).deriv,
    (tMapD_hasDeriv hσ hE hx₀ hg (Formalism.REAL.imaginary_part_single_mem ε a b) x₁ w f).deriv]
  set y := (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ x₁ with hy
  have hZ := (Formalism.REAL.complex_parts_mem_lie_algebra_holds _ ε (Matrix.single a b (1 : ℂ))).2.2.1
  set X1 := Formalism.REAL.cpart1 ε (Matrix.single a b (1 : ℂ))
  set X2 := Formalism.REAL.cpart2 ε (Matrix.single a b (1 : ℂ))
  have hyb : cJd x₁ (Pi.single b 1) g = y b := by
    rw [cJd_eq x₁ _ hg, cL, hy, single_dotProduct, one_mul]
  have hL : ∀ c, (-(Pi.single c 1 ⬝ᵥ (X1 *ᵥ y)) * coefX σ x₀ w (f c : H) g +
        cJd x₁ (Pi.single c 1) g * coefX σ x₀ w ((actM E X1 (f c) : D) : H) g) +
      Complex.I * (-(Pi.single c 1 ⬝ᵥ (X2 *ᵥ y)) * coefX σ x₀ w (f c : H) g +
        cJd x₁ (Pi.single c 1) g * coefX σ x₀ w ((actM E X2 (f c) : D) : H) g) =
      cJd x₁ (Pi.single c 1) g * coefX σ x₀ w ((E a b (f c) : D) : H) g -
        (if c = a then y b * coefX σ x₀ w (f a : H) g else 0) := by
    intro c
    rw [← coefX_cp σ E x₀ g w (f c) a b]
    have e1 : Pi.single c 1 ⬝ᵥ (X1 *ᵥ y) + Complex.I * (Pi.single c 1 ⬝ᵥ (X2 *ᵥ y)) =
        if c = a then y b else 0 := by
      have h3 : X1 *ᵥ y + Complex.I • (X2 *ᵥ y) = (Matrix.single a b (1 : ℂ)) *ᵥ y := by
        rw [hZ, Matrix.add_mulVec, Matrix.smul_mulVec]
      calc Pi.single c 1 ⬝ᵥ (X1 *ᵥ y) + Complex.I * (Pi.single c 1 ⬝ᵥ (X2 *ᵥ y)) =
            Pi.single c 1 ⬝ᵥ (X1 *ᵥ y + Complex.I • (X2 *ᵥ y)) := by
            rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
        _ = Pi.single c 1 ⬝ᵥ ((Matrix.single a b (1 : ℂ)) *ᵥ y) := by rw [h3]
        _ = _ := ?_
      rw [single_dotProduct, one_mul]
      by_cases h : c = a
      · subst h; simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
      · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, h, Ne.symm h]
    have e2 : (if c = a then y b * coefX σ x₀ w (f a : H) g else 0) =
        (if c = a then y b else 0) * coefX σ x₀ w (f c : H) g := by
      by_cases h : c = a
      · subst h; simp
      · simp [h]
    rw [e2, ← e1]
    ring
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun c _ => hL c),
    Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ a]
  simp only [Finset.mem_univ, if_true]
  unfold tMapD
  have hR : ∀ c, cJd x₁ (Pi.single c 1) g * coefX σ x₀ w ((LemK.tensVd E a b f c : D) : H) g =
      cJd x₁ (Pi.single c 1) g * coefX σ x₀ w ((E a b (f c) : D) : H) g -
        (if c = b then cJd x₁ (Pi.single b 1) g * coefX σ x₀ w (f a : H) g else 0) := by
    intro c
    rw [tensVd_apply]
    by_cases h : c = b
    · subst h; simp [coefX_sub, mul_sub]
    · simp [h]
  rw [Finset.sum_congr rfl (fun c _ => hR c), Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ b]
  simp only [Finset.mem_univ, if_true, hyb]

end TDAux
end ReciprocityTheory.ChartRestriction.DS.Lap
