import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelGamA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix MG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem map_gl_mul (τ : E →+* ℂ) (γ₁ γ₂ : GL (Fin r) E) :
    ((γ₁ * γ₂ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ =
      (γ₁ : Matrix (Fin r) (Fin r) E).map τ * (γ₂ : Matrix (Fin r) (Fin r) E).map τ := by
  rw [Units.val_mul, Matrix.map_mul]

theorem map_gl_inv_mul (τ : E →+* ℂ) (γ : GL (Fin r) E) :
    ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * (γ : Matrix (Fin r) (Fin r) E).map τ = 1 := by
  rw [← map_gl_mul, inv_mul_cancel, Units.val_one, Matrix.map_one τ (map_zero τ) (map_one τ)]

def TSet (Ψ : Finset (E →+* ℂ)) (g : Matrix (Fin r) (Fin r) E) : Set (Frame Ψ r) :=
  {x | ∀ τ : Ψ, ∀ a c : Fin r, c < a → (adjugate (mat x τ) * g.map τ.1 * mat x τ) a c = 0}

theorem isClosed_TSet (Ψ : Finset (E →+* ℂ)) (g : Matrix (Fin r) (Fin r) E) : IsClosed (TSet Ψ g) := by
  simp only [TSet, Set.setOf_forall]
  refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
    isClosed_iInter fun _ => ?_
  have hm : Continuous fun x : Frame Ψ r => mat x τ :=
    continuous_pi fun i => continuous_pi fun j => by
      simp only [mat, Matrix.of_apply]
      fun_prop
  exact isClosed_eq
    (((hm.matrix_adjugate.matrix_mul continuous_const).matrix_mul hm).matrix_elem a c)
    continuous_const

theorem mem_TSet (Ψ : Finset (E →+* ℂ)) (γ γ' : GL (Fin r) E) {x b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (h : lact γ x = rmul (lact γ' x) b) : x ∈ TSet Ψ ((γ'⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
  simp only [TSet, Set.mem_setOf_eq]
  intro τ a c hca
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) := by
    have h0 := congrArg (fun y => mat y τ) h
    rw [← Matrix.mul_assoc]
    exact h0
  have h2 : adjugate (mat x τ) * ((γ'⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat x τ = (mat x τ).det • mat b τ := by
    rw [map_gl_mul]
    simp only [Matrix.mul_assoc]
    rw [h1, ← Matrix.mul_assoc _ ((γ' : Matrix (Fin r) (Fin r) E).map τ.1), map_gl_inv_mul,
      Matrix.one_mul, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [h2, Matrix.smul_apply, smul_eq_mul]
  have hB : b τ a c = 0 := (hb τ).2 a c hca
  simp [mat, hB]

theorem scalar_step {Ψ : Finset (E →+* ℂ)} (τ₀ : Ψ) (g : Matrix (Fin r) (Fin r) E) {W : Set (Frame Ψ r)}
    (hWo : IsOpen W) (hWT : W ⊆ TSet Ψ g) {y : Frame Ψ r} (hyW : y ∈ W) (hy : (mat y τ₀).det ≠ 0) :
    ∃ κ : ℂ, g.map τ₀.1 = κ • 1 := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨0, by ext a; exact Fin.elim0 a⟩
  set M : Matrix (Fin r) (Fin r) ℂ := g.map τ₀.1 with hM
  let i0 : Fin r := ⟨0, hr⟩
  let fr : (Fin r → ℂ) → Frame Ψ r := fun v τ a c => if τ = τ₀ ∧ c = i0 then v a else y τ a c
  let v₀ : Fin r → ℂ := fun a => y τ₀ a i0
  have hfr : Continuous fr := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    by_cases h : τ = τ₀ ∧ c = i0
    · simp only [fr, if_pos h]
      exact continuous_apply a
    · simp only [fr, if_neg h]
      exact continuous_const
  have hfr0 : fr v₀ = y := by
    funext τ a c
    by_cases h : τ = τ₀ ∧ c = i0
    · obtain ⟨rfl, rfl⟩ := h
      simp [fr, v₀]
    · simp [fr, h]
  have hdet : Continuous fun v => (mat (fr v) τ₀).det := by
    refine Continuous.matrix_det ?_
    exact continuous_pi fun a => continuous_pi fun c => by
      simp only [mat, Matrix.of_apply]
      exact (continuous_apply c).comp ((continuous_apply a).comp ((continuous_apply τ₀).comp hfr))
  have hW1 : ∀ᶠ v in nhds v₀, fr v ∈ W := (hfr.tendsto' v₀ y hfr0) (hWo.mem_nhds hyW)
  have hP : ∀ᶠ v in nhds v₀, fr v ∈ W ∧ (mat (fr v) τ₀).det ≠ 0 :=
    hW1.and (hdet.continuousAt.eventually_ne (by
      show (mat (fr v₀) τ₀).det ≠ 0
      rw [hfr0]
      exact hy))
  have hB : ∀ v, fr v ∈ W → (mat (fr v) τ₀).det ≠ 0 → ∃ l : ℂ, M *ᵥ v = l • v := by
    intro v hvW hd
    have hT : ∀ τ : Ψ, ∀ a c : Fin r, c < a →
        (adjugate (mat (fr v) τ) * g.map τ.1 * mat (fr v) τ) a c = 0 := hWT hvW
    set X := mat (fr v) τ₀ with hX
    have hcol : ∀ a, X a i0 = v a := fun a => by simp [hX, mat, fr]
    set z := X.adjugate *ᵥ (M *ᵥ v) with hz
    have hz0 : ∀ a, a ≠ i0 → z a = 0 := by
      intro a ha
      have h1 := hT τ₀ a i0 (by
        rw [Fin.lt_iff_val_lt_val]
        exact Nat.pos_of_ne_zero fun h => ha (Fin.ext h))
      have h2 : z a = (X.adjugate * M * X) a i0 := by
        rw [hz, Matrix.mulVec_mulVec]
        simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hcol]
      rw [h2]
      exact h1
    have hXz : X *ᵥ z = X.det • (M *ᵥ v) := by
      calc X *ᵥ z = (X * X.adjugate) *ᵥ (M *ᵥ v) := by
            rw [hz]
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = X.det • (M *ᵥ v) := by
            rw [Matrix.mul_adjugate]
            first
              | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
              | (ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])
    have hXz' : X *ᵥ z = z i0 • v := by
      funext a
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i0 (fun b _ hb => by rw [hz0 b hb, mul_zero])
        (fun h => absurd (Finset.mem_univ i0) h), hcol, mul_comm]
    refine ⟨z i0 / X.det, ?_⟩
    funext a
    have ha := congrFun (hXz.symm.trans hXz') a
    simp only [Pi.smul_apply, smul_eq_mul] at ha ⊢
    rw [div_mul_eq_mul_div, eq_div_iff hd]
    linear_combination ha
  have hQ : ∀ v, fr v ∈ W → (mat (fr v) τ₀).det ≠ 0 →
      ∀ a b, (M *ᵥ v) a * v b = (M *ᵥ v) b * v a := by
    intro v h1 h2 a b
    obtain ⟨l, hl⟩ := hB v h1 h2
    rw [hl]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hall : ∀ u : Fin r → ℂ, ∀ a b, (M *ᵥ u) a * u b = (M *ᵥ u) b * u a := by
    intro u a b
    have t1 : Filter.Tendsto (fun s : ℂ => v₀ + s • u) (nhds 0) (nhds v₀) :=
      Continuous.tendsto' (by fun_prop) 0 v₀ (by simp)
    have t2 : Filter.Tendsto (fun s : ℂ => v₀ + (2 * s) • u) (nhds 0) (nhds v₀) :=
      Continuous.tendsto' (by fun_prop) 0 v₀ (by simp)
    have e1 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, fr (v₀ + s • u) ∈ W ∧ (mat (fr (v₀ + s • u)) τ₀).det ≠ 0 :=
      nhdsWithin_le_nhds (t1.eventually hP)
    have e2 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ,
        fr (v₀ + (2 * s) • u) ∈ W ∧ (mat (fr (v₀ + (2 * s) • u)) τ₀).det ≠ 0 :=
      nhdsWithin_le_nhds (t2.eventually hP)
    have e3 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, s ≠ 0 := self_mem_nhdsWithin
    obtain ⟨s, hs1, hs2, hs0⟩ := (e1.and (e2.and e3)).exists
    have q0 := hQ v₀ (by rw [hfr0]; exact hyW) (by rw [hfr0]; exact hy) a b
    have q1 := hQ _ hs1.1 hs1.2 a b
    have q2 := hQ _ hs2.1 hs2.2 a b
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at q1 q2
    have key : (2 * s ^ 2) * ((M *ᵥ u) a * u b - (M *ᵥ u) b * u a) = 0 := by
      linear_combination q2 - 2 * q1 + q0
    have hs2' : (2 * s ^ 2 : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hs0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hs2')
  have hcolv : ∀ j i, (M *ᵥ Pi.single j 1) i = M i j := by
    intro j i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hoff : ∀ a b, a ≠ b → M a b = 0 := by
    intro a b hab
    have h := hall (Pi.single b 1) a b
    rw [hcolv, hcolv] at h
    simpa [Pi.single_apply, hab] using h
  have hdiag : ∀ a b, M a a = M b b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    have h := hall (Pi.single a 1 + Pi.single b 1) a b
    rw [Matrix.mulVec_add] at h
    simp only [Pi.add_apply, hcolv] at h
    simp [Pi.single_apply, hab, Ne.symm hab, hoff a b hab, hoff b a (Ne.symm hab)] at h
    linear_combination h
  refine ⟨M i0 i0, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [hdiag a i0]
  · simp [hoff a b hab, hab]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
