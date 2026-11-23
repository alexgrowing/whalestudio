import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem umat_mem_UJset (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat g ∈ UJset ε := by
  rw [← mir_UJset_eq]; exact g.2

theorem sigLam_umat_one (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) = 1 := by
  have e : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  rw [e]
  exact (sigLam_isURepOn hgap hP hv₀).1.1

theorem sigLam_umat_mul (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (a b : Formalism.REAL.UJ ε) :
    sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat (a * b)) = (sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat a)).comp (sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat b)) := by
  have e : Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl
  rw [e]
  exact (sigLam_isURepOn hgap hP hv₀).1.2 _ (umat_mem_UJset a) _ (umat_mem_UJset b)

theorem sigLam_umat_iso (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (g : Formalism.REAL.UJ ε)
    (v : Hlam ε Ψ v₀) : ‖sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) v‖ = ‖v‖ :=
  (sigLam_isURepOn hgap hP hv₀).2.1 _ (umat_mem_UJset g) v

theorem sigLam_memLp_of_ne (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (w₀ x₀ : Hlam ε Ψ v₀)
    (hx₀ : x₀ ≠ 0)
    (h0 : MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) x₀⟫_ℂ) 2 (Formalism.REAL.muG ε))
    (x : Hlam ε Ψ v₀) :
    MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) x⟫_ℂ) 2 (Formalism.REAL.muG ε) :=
  GraphTrick.memLp_of_ne (μ := Formalism.REAL.muG ε) (ρ := fun g : Formalism.REAL.UJ ε => sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g))
    (measurePreserving_mul_right ε) (sigLam_umat_one hgap hP hv₀) (sigLam_umat_mul hgap hP hv₀)
    (sigLam_umat_iso hgap hP hv₀) (Formalism.MainNotions.BridgeCSchur.irr_of (sigLam_irred hgap hP hv₀)) w₀ x₀ hx₀ h0 x

theorem inner_sigLam_umat (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (y z : Hlam ε Ψ v₀)
    (g : Formalism.REAL.UJ ε) :
    ⟪y, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) z⟫_ℂ = inner ℂ (y : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) (z : L2 ε)) := by
  rw [Submodule.coe_inner, sigLam_coe hgap hP hv₀ (umat_mem_UJset g)]

theorem coef_memLp_all (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (x : Hlam ε Ψ v₀) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      inner ℂ (uniformisationL2 ε Ψ v₀ T.w) (rreg ε (Formalism.MainNotions.S.umat g) (x : L2 ε))) 2 (Formalism.REAL.muG ε) := by
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Hlam ε Ψ v₀, (w₀ : L2 ε) = uniformisationL2 ε Ψ v₀ T.w := ⟨⟨_, datumEmbedding_mem_Hlam hP T.w⟩, rfl⟩
  have hne : w₀ ≠ 0 := by
    intro h
    apply datumEmbedding_highest_ne_zero hgap hP hv₀
    rw [← hw₀, h]
    rfl
  have e0 : (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w₀⟫_ℂ) =
      fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * jfun Ψ T.w T.w (Formalism.MainNotions.S.umat g) := by
    funext g
    rw [inner_sigLam_umat hgap hP hv₀, hw₀, formulaF hgap hP hv₀ (umat_mem_UJset g)]
    rfl
  have h0 : MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w₀⟫_ℂ) 2 (Formalism.REAL.muG ε) := by
    rw [e0]
    exact ((datumFunction_isSmoothL2 hP T.w T.w).2 []).const_mul _
  have h1 := sigLam_memLp_of_ne hgap hP hv₀ w₀ w₀ hne h0 x
  have e1 : (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) x⟫_ℂ) =
      fun g => inner ℂ (uniformisationL2 ε Ψ v₀ T.w) (rreg ε (Formalism.MainNotions.S.umat g) (x : L2 ε)) := by
    funext g
    rw [inner_sigLam_umat hgap hP hv₀, hw₀]
  rw [e1] at h1
  exact h1

theorem sqInt_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : Formalism.MainNotions.S.IsSqIntOn ε (sigLam ε Ψ v₀) := by
  intro v w
  show MemLp (fun g : Formalism.REAL.UJ ε => ⟪w, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) v⟫_ℂ) 2 (Formalism.REAL.muG ε)
  by_cases hw : w = 0
  · have e : (fun g : Formalism.REAL.UJ ε => ⟪w, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) v⟫_ℂ) = 0 := by
      funext g
      rw [hw, inner_zero_left]
      rfl
    rw [e]
    exact (Lp.memLp (0 : Lp ℂ 2 (Formalism.REAL.muG ε))).ae_eq (Lp.coeFn_zero ℂ 2 _)
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Hlam ε Ψ v₀, (w₀ : L2 ε) = uniformisationL2 ε Ψ v₀ T.w := ⟨⟨_, datumEmbedding_mem_Hlam hP T.w⟩, rfl⟩
  have hne : w₀ ≠ 0 := by
    intro h
    apply datumEmbedding_highest_ne_zero hgap hP hv₀
    rw [← hw₀, h]
    rfl
  have hF : MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w⟫_ℂ) 2 (Formalism.REAL.muG ε) := by
    have e1 : (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w⟫_ℂ) =
        fun g => inner ℂ (uniformisationL2 ε Ψ v₀ T.w) (rreg ε (Formalism.MainNotions.S.umat g) (w : L2 ε)) := by
      funext g
      rw [inner_sigLam_umat hgap hP hv₀, hw₀]
    rw [e1]
    exact coef_memLp_all hgap hP hv₀ w
  have hinv := (hF.comp_measurePreserving (Measure.measurePreserving_inv (Formalism.REAL.muG ε))).star
  have e2 : star ((fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w⟫_ℂ) ∘ Inv.inv) =
      fun g : Formalism.REAL.UJ ε => ⟪w, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w₀⟫_ℂ := by
    funext g
    have hs : star (sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g⁻¹)) = sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g⁻¹⁻¹) :=
      GraphTrick.star_eq (ρ := fun g : Formalism.REAL.UJ ε => sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g))
        (sigLam_umat_one hgap hP hv₀) (sigLam_umat_mul hgap hP hv₀) (sigLam_umat_iso hgap hP hv₀) g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  rw [e2] at hinv
  exact sigLam_memLp_of_ne hgap hP hv₀ w w₀ hne hinv v

end ReciprocityTheory.ChartRestriction.DS
