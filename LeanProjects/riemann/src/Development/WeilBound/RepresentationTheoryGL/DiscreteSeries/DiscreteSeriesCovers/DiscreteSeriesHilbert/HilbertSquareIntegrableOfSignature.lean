import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

section SquareIntegrability

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem hq_umem (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat g ∈ UJset ε :=
  ReciprocityTheory.ChartRestriction.DS.umat_mem_UJset ε g

theorem hq_one (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w)) :
    sigLam ε Ψ T.w (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) = 1 := by
  have e : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  rw [e]
  exact hrep.1.1

theorem hq_mul (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w)) (a b : Formalism.REAL.UJ ε) :
    sigLam ε Ψ T.w (Formalism.MainNotions.S.umat (a * b)) =
      (sigLam ε Ψ T.w (Formalism.MainNotions.S.umat a)).comp (sigLam ε Ψ T.w (Formalism.MainNotions.S.umat b)) := by
  have e : Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl
  rw [e]
  exact hrep.1.2 _ (hq_umem a) _ (hq_umem b)

theorem hq_iso (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w)) (g : Formalism.REAL.UJ ε) (v : Hlam ε Ψ T.w) :
    ‖sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) v‖ = ‖v‖ :=
  hrep.2.1 _ (hq_umem g) v

theorem hq_memLp_of_ne (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w))
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w)) (w₀ x₀ : Hlam ε Ψ T.w) (hx₀ : x₀ ≠ 0)
    (h0 : MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) x₀⟫_ℂ) 2 (Formalism.REAL.muG ε))
    (x : Hlam ε Ψ T.w) :
    MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) x⟫_ℂ) 2 (Formalism.REAL.muG ε) :=
  GraphTrick.memLp_of_ne (μ := Formalism.REAL.muG ε) (ρ := fun g : Formalism.REAL.UJ ε => sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g))
    (measurePreserving_mul_right ε) (hq_one hrep) (hq_mul hrep) (hq_iso hrep)
    (Formalism.MainNotions.BridgeCSchur.irr_of hirr) w₀ x₀ hx₀ h0 x

theorem hq_inner
    (hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x)
    (y z : Hlam ε Ψ T.w) (g : Formalism.REAL.UJ ε) :
    ⟪y, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) z⟫_ℂ = inner ℂ (y : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) (z : L2 ε)) := by
  rw [Submodule.coe_inner, hcoe _ (hq_umem g)]

theorem hq_w_ne (hP : IsPsiFor ε lam T Ψ) : uniformisationL2 ε Ψ T.w T.w ≠ 0 := by
  have hw : T.w ≠ 0 := by
    intro h
    have h1 : ‖T.w‖ = 1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  exact datumEmbedding_self_ne_zero hP hw

theorem hq_coef_all (hP : IsPsiFor ε lam T Ψ)
    (hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x)
    (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w))
    (hF : ∀ g ∈ UJset ε, ∀ v v' : T.V,
      inner ℂ (uniformisationL2 ε Ψ T.w v') (rreg ε g (uniformisationL2 ε Ψ T.w v)) =
        ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v))
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w)) (x : Hlam ε Ψ T.w) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      inner ℂ (uniformisationL2 ε Ψ T.w T.w) (rreg ε (Formalism.MainNotions.S.umat g) (x : L2 ε))) 2 (Formalism.REAL.muG ε) := by
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Hlam ε Ψ T.w, (w₀ : L2 ε) = uniformisationL2 ε Ψ T.w T.w := ⟨⟨_, datumEmbedding_mem_Hlam hP T.w⟩, rfl⟩
  have hne : w₀ ≠ 0 := by
    intro h
    apply hq_w_ne hP
    rw [← hw₀, h]
    rfl
  have e0 : (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) w₀⟫_ℂ) =
      fun g => ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * jfun Ψ T.w T.w (Formalism.MainNotions.S.umat g) := by
    funext g
    rw [hq_inner hcoe, hw₀, hF _ (hq_umem g)]
    rfl
  have h0 : MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) w₀⟫_ℂ) 2 (Formalism.REAL.muG ε) := by
    rw [e0]
    exact (dt_memLp hP T.w T.w).const_mul _
  have h1 := hq_memLp_of_ne hrep hirr w₀ w₀ hne h0 x
  have e1 : (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) x⟫_ℂ) =
      fun g => inner ℂ (uniformisationL2 ε Ψ T.w T.w) (rreg ε (Formalism.MainNotions.S.umat g) (x : L2 ε)) := by
    funext g
    rw [hq_inner hcoe, hw₀]
  rw [e1] at h1
  exact h1

theorem hq_sqInt (hP : IsPsiFor ε lam T Ψ)
    (hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x)
    (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w))
    (hF : ∀ g ∈ UJset ε, ∀ v v' : T.V,
      inner ℂ (uniformisationL2 ε Ψ T.w v') (rreg ε g (uniformisationL2 ε Ψ T.w v)) =
        ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v))
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w)) :
    Formalism.MainNotions.S.IsSqIntOn ε (sigLam ε Ψ T.w) := by
  intro v w
  show MemLp (fun g : Formalism.REAL.UJ ε => ⟪w, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) v⟫_ℂ) 2 (Formalism.REAL.muG ε)
  by_cases hw : w = 0
  · have e : (fun g : Formalism.REAL.UJ ε => ⟪w, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) v⟫_ℂ) = 0 := by
      funext g
      rw [hw, inner_zero_left]
      rfl
    rw [e]
    exact (Lp.memLp (0 : Lp ℂ 2 (Formalism.REAL.muG ε))).ae_eq (Lp.coeFn_zero ℂ 2 _)
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Hlam ε Ψ T.w, (w₀ : L2 ε) = uniformisationL2 ε Ψ T.w T.w := ⟨⟨_, datumEmbedding_mem_Hlam hP T.w⟩, rfl⟩
  have hne : w₀ ≠ 0 := by
    intro h
    apply hq_w_ne hP
    rw [← hw₀, h]
    rfl
  have hFw : MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) w⟫_ℂ) 2 (Formalism.REAL.muG ε) := by
    have e1 : (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) w⟫_ℂ) =
        fun g => inner ℂ (uniformisationL2 ε Ψ T.w T.w) (rreg ε (Formalism.MainNotions.S.umat g) (w : L2 ε)) := by
      funext g
      rw [hq_inner hcoe, hw₀]
    rw [e1]
    exact hq_coef_all hP hcoe hrep hF hirr w
  have hinv := (hFw.comp_measurePreserving (Measure.measurePreserving_inv (Formalism.REAL.muG ε))).star
  have e2 : star ((fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) w⟫_ℂ) ∘ Inv.inv) =
      fun g : Formalism.REAL.UJ ε => ⟪w, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) w₀⟫_ℂ := by
    funext g
    have hs : star (sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g⁻¹)) = sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g⁻¹⁻¹) :=
      GraphTrick.star_eq (ρ := fun g : Formalism.REAL.UJ ε => sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g))
        (hq_one hrep) (hq_mul hrep) (hq_iso hrep) g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  rw [e2] at hinv
  exact hq_memLp_of_ne hrep hirr w w₀ hne hinv v

end SquareIntegrability

theorem hilbert_square_integrable_of_signature : StepSig → StepSqInt := by
  intro hS n ε lam T Ψ hP hst hF hirr
  obtain ⟨hcoe, hrep, -⟩ := hS n ε lam T Ψ hP hst
  exact hq_sqInt hP hcoe hrep hF hirr

end PositivityTheory.RgDs.Hilb
