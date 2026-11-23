import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem tf_sqInt_of_hW {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    Formalism.MainNotions.S.IsSqIntOn ε (tfClRep σ (closGen E V)) := by
  have hU := tfClRep_isURepOn hgap hσ hD hV hc hVK
  have hst := closGen_stable hgap hσ hD hV hc hVK
  set ρ : Formalism.REAL.UJ ε → (closGen E V →L[ℂ] closGen E V) :=
    fun g => tfClRep σ (closGen E V) (Formalism.MainNotions.S.umat g) with hρ
  have hone : ρ 1 = 1 := by
    simp only [hρ]
    have e : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
    rw [e]; exact hU.1.1
  have hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := by
    intro a b
    simp only [hρ]
    have e : Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl
    rw [e]; exact hU.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hU.2.1 _ (umat_mem_UJset ε g) v
  have hirr := Formalism.MainNotions.BridgeCSchur.irr_of (tfClRep_irred hgap hσ hD hV hc hVK)
  obtain ⟨y, hyV, hy0, -⟩ := hV.2.2.2
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  let y0 : closGen E V := ⟨((y : D) : H), Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩⟩
  have hy0 : y0 ≠ 0 := by
    intro h
    apply hy0
    have h2 : ((y : D) : H) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2
  have hcoe : ∀ (g : Formalism.REAL.UJ ε) (x w : closGen E V),
      inner ℂ w (ρ g x) = inner ℂ (w : H) (σ (Formalism.MainNotions.S.umat g) (x : H)) := by
    intro g x w
    rw [Submodule.coe_inner, tfClRep_coe σ _ (hst _ (umat_mem_UJset ε g))]
  have hcont : Continuous (fun g : Formalism.REAL.UJ ε => inner ℂ ((y : D) : H) (σ (Formalism.MainNotions.S.umat g) ((y : D) : H))) :=
    continuous_const.inner ((hσ.2.2 _).comp_continuous Formalism.MainNotions.BridgeCSchur.continuous_umat
      (fun g => umat_mem_UJset ε g))
  have h0 : MemLp (fun g => inner ℂ y0 (ρ g y0)) 2 (Formalism.REAL.muG ε) := by
    simp only [hcoe]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : Subsingleton (Formalism.REAL.UJ ε) :=
        ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
      have : CompactSpace (Formalism.REAL.UJ ε) := Finite.compactSpace
      refine MemLp.of_bound hcont.aestronglyMeasurable (‖((y : D) : H)‖ * ‖((y : D) : H)‖)
        (Filter.Eventually.of_forall fun g => ?_)
      calc ‖inner ℂ ((y : D) : H) (σ (Formalism.MainNotions.S.umat g) ((y : D) : H))‖
          ≤ ‖((y : D) : H)‖ * ‖σ (Formalism.MainNotions.S.umat g) ((y : D) : H)‖ := norm_inner_le_norm _ _
        _ = _ := by rw [hσ.2.1 _ (umat_mem_UJset ε g)]
    · refine (hW y hyG y hyG).of_le hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
      have h1 : 1 ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) :=
        Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs (umat_mem_UJset ε g) ⟨0, hn⟩)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact le_mul_of_one_le_left (norm_nonneg _) h1
  have hall : ∀ x, MemLp (fun g => inner ℂ y0 (ρ g x)) 2 (Formalism.REAL.muG ε) := fun x =>
    GraphTrick.memLp_of_ne (μ := Formalism.REAL.muG ε) (ρ := ρ) (measurePreserving_mul_right ε) hone hmul hiso hirr
      y0 y0 hy0 h0 x
  intro v w
  show MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ w (ρ g v)) 2 (Formalism.REAL.muG ε)
  by_cases hw : w = 0
  · have e : (fun g : Formalism.REAL.UJ ε => inner ℂ w (ρ g v)) = 0 := by
      funext g
      rw [hw, inner_zero_left]
      rfl
    rw [e]
    exact (Lp.memLp (0 : Lp ℂ 2 (Formalism.REAL.muG ε))).ae_eq (Lp.coeFn_zero ℂ 2 _)
  have hinv := ((hall w).comp_measurePreserving (Measure.measurePreserving_inv (Formalism.REAL.muG ε))).star
  have e2 : star ((fun g : Formalism.REAL.UJ ε => inner ℂ y0 (ρ g w)) ∘ Inv.inv) =
      fun g : Formalism.REAL.UJ ε => inner ℂ w (ρ g y0) := by
    funext g
    have hs : star (ρ g⁻¹) = ρ g⁻¹⁻¹ := GraphTrick.star_eq hone hmul hiso g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  rw [e2] at hinv
  exact GraphTrick.memLp_of_ne (μ := Formalism.REAL.muG ε) (ρ := ρ) (measurePreserving_mul_right ε) hone hmul hiso hirr
    w y0 hy0 hinv v

end ReciprocityTheory.ChartRestriction.DS
