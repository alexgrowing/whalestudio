import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def ob3PsiCoef (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ c, inner ℂ (ξ c) (∑ d, (cond dual ((g⁻¹) d c) (g c d)) • Ψ g (ζ d))

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem psi_weighted_memLp {v₀ : T.V} (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (v w : T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε) := by
  have hC : ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have h := datumEmbedding_highest_ne_zero hgap hP hv₀
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 h)
  have hmem : ∀ u, (⟨uniformisationL2 ε Ψ v₀ u, datumEmbedding_mem_smooth hP v₀ u⟩ : smD ε (rreg ε)) ∈
      genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) := fun u =>
    Submodule.mem_sInf.2 (fun S hS => hS.1 (Submodule.mem_comap.2 (Submodule.subset_span ⟨u, rfl⟩)))
  have h := (hW _ (hmem v) _ (hmem w)).const_mul (((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ)⁻¹)
  refine h.congr_norm ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact h.1.congr (Filter.Eventually.of_forall fun g => by
      simp only
      rw [formulaF hgap hP hv₀ (g := Formalism.MainNotions.S.umat g) g.2 v w]
      field_simp)
  · simp only
    rw [formulaF hgap hP hv₀ (g := Formalism.MainNotions.S.umat g) g.2 v w]
    congr 1
    field_simp

end Psi

theorem norm_unitary_inv_entry {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖(Formalism.MainNotions.S.umat g)⁻¹ d c‖ = ‖Formalism.MainNotions.S.umat g c d‖ := by
  have hg : inUJ ε (Formalism.MainNotions.S.umat g) := g.2
  have h1 : (Jm ε * (Formalism.MainNotions.S.umat g)ᴴ * Jm ε) * Formalism.MainNotions.S.umat g = 1 := by
    calc (Jm ε * (Formalism.MainNotions.S.umat g)ᴴ * Jm ε) * Formalism.MainNotions.S.umat g
        = Jm ε * ((Formalism.MainNotions.S.umat g)ᴴ * Jm ε * Formalism.MainNotions.S.umat g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, S7.Jm_mul_self]
  rw [Matrix.inv_eq_left_inv h1]
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem norm_unitary_entry_le_sqrt_hs {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖Formalism.MainNotions.S.umat g c d‖ ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) := by
  rw [← Real.sqrt_sq (norm_nonneg (Formalism.MainNotions.S.umat g c d))]
  apply Real.sqrt_le_sqrt
  unfold S7.hs
  calc ‖Formalism.MainNotions.S.umat g c d‖ ^ 2 ≤ ∑ j, ‖Formalism.MainNotions.S.umat g c j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖Formalism.MainNotions.S.umat g c j‖ ^ 2) (fun j _ => sq_nonneg _) (mem_univ d)
    _ ≤ ∑ i, ∑ j, ‖Formalism.MainNotions.S.umat g i j‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖Formalism.MainNotions.S.umat g i j‖ ^ 2)
          (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (mem_univ c)

theorem norm_dual_entry_le_sqrt_hs (dual : Bool) {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖cond dual ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d)‖ ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) := by
  cases dual
  · exact norm_unitary_entry_le_sqrt_hs g c d
  · simp only [cond]; rw [norm_unitary_inv_entry]; exact norm_unitary_entry_le_sqrt_hs g c d

theorem continuous_dual_entry (dual : Bool) {ε : Fin n → Bool} (c d : Fin n) :
    Continuous (fun g : Formalism.REAL.UJ ε => cond dual ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d)) := by
  cases dual
  · exact (continuous_apply d).comp ((continuous_apply c).comp ((Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val))
  · have e : (fun g : Formalism.REAL.UJ ε => cond true ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d)) =
        fun g : Formalism.REAL.UJ ε => ((((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
          Matrix (Fin n) (Fin n) ℂ) d c) := by
      funext g
      simp only [cond, Formalism.MainNotions.S.umat, Matrix.coe_units_inv]
    rw [e]
    exact (continuous_apply c).comp ((continuous_apply d).comp ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val))

section Psi2

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem aestronglyMeasurable_psi_inner (hP : IsPsiFor ε lam T Ψ) (x y : T.V) :
    AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => inner ℂ x (Ψ (Formalism.MainNotions.S.umat g) y)) (Formalism.REAL.muG ε) := by
  have hΨm : AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) (Formalism.REAL.muG ε) :=
    (hP.2.2.2.2 (Formalism.REAL.muG ε) (Formalism.REAL.instIsHaarMuG n ε)).1
  exact (continuous_const.inner (continuous_id.clm_apply continuous_const)).comp_aestronglyMeasurable hΨm

theorem psi_inner_memLp (hP : IsPsiFor ε lam T Ψ) (x y : T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ x (Ψ (Formalism.MainNotions.S.umat g) y)) 2 (Formalism.REAL.muG ε) := by
  have hΨ : MemLp (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    hP.2.2.2.2 (Formalism.REAL.muG ε) (Formalism.REAL.instIsHaarMuG n ε)
  refine hΨ.of_le_mul (c := ‖x‖ * ‖y‖) (aestronglyMeasurable_psi_inner hP x y) (Filter.Eventually.of_forall fun g => ?_)
  calc ‖inner ℂ x (Ψ (Formalism.MainNotions.S.umat g) y)‖ ≤ ‖x‖ * ‖Ψ (Formalism.MainNotions.S.umat g) y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖Ψ (Formalism.MainNotions.S.umat g)‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖x‖ * ‖y‖ * ‖Ψ (Formalism.MainNotions.S.umat g)‖ := by ring

theorem psi_coef_memLp_of_weighted (dual : Bool) (hP : IsPsiFor ε lam T Ψ)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  have e : (fun g : Formalism.REAL.UJ ε => ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) = fun g => ∑ c, ∑ d,
      cond dual ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d) *
        inner ℂ (ξ c) (Ψ (Formalism.MainNotions.S.umat g) (ζ d)) := by
    funext g
    simp only [ob3PsiCoef, inner_sum, inner_smul_right]
  rw [e]
  refine memLp_finsetSum _ fun c _ => memLp_finsetSum _ fun d _ => ?_
  refine (hWT (ζ d) (ξ c)).of_le (((continuous_dual_entry dual c d).aestronglyMeasurable).mul (aestronglyMeasurable_psi_inner hP _ _))
    (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right (norm_dual_entry_le_sqrt_hs dual g c d) (norm_nonneg _)

theorem psi_pairing_integrable (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) (u' v' : T'.V) :
    Integrable (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
      inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')) (Formalism.REAL.muG ε) :=
  (psi_coef_memLp_of_weighted dual hP hWT ξ ζ).star.integrable_mul (psi_inner_memLp hP' u' v')

end Psi2

theorem clm_mul_apply_eq_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A B : E →L[ℂ] E) (x : E) :
    (A * B) x = A (B x) := rfl

theorem dual_entry_mul_sum (dual : Bool) (K H : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) :
    cond dual ((K * H)⁻¹ d c) ((K * H) c d) =
      ∑ e, cond dual (K⁻¹ e c) (K c e) * cond dual (H⁻¹ d e) (H e d) := by
  cases dual
  · simp only [cond, Matrix.mul_apply]
  · simp only [cond, Matrix.mul_inv_rev, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _

section Psi3

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem psi_k_left_equivariant {Λ : Fin n → ℝ} {T : S7.KType ε Λ} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hK : ∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂) (k : S7.KG ε) (h : Formalism.REAL.UJ ε) :
    Ψ (S7.toMK k * Formalism.MainNotions.S.umat h) = T.op k * Ψ (Formalism.MainNotions.S.umat h) := by
  have e := hK k 1 (Formalism.MainNotions.S.umat h) h.2
  have h1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
  have h2 : T.op 1 = 1 := by simp [S7.KType.op]
  rwa [h1, mul_one, h2, mul_one] at e

theorem psi_coef_k_left_translate (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (k : S7.KG ε) (h : Formalism.REAL.UJ ε)
    (ξ ζ : Fin n → T.V) :
    ob3PsiCoef dual Ψ ξ ζ (S7.toMK k * Formalism.MainNotions.S.umat h) =
      ob3PsiCoef dual Ψ (fun e => ∑ c, starRingEnd ℂ (cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e)) •
        (ContinuousLinearMap.adjoint (T.op k)) (ξ c)) ζ (Formalism.MainNotions.S.umat h) := by
  have hΨ := psi_k_left_equivariant hP.1 k h
  have hL : ob3PsiCoef dual Ψ ξ ζ (S7.toMK k * Formalism.MainNotions.S.umat h) = ∑ c, ∑ d, ∑ e,
      cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e) *
        cond dual ((Formalism.MainNotions.S.umat h)⁻¹ d e) (Formalism.MainNotions.S.umat h e d) *
          inner ℂ (ξ c) (T.op k (Ψ (Formalism.MainNotions.S.umat h) (ζ d))) := by
    simp only [ob3PsiCoef, hΨ, dual_entry_mul_sum, clm_mul_apply_eq_comp, inner_sum, inner_smul_right,
      Finset.sum_mul]
  have hR : ob3PsiCoef dual Ψ (fun e => ∑ c, starRingEnd ℂ (cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e)) •
        (ContinuousLinearMap.adjoint (T.op k)) (ξ c)) ζ (Formalism.MainNotions.S.umat h) = ∑ e, ∑ d, ∑ c,
      cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e) *
        cond dual ((Formalism.MainNotions.S.umat h)⁻¹ d e) (Formalism.MainNotions.S.umat h e d) *
          inner ℂ (ξ c) (T.op k (Ψ (Formalism.MainNotions.S.umat h) (ζ d))) := by
    simp only [ob3PsiCoef, inner_sum, inner_smul_right, sum_inner, inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left, RCLike.conj_conj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by ring
  rw [hL, hR]
  calc _ = ∑ c, ∑ e, ∑ d, cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e) *
        cond dual ((Formalism.MainNotions.S.umat h)⁻¹ d e) (Formalism.MainNotions.S.umat h e d) *
          inner ℂ (ξ c) (T.op k (Ψ (Formalism.MainNotions.S.umat h) (ζ d))) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = _ := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun e _ => Finset.sum_comm

theorem psi_pairing_vanishing_spread (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ') {v₀' : T'.V} (hv₀' : v₀' ≠ 0)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (h0 : ∀ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0) :
    ∀ (ξ ζ : Fin n → T.V) (u' v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0 := by
  let W : Submodule ℂ T'.V :=
    { carrier := {u' | ∀ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
        starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')
          ∂(Formalism.REAL.muG ε) = 0}
      add_mem' := fun {a b} ha hb ξ ζ v' => by
        simp only [inner_add_left, mul_add]
        rw [integral_add (psi_pairing_integrable dual hP hP' hWT ξ ζ a v') (psi_pairing_integrable dual hP hP' hWT ξ ζ b v'),
          ha ξ ζ v', hb ξ ζ v', add_zero]
      zero_mem' := fun ξ ζ v' => by simp only [inner_zero_left, mul_zero, integral_zero]
      smul_mem' := fun c x hx ξ ζ v' => by
        have e : (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
            inner ℂ (c • x) (Ψ' (Formalism.MainNotions.S.umat g) v')) = fun g => starRingEnd ℂ c *
              (starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ x (Ψ' (Formalism.MainNotions.S.umat g) v')) := by
          funext g
          rw [inner_smul_left]
          ring
        show ∫ g : Formalism.REAL.UJ ε, starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
            inner ℂ (c • x) (Ψ' (Formalism.MainNotions.S.umat g) v') ∂(Formalism.REAL.muG ε) = 0
        rw [e, integral_const_mul, hx ξ ζ v', mul_zero] }
  have hst : ∀ k : S7.KG ε, ∀ v ∈ W, T'.op k v ∈ W := by
    intro k u hu ξ ζ v'
    let kk : Formalism.REAL.UJ ε := ⟨((k : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ), (k : S7.UJ ε).2⟩
    rw [← integral_mul_left_eq_self (μ := Formalism.REAL.muG ε) _ kk]
    have e : ∀ g : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat (kk * g) =
        S7.toMK k * Formalism.MainNotions.S.umat g := fun g => rfl
    simp only [e, psi_coef_k_left_translate dual hP k, psi_k_left_equivariant hP'.1 k, clm_mul_apply_eq_comp,
      ContinuousLinearMap.inner_map_map_of_mem_unitary (T'.τ k).2]
    exact hu _ ζ v'
  have hv : v₀' ∈ W := h0
  rcases T'.irred W hst with hW | hW
  · exact absurd ((Submodule.mem_bot ℂ).1 (hW ▸ hv)) hv₀'
  · intro ξ ζ u' v'
    have hu : u' ∈ W := hW ▸ Submodule.mem_top
    exact hu ξ ζ v'

end Psi3

end ReciprocityTheory.ChartRestriction.DS
