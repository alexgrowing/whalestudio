import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth

noncomputable section

open Finset Matrix MeasureTheory
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

abbrev L2 (ε : Fin n → Bool) : Type := Lp ℂ 2 (Formalism.REAL.muG ε)

def rregG (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) : L2 ε →L[ℂ] L2 ε :=
  if hm : MeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y) (Formalism.REAL.muG ε) (Formalism.REAL.muG ε) then
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x : Formalism.REAL.UJ ε => x * y) hm).toContinuousLinearMap
  else 1

def rreg (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : L2 ε →L[ℂ] L2 ε :=
  if h : ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g then rregG ε h.choose else 1

def toL2 (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : L2 ε :=
  if h : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) then h.toLp _ else 0

theorem signature_matrix_sq (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem exists_unitary_preimage (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g := by
  have hJ := signature_matrix_sq ε
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hl : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc gᴴ (Formalism.REAL.Jm ε) g, h, hJ]
  have hr : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
    first
    | exact mul_eq_one_comm.mp hl
    | (letI := Matrix.invertibleOfLeftInverse g _ hl; exact mul_invOf_self g)
  exact ⟨⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, hr, hl⟩, h⟩, rfl⟩

theorem unitary_matrix_injective (ε : Fin n → Bool) {x y : Formalism.REAL.UJ ε}
    (h : Formalism.MainNotions.S.umat x = Formalism.MainNotions.S.umat y) : x = y := Subtype.ext (Units.ext h)

theorem unitary_matrix_mem_set (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat y ∈ UJset ε := y.2

theorem continuous_unitary_matrix (ε : Fin n → Bool) :
    Continuous (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) := Units.continuous_val.comp continuous_subtype_val

theorem rightRegular_unitary_eq (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) :
    rreg ε (Formalism.MainNotions.S.umat y) = rregG ε y := by
  have h : ∃ y' : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y' = Formalism.MainNotions.S.umat y := ⟨y, rfl⟩
  unfold rreg
  rw [dif_pos h, unitary_matrix_injective ε h.choose_spec]

theorem rightRegularGroup_eq_comp (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (f : L2 ε) :
    rregG ε y f = Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y) (measurePreserving_mul_right ε y) f := by
  unfold rregG
  rw [dif_pos (measurePreserving_mul_right ε y)]
  rfl

theorem toL2_eq_memLp_toLp (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε F = hF.toLp _ := by
  unfold toL2
  exact dif_pos hF

theorem toL2_eq_zero_of_not_memLp (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ¬ MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε F = 0 := by
  unfold toL2
  exact dif_neg hF

theorem rreg_umat_ae (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (f : L2 ε) :
    (rreg ε (Formalism.MainNotions.S.umat y) f : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε] fun x => f (x * y) := by
  rw [rightRegular_unitary_eq, rightRegularGroup_eq_comp]
  exact Lp.coeFn_compMeasurePreserving _ _

theorem rightRegular_toL2 (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : rreg ε g (toL2 ε F) = toL2 ε (fun x => F (x * g)) := by
  obtain ⟨y, rfl⟩ := exists_unitary_preimage ε hg
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hFy : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat y)) 2
        (Formalism.REAL.muG ε) := hF.comp_measurePreserving (measurePreserving_mul_right ε y)
    rw [toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε (F := fun x => F (x * Formalism.MainNotions.S.umat y)) hFy,
      rightRegular_unitary_eq, rightRegularGroup_eq_comp]
    refine Lp.ext ?_
    refine (Lp.coeFn_compMeasurePreserving _ _).trans ?_
    refine (hF.coeFn_toLp.comp_tendsto
      (measurePreserving_mul_right ε y).quasiMeasurePreserving.tendsto_ae).trans ?_
    exact hFy.coeFn_toLp.symm
  · have hFy : ¬ MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat y)) 2
        (Formalism.REAL.muG ε) := by
      intro h
      apply hF
      have h2 := h.comp_measurePreserving (measurePreserving_mul_right ε y⁻¹)
      have e : ((fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat y)) ∘
          fun x => x * y⁻¹) = fun g => F (Formalism.MainNotions.S.umat g) := by
        funext g
        show F (Formalism.MainNotions.S.umat (g * y⁻¹ * y)) = F (Formalism.MainNotions.S.umat g)
        rw [inv_mul_cancel_right]
      rwa [e] at h2
    rw [toL2_eq_zero_of_not_memLp ε hF, toL2_eq_zero_of_not_memLp ε (F := fun x => F (x * Formalism.MainNotions.S.umat y)) hFy,
      map_zero]

theorem toL2_add_smooth (ε : Fin n → Bool) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε (F + G) = toL2 ε F + toL2 ε G := by
  have hFG : MemLp (fun g : Formalism.REAL.UJ ε => (F + G) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    hF.add hG
  rw [toL2_eq_memLp_toLp ε hFG, toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε hG]
  exact MemLp.toLp_add hF hG

theorem toL2_smul_smooth (ε : Fin n → Bool) (c : ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    toL2 ε (c • F) = c • toL2 ε F := by
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hcF : MemLp (fun g : Formalism.REAL.UJ ε => (c • F) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
      hF.const_smul c
    rw [toL2_eq_memLp_toLp ε hcF, toL2_eq_memLp_toLp ε hF]
    exact MemLp.toLp_const_smul c hF
  · by_cases hc : c = 0
    · subst hc
      rw [zero_smul, zero_smul]
      have h0 : MemLp (fun g : Formalism.REAL.UJ ε => (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) (Formalism.MainNotions.S.umat g)) 2
          (Formalism.REAL.muG ε) := MemLp.zero
      rw [toL2_eq_memLp_toLp ε h0]
      exact Lp.ext (h0.coeFn_toLp.trans (Lp.coeFn_zero ..).symm)
    · have hcF : ¬ MemLp (fun g : Formalism.REAL.UJ ε => (c • F) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
        intro h
        apply hF
        have h2 := h.const_smul c⁻¹
        have e : (c⁻¹ • fun g : Formalism.REAL.UJ ε => (c • F) (Formalism.MainNotions.S.umat g)) =
            fun g => F (Formalism.MainNotions.S.umat g) := by
          funext g
          simp only [Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hc]
        rwa [e] at h2
      rw [toL2_eq_zero_of_not_memLp ε hcF, toL2_eq_zero_of_not_memLp ε hF, smul_zero]

theorem inner_toL2_eq_theta_pairing (ε : Fin n → Bool) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    inner ℂ (toL2 ε F) (toL2 ε G) =
      ∫ g : Formalism.REAL.UJ ε, starRingEnd ℂ (F (Formalism.MainNotions.S.umat g)) * G (Formalism.MainNotions.S.umat g) ∂(Formalism.REAL.muG ε) := by
  rw [toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε hG, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with g h1 h2
  simp only [h1, h2, RCLike.inner_apply]
  exact mul_comm _ _

theorem eq_on_unitary_of_toL2_eq (ε : Fin n → Bool) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hFc : ContinuousOn F (UJset ε)) (hGc : ContinuousOn G (UJset ε))
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (h : toL2 ε F = toL2 ε G) : ∀ g ∈ UJset ε, F g = G g := by
  have h' := h
  rw [toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε hG] at h'
  have hae := (MemLp.toLp_eq_toLp_iff hF hG).mp h'
  have hcF : Continuous (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) :=
    hFc.comp_continuous (continuous_unitary_matrix ε) (unitary_matrix_mem_set ε)
  have hcG : Continuous (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) :=
    hGc.comp_continuous (continuous_unitary_matrix ε) (unitary_matrix_mem_set ε)
  haveI : MeasureTheory.Measure.IsOpenPosMeasure (Formalism.REAL.muG ε) := by
    first
    | infer_instance
    | (unfold Formalism.REAL.muG; infer_instance)
  have heq := (Continuous.ae_eq_iff_eq (Formalism.REAL.muG ε) hcF hcG).mp hae
  intro g hg
  obtain ⟨y, rfl⟩ := exists_unitary_preimage ε hg
  exact congrFun heq y

end ReciprocityTheory.ChartRestriction.DS
