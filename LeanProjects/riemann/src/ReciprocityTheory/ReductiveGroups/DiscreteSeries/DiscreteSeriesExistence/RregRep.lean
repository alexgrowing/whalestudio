import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SquareIntegrableInnerProduct

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rregRep_umat_inj (ε : Fin n → Bool) {x y : Formalism.REAL.UJ ε}
    (h : Formalism.MainNotions.S.umat x = Formalism.MainNotions.S.umat y) : x = y := Subtype.ext (Units.ext h)

theorem rregRep_rreg_umat (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) :
    rreg ε (Formalism.MainNotions.S.umat y) = rregG ε y := by
  have h : ∃ y' : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y' = Formalism.MainNotions.S.umat y := ⟨y, rfl⟩
  rw [rreg, dif_pos h]
  exact congrArg (rregG ε) (rregRep_umat_inj ε h.choose_spec)

theorem rregRep_rregG_apply (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (f : L2 ε) :
    rregG ε y f = Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y)
      (measurePreserving_mul_right ε y) f := by
  rw [rregG, dif_pos (measurePreserving_mul_right ε y)]
  rfl

private theorem Jm_mul_selfDiscreteSeriesExistence (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : ε i <;> simp [h]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

private theorem Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  rw [Matrix.mul_assoc] at hg'
  simp only [Matrix.mul_assoc]
  rw [hg', Jm_mul_selfDiscreteSeriesExistence]

private theorem mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
  have hl := Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg
  first
  | exact mul_eq_one_comm.mp hl
  | (rw [← Matrix.inv_eq_left_inv hl]
     exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl))

theorem rregRep_range (ε : Fin n → Bool) :
    Set.range (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) = UJset ε := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hg
    exact ⟨⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε hg,
      Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg⟩, hg⟩, rfl⟩

theorem rregRep_mem (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g := by
  have h2 : g ∈ Set.range (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) := by
    rw [rregRep_range ε]
    exact hg
  obtain ⟨y, hy⟩ := h2
  exact ⟨y, hy⟩

theorem rregRep_one (ε : Fin n → Bool) : rreg ε 1 = 1 := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) := rfl
  rw [h1, rregRep_rreg_umat]
  ext1 f
  rw [rregRep_rregG_apply, ContinuousLinearMap.one_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε 1)] with x hx
  rw [hx]
  simp

theorem rregRep_mul (ε : Fin n → Bool) (a b : Formalism.REAL.UJ ε) :
    rregG ε (a * b) = (rregG ε a).comp (rregG ε b) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply, rregRep_rregG_apply, rregRep_rregG_apply,
    rregRep_rregG_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε (a * b)),
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * b)
        (measurePreserving_mul_right ε b) f) (measurePreserving_mul_right ε a),
    (measurePreserving_mul_right ε a).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε b))] with x h1 h2 h3
  simp only [Function.comp_apply] at h1 h2 h3 ⊢
  rw [h1, h2, h3, mul_assoc]

theorem rregRep_cont (ε : Fin n → Bool) (v : L2 ε) :
    Continuous (fun y : Formalism.REAL.UJ ε => rregG ε y v) := by
  haveI : SMulInvariantMeasure (Formalism.REAL.UJ ε)ᵐᵒᵖ (Formalism.REAL.UJ ε) (Formalism.REAL.muG ε) := by
    refine ⟨fun c s hs => ?_⟩
    first
    | exact (measurePreserving_mul_right ε c.unop).measure_preimage hs.nullMeasurableSet
    | exact (measurePreserving_mul_right ε c.unop).measure_preimage hs
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by first | simp | exact ENNReal.ofNat_ne_top⟩
  have he : (fun y : Formalism.REAL.UJ ε => rregG ε y v) =
      fun y => (DomMulAct.mk (MulOpposite.op y)) • v := by
    funext y
    rw [rregRep_rregG_apply]
    rfl
  rw [he]
  have hm : Continuous (fun y : Formalism.REAL.UJ ε => DomMulAct.mk (MulOpposite.op y)) := by
    first
    | exact DomMulAct.continuous_mk.comp MulOpposite.continuous_op
    | exact DomMulAct.mkHomeomorph.continuous.comp MulOpposite.continuous_op
    | fun_prop
  haveI : OpensMeasurableSpace (Formalism.REAL.UJ ε)ᵐᵒᵖ :=
    ⟨MeasurableSpace.generateFrom_le fun s hs =>
      (IsOpen.preimage MulOpposite.continuous_op hs).measurableSet⟩
  exact hm.smul continuous_const

theorem rreg_isURepOn (ε : Fin n → Bool) : IsURepOn (UJset ε) (rreg ε) := by
  unfold IsURepOn
  refine ⟨⟨rregRep_one ε, ?_⟩, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨ya, rfl⟩ := rregRep_mem ε ha
    obtain ⟨yb, rfl⟩ := rregRep_mem ε hb
    have hab : Formalism.MainNotions.S.umat ya * Formalism.MainNotions.S.umat yb = Formalism.MainNotions.S.umat (ya * yb) := rfl
    rw [hab, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_mul]
  · intro g hg v
    obtain ⟨y, rfl⟩ := rregRep_mem ε hg
    rw [rregRep_rreg_umat, rregRep_rregG_apply]
    exact Lp.norm_compMeasurePreserving v _
  · intro v
    obtain ⟨φ, hφc, hφ⟩ : ∃ φ : UJset ε → Formalism.REAL.UJ ε, Continuous φ ∧
        ∀ g : UJset ε, Formalism.MainNotions.S.umat (φ g) = g :=
      ⟨fun g => ⟨⟨(g : Matrix (Fin n) (Fin n) ℂ),
          Formalism.REAL.Jm ε * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε,
          mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε g.2, Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε g.2⟩, g.2⟩,
        by
          apply Continuous.subtype_mk
          rw [Units.continuous_iff]
          constructor
          · exact continuous_subtype_val
          · exact (continuous_const.mul continuous_subtype_val.matrix_conjTranspose).mul
              continuous_const,
        fun g => rfl⟩
    have he : ∀ g : UJset ε, rreg ε (g : Matrix (Fin n) (Fin n) ℂ) v = rregG ε (φ g) v := by
      intro g
      rw [← hφ g, rregRep_rreg_umat]
    rw [continuousOn_iff_continuous_restrict]
    convert (rregRep_cont ε v).comp hφc using 1
    funext g
    exact he g

end ReciprocityTheory.ChartRestriction.DS
