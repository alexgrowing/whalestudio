import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.LocJEq

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

private theorem isUnit_y_det (τ : D.what₂.Tau) : IsUnit (C.y τ).det := by
  obtain ⟨hQiQ, hQQi, hH, -⟩ := C.isT τ
  have hJJ : Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  generalize Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) = J at hH hJJ
  have hHinv : (C.Qi τ * J * (C.Qi τ)ᴴ) * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = 1 := by
    rw [← hH]
    calc C.Qi τ * J * (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * J * C.Q τ)
        = C.Qi τ * J * (C.Q τ * C.Qi τ)ᴴ * J * C.Q τ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hQQi, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_assoc (C.Qi τ), hJJ, Matrix.mul_one, hQiQ]
  have hy' : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have h1 : (C.Qi τ * J * (C.Qi τ)ᴴ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) * C.y τ = 1 := by
    rw [Matrix.mul_assoc, hy', hHinv]
  exact Matrix.isUnit_det_of_left_inverse h1

private theorem conj_lemma_2 (τ : D.what₂.Tau) (w : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    C.Q τ * (C.Qi τ * w * C.Q τ * (C.y τ)⁻¹) * C.y τ * C.Qi τ = w := by
  obtain ⟨hQiQ, hQQi, -, -⟩ := C.isT τ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQQi, Matrix.one_mul, ← Matrix.mul_assoc (C.y τ)⁻¹ (C.y τ),
    Matrix.nonsing_inv_mul _ (isUnit_y_det C τ), Matrix.one_mul, hQQi, Matrix.mul_one]

private theorem Qi_mul_Q_conj_mul_y_inv_eq (τ : D.what₂.Tau) (x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    C.Qi τ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) * C.Q τ * (C.y τ)⁻¹ = Matrix.of x := by
  obtain ⟨hQiQ, hQQi, -, -⟩ := C.isT τ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Qi τ) (C.Q τ), hQiQ, Matrix.one_mul, ← Matrix.mul_assoc (C.Qi τ) (C.Q τ), hQiQ,
    Matrix.one_mul, Matrix.mul_nonsing_inv _ (isUnit_y_det C τ), Matrix.mul_one]

theorem mem_of_range (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (x : Set.range (Smap C τ γ)) :
    umat γ * (C.Q τ * Matrix.of x.1 * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ)) := by
  obtain ⟨z, hz⟩ := x.2
  rw [← hz]
  unfold Smap
  simp only [Equiv.apply_symm_apply]
  rw [conj_lemma_2 C τ]
  unfold umat UJset
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.mul_inv_cancel_left]
  exact z.2

def smapInv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (x : Set.range (Smap C τ γ)) :
    Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) :=
  ujOf' (umat γ * (C.Q τ * Matrix.of x.1 * C.y τ * C.Qi τ)) (mem_of_range C τ γ x)

theorem smapInv_cont (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Continuous (smapInv C τ γ) := by
  unfold smapInv ujOf'
  apply Continuous.subtype_mk
  have hx : Continuous fun x : Set.range (Smap C τ γ) => (Matrix.of (x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    continuous_subtype_val
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · dsimp only [Function.comp_def]
    fun_prop
  · dsimp only [Units.inv_mk]
    fun_prop

theorem smap_measEmb (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : MeasurableEmbedding (Smap C τ γ) := by
  have hu : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => umat (γ⁻¹ * z) := by
    unfold umat
    exact Units.continuous_val.comp (continuous_subtype_val.comp (continuous_const.mul continuous_id))
  have hc : Continuous (Smap C τ γ) := by
    have h2 : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹ :=
      ((continuous_const.matrix_mul hu).matrix_mul continuous_const).matrix_mul continuous_const
    exact h2
  refine MeasurableEmbedding.of_measurable_inverse_on_range hc.measurable ?_ (smapInv_cont C τ γ).measurable ?_
  · have hS : Set.range (Smap C τ γ) =
        {x | umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))} := by
      ext x
      constructor
      · intro hx
        exact mem_of_range C τ γ ⟨x, hx⟩
      · intro hx
        have hx' : umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ)) := hx
        refine ⟨ujOf' _ hx', ?_⟩
        unfold Smap umat ujOf'
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mk, Units.inv_mul_cancel_left]
        rw [Qi_mul_Q_conj_mul_y_inv_eq C τ]
        simp
    rw [hS]
    apply IsClosed.measurableSet
    have hof : Continuous fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => Matrix.of x := continuous_id
    have hf : Continuous fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) :=
      continuous_const.matrix_mul (((continuous_const.matrix_mul hof).matrix_mul continuous_const).matrix_mul
        continuous_const)
    unfold UJset Formalism.REAL.inUJ
    exact isClosed_eq ((hf.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hf) continuous_const
  · intro z
    apply Subtype.ext
    apply Units.ext
    unfold smapInv ujOf' Set.rangeFactorization Smap
    simp only [Equiv.apply_symm_apply, Units.val_mk]
    rw [conj_lemma_2 C τ]
    unfold umat
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.mul_inv_cancel_left]

variable (hB : WuBessel C)

theorem integrand_S (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of (Smap C τ γ z)))).smulRight
      ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z))) =
      sclOf hB u u' τ • Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z)) := by
  rw [phi'_S, phi_S]
  unfold Formalism.L2.SG.TermOp.rk1
  have hc : (starRingEnd ℂ) (sclOf hB u u' τ) = sclOf hB u u' τ := by
    unfold sclOf
    exact Complex.conj_ofReal _
  change (innerSL ℂ (sclOf hB u u' τ • X.Wloc u' (vOf X τ) (γ⁻¹ * z))).smulRight
      (X.Wloc u (vOf X τ) z) =
    sclOf hB u u' τ • (innerSL ℂ (X.Wloc u' (vOf X τ) (γ⁻¹ * z))).smulRight (X.Wloc u (vOf X τ) z)
  rw [map_smulₛₗ, hc]
  ext v
  simp [smul_smul]

theorem rank_one_continuous {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] {T : Type*} [TopologicalSpace T] {a : T → V} {b : T → V'} (ha : Continuous a)
    (hb : Continuous b) : Continuous fun t => Formalism.L2.SG.TermOp.rk1 (a t) (b t) := by
  unfold Formalism.L2.SG.TermOp.rk1
  have h1 : Continuous fun t => innerSL ℂ (b t) := (innerSL ℂ).continuous.comp hb
  exact (ContinuousLinearMap.smulRightL ℂ V' V).continuous₂.comp₂ h1 ha

theorem integrand_aesm (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) :
    AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Smap C τ γ)) := by
  have hw : ∀ w : D.what₂.Word, Continuous (X.Wloc w (vOf X τ)) := fun w => by
    first
      | exact X.W.Wloc_cont w _
      | exact X.Wloc_cont w _
      | exact X.toWBlk.Wloc_cont w _
  rw [(smap_measEmb C τ γ).aestronglyMeasurable_map_iff]
  have he : (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) ∘ Smap C τ γ =
      fun z => sclOf hB u u' τ •
        Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z)) := by
    funext z
    exact integrand_S C hB u u' τ γ z
  rw [he]
  apply Continuous.aestronglyMeasurable
  exact (rank_one_continuous (hw u) ((hw u').comp (continuous_const.mul continuous_id))).const_smul (sclOf hB u u' τ)

theorem locJ_map_eq' (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) :
    (locS hB u u' τ).J (ν.map (Smap C τ γ)) (trG (C.Q τ) (C.Qi τ) γ) =
      ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) •
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) :=
  locJ_map_eq (C := C) (hB := hB) u u' τ γ ν (integrand_aesm (C := C) (hB := hB) u u' τ γ ν)

end Formalism.L2.SG.Pf.LocJEq
