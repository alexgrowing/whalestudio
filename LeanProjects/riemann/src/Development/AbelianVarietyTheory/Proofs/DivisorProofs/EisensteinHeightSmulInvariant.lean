import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.EisMidHtScale

open GlobalTheory.Doubling (absEv absEw absE_apply absEv_apply absEw_apply unitFin unitInf finite_mulSupport_absEv absE_inclR)
open GlobalTheory.EisMidHt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem normFin_smul (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (U : (Fv F v ⊗[F] E)ˣ)
    (u : Fin n → Fv F v ⊗[F] E) :
    GlobalTheory.EisMidHt.normFin F L v ((U : Fv F v ⊗[F] E) • u) = absEv F E v U * GlobalTheory.EisMidHt.normFin F L v u := by
  have hS : {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • ((U : Fv F v ⊗[F] E) • u) ∈
      latLoc F L v ∧ c = absEv F E v l} = (fun x => absEv F E v U * x) ''
      {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • u ∈ latLoc F L v ∧ c = absEv F E v l} := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨absEv F E v (U⁻¹ * l), ⟨U⁻¹ * l, ?_, rfl⟩, ?_⟩
      · convert hl using 1
        rw [smul_smul, mul_inv_rev, inv_inv, Units.val_mul]
      · show absEv F E v U * absEv F E v (U⁻¹ * l) = absEv F E v l
        rw [← map_mul, mul_inv_cancel_left]
    · rintro ⟨y, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨U * l, ?_, by rw [map_mul]⟩
      convert hl using 1
      rw [smul_smul, ← Units.val_mul, mul_inv_rev, inv_mul_cancel_right]
  unfold GlobalTheory.EisMidHt.normFin
  rw [hS, sInf_image', sInf_eq_iInf', NNReal.mul_iInf]

theorem normInf_smul (a : GL (Fin n) (AF F ⊗[F] E)) (w : InfinitePlace F) (U : (w.Completion ⊗[F] E)ˣ)
    (u : Fin n → w.Completion ⊗[F] E) :
    GlobalTheory.EisMidHt.normInf a w ((U : w.Completion ⊗[F] E) • u) = (absEw F E w U : ℝ) * GlobalTheory.EisMidHt.normInf a w u := by
  unfold GlobalTheory.EisMidHt.normInf
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, ← Finset.mul_sum, norm_mul, mul_pow]
  rw [absEw_apply, NNReal.coe_pow, coe_nnnorm]

theorem eventually_nnnorm_norm_le_one :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y ∈ intLoc F E v, ‖Algebra.norm (Fv F v) y‖₊ ≤ 1 := by
  let b := Module.finBasis F E
  filter_upwards [GlobalTheory.AdelicU.Cofinite.eventually_mem_intLoc_iff_repr b,
    eventually_all.2 fun k => eventually_one_tmul_mem_intLoc (F := F) (b k)] with v hv hb y hy
  let B := Algebra.TensorProduct.basis (Fv F v) b
  have hM : ∀ i j, Algebra.leftMulMatrix B y i j ∈ v.adicCompletionIntegers F := fun i j => by
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    refine (hv _).1 (mul_mem hy ?_) i
    rw [Algebra.TensorProduct.basis_apply]
    exact hb j
  have hdet : (Algebra.leftMulMatrix B y).det ∈ v.adicCompletionIntegers F := by
    rw [Matrix.det_apply]
    exact sum_mem fun σ _ => by
      rw [Units.smul_def]
      exact zsmul_mem (prod_mem fun i _ => hM _ _) _
  rw [Algebra.norm_eq_matrix_det B, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact Valued.toNormedField.norm_le_one_iff.2 hdet

theorem compFin_adVec (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → E) (i : Fin n) :
    compFin F E v (adVec F z i) = (1 : Fv F v) ⊗ₜ[F] z i :=
  show compFin F E v ((1 : AF F) ⊗ₜ[F] z i) = _ from congrArg (· ⊗ₜ[F] z i) (map_one (evFin F v))

theorem finite_mulSupport_normFin (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) (z : Fin n → E)
    (hz : z ≠ 0) :
    (Function.mulSupport fun v => GlobalTheory.EisMidHt.normFin F L v (fun i => compFin F E v (adVec F z i))).Finite := by
  obtain ⟨i0, hi0⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  haveI := hL
  haveI := isLattice_stdLattice (E := E) (n := n)
  have hev : ∀ᶠ v in cofinite, GlobalTheory.EisMidHt.normFin F L v (fun i => compFin F E v (adVec F z i)) = 1 := by
    filter_upwards [eventually_latLoc_eq F L (stdLattice E n),
      eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (z i),
      eventually_one_tmul_mem_intLoc (F := F) (z i0)⁻¹, eventually_nnnorm_norm_le_one (F := F) (E := E)]
      with v h1 h2 h3 h4
    have hu : (fun i => compFin F E v (adVec F z i)) = fun i => (1 : Fv F v) ⊗ₜ[F] z i :=
      funext fun i => compFin_adVec v z i
    rw [hu]
    refine IsLeast.csInf_eq ⟨⟨1, ?_, (map_one _).symm⟩, ?_⟩
    · rw [inv_one, Units.val_one, one_smul, h1, mem_latLoc_stdLattice]
      exact h2
    · rintro _ ⟨l, hl, rfl⟩
      rw [h1, mem_latLoc_stdLattice] at hl
      have h5 : ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v := by
        have := mul_mem (hl i0) h3
        convert this using 1
        rw [Pi.smul_apply, smul_eq_mul, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          mul_inv_cancel₀ hi0, ← Algebra.TensorProduct.one_def, mul_one]
      have h6 : absEv F E v l⁻¹ ≤ 1 := (absEv_apply _ _).trans_le (h4 _ h5)
      have e : absEv F E v l * absEv F E v l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      exact e.symm.le.trans (mul_le_of_le_one_right' h6)
  exact Filter.eventually_cofinite.1 hev

theorem ht_smul_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
      ∀ (μ : E), μ ≠ 0 → ∀ z : Fin n → E,
        GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (μ • z)) = GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F z) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS μ hμ z
  have hL : Submodule.IsLattice E L := hS.2.2.2.2.2.1.lat
  by_cases hz : z = 0
  · subst hz
    rw [smul_zero]
  let P : (AF F ⊗[F] E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 μ hμ)
  have hfin : ∀ v, (fun i => compFin F E v (adVec F (μ • z) i)) =
      ((unitFin F E v P : Fv F v ⊗[F] E)) • (fun i => compFin F E v (adVec F z i)) := fun v => funext fun i => by
    show compFin F E v (inclR (F := F) (AF F) (μ * z i)) =
      compFin F E v (inclR (F := F) (AF F) μ) * compFin F E v (inclR (F := F) (AF F) (z i))
    rw [map_mul, map_mul]
  have hinf : ∀ w, (fun i => compInf F E w (adVec F (μ • z) i)) =
      ((unitInf F E w P : w.Completion ⊗[F] E)) • (fun i => compInf F E w (adVec F z i)) := fun w => funext fun i => by
    show compInf F E w (inclR (F := F) (AF F) (μ * z i)) =
      compInf F E w (inclR (F := F) (AF F) μ) * compInf F E w (inclR (F := F) (AF F) (z i))
    rw [map_mul, map_mul]
  have e1 : ∀ v, (GlobalTheory.EisMidHt.normFin F L v (fun i => compFin F E v (adVec F (μ • z) i)) : ℝ) =
      (absEv F E v (unitFin F E v P) : ℝ) * GlobalTheory.EisMidHt.normFin F L v (fun i => compFin F E v (adVec F z i)) :=
    fun v => by rw [hfin v, normFin_smul, NNReal.coe_mul]
  have e2 : ∀ w, GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (adVec F (μ • z) i)) =
      (absEw F E w (unitInf F E w P) : ℝ) * GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (adVec F z i)) :=
    fun w => by rw [hinf w, normInf_smul]
  have hA : (Function.mulSupport fun v => (absEv F E v (unitFin F E v P) : ℝ)).Finite :=
    (finite_mulSupport_absEv P).subset fun v hv h => hv (by simp [h])
  have hB : (Function.mulSupport fun v =>
      (GlobalTheory.EisMidHt.normFin F L v (fun i => compFin F E v (adVec F z i)) : ℝ)).Finite :=
    (finite_mulSupport_normFin L hL z hz).subset fun v hv h => hv (by simp [h])
  have hP : (∏ w, (absEw F E w (unitInf F E w P) : ℝ)) * ∏ᶠ v, (absEv F E v (unitFin F E v P) : ℝ) = 1 := by
    have h0 := congrArg NNReal.toReal (absE_inclR (F := F) (Units.mk0 μ hμ))
    have hc : ((∏ᶠ v, absEv F E v (unitFin F E v P) : ℝ≥0) : ℝ) = ∏ᶠ v, (absEv F E v (unitFin F E v P) : ℝ) :=
      NNReal.toRealHom.toMonoidHom.map_finprod (finite_mulSupport_absEv P)
    rw [absE_apply, NNReal.coe_mul, NNReal.coe_prod, hc, NNReal.coe_one] at h0
    exact h0
  simp only [GlobalTheory.EisMidHt.ht]
  rw [finprod_congr e1, Finset.prod_congr rfl fun w _ => e2 w, finprod_mul_distrib hA hB, Finset.prod_mul_distrib]
  linear_combination ((∏ᶠ v, (GlobalTheory.EisMidHt.normFin F L v (fun i => compFin F E v (adVec F z i)) : ℝ)) *
    ∏ w, GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (adVec F z i))) * hP

end GlobalTheory.EisMidHtScale
