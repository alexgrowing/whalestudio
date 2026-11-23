import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.MaximalCompactGL2FiniteAdeleCharacterization
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.FiniteNarrowIdeleClassesAndUnitsModSquares
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsDifferentGeneratorTotallyPositiveTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.Reps

variable {F : Type} [Field F] [NumberField F]

theorem aff_mul_aff {R : Type} [CommRing R] (a b : Rˣ) : aff a 0 * aff b 0 = aff (a * b) (0 : R) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

theorem toFin_aff (η : Fˣ) : toFin (aff η 0) = aff (Units.map (algebraMap F (Af F)).toMonoidHom η) 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toFin, aff]

theorem det_aff' {R : Type} [CommRing R] (y : Rˣ) (x : R) : Matrix.GeneralLinearGroup.det (aff y x) = y := by
  ext
  simp [aff, Matrix.det_fin_two]

theorem exists_sl_aff (K : Subgroup (GL (Fin 2) (Af F)))
    (hK : IsOpen (K : Set (GL (Fin 2) (Af F)))) (g : GL (Fin 2) (Af F)) :
    ∃ (σ : GL (Fin 2) F) (y : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ K ∧ Matrix.GeneralLinearGroup.det σ = 1 ∧
      g = toFin σ * (aff y 0 * u) := by
  set y := Matrix.GeneralLinearGroup.det g with hy
  have hs : g * (aff y 0)⁻¹ ∈ GroundTheory.Automorphic.AdelicGLn.finiteSL F 2 := by
    rw [GroundTheory.Automorphic.AdelicGLn.mem_finiteSL, map_mul, map_inv, det_aff', hy, mul_inv_cancel]
  have hcl := GroundTheory.Automorphic.AdelicGLn.finiteSL_le_topologicalClosure F 2 hs
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hcl
  have ho : IsOpen {s : GL (Fin 2) (Af F) | (aff y 0)⁻¹ * s⁻¹ * g ∈ K} :=
    hK.preimage (f := fun s : GL (Fin 2) (Af F) => (aff y 0)⁻¹ * s⁻¹ * g) ((continuous_const.mul continuous_inv).mul continuous_const)
  obtain ⟨_, hu, σ, hσ, rfl⟩ := mem_closure_iff.1 hcl _ ho (by
    rw [Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_left, inv_mul_cancel]; exact one_mem K)
  refine ⟨σ, y, _, hu, hσ, ?_⟩
  rw [mul_assoc, mul_inv_cancel_left]
  exact (mul_inv_cancel_left _ g).symm

variable [IsTotallyReal F]

theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply, Complex.ofReal_re]

theorem TP_mul {x y : F} (hx : TP x) (hy : TP y) : TP (x * y) := fun v => by
  have := mul_pos (hx v) (hy v)
  rw [reAt_eq, reAt_eq] at this; rw [reAt_eq, map_mul]; exact this

theorem TP_inv {x : F} (hx : TP x) : TP x⁻¹ := fun v => by
  have := inv_pos.2 (hx v)
  rw [reAt_eq] at this; rw [reAt_eq, map_inv₀]; exact this

end GlobalTheory.HilbertThetaSeries.Reps

open GlobalTheory.HilbertThetaSeries.Reps in
theorem GlobalTheory.HilbertThetaSeries.finite_reps : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∃ Y : Finset (Af F)ˣ, (∀ y ∈ Y, AtP p δ y) ∧ ∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u := by
  intro F _ _ _ p hp δ hδ
  classical
  obtain ⟨Y0, hY0⟩ := (GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares F).1
  choose ξf hξf using (GlobalTheory.T.exists_different_generator_totallyPositive_translate F p hp).2 δ hδ
  set ι := Units.map (algebraMap F (Af F)).toMonoidHom with hι
  refine ⟨Y0.image (fun y => ι (ξf y) * y), ?_, ?_⟩
  · intro z hz
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
    exact (hξf y).2
  · intro g
    obtain ⟨σ, y, u, hu, hσ, e⟩ := exists_sl_aff (KLev F 2 1) (isOpen_KLev le_rfl) g
    obtain ⟨y0, hy0, ξ, u0, hξ, hu0, hy⟩ := hY0 y
    have hK := (GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.1 u0 0 hu0 (fun w => by simp)
    refine ⟨aff (ξ⁻¹ * ξf y0) 0 * σ⁻¹, ?_, ι (ξf y0) * y0, Finset.mem_image_of_mem _ hy0, aff u0 0 * u, mul_mem hK.1 hu, ?_⟩
    · have hd : (aff (ξ⁻¹ * ξf y0) 0 * σ⁻¹ : GL (Fin 2) F).val.det = ((ξ⁻¹ * ξf y0 : Fˣ) : F) := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_inv, hσ, det_aff', inv_one, mul_one]
      rw [hd, Units.val_mul]
      exact TP_mul (by simpa using TP_inv hξ) (hξf y0).1
    · rw [e, map_mul, map_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel_right, toFin_aff, ← mul_assoc, aff_mul_aff, aff_mul_aff, hy]
      congr 2
      simp only [map_mul, map_inv, hι]
      generalize (Units.map (algebraMap F (Af F)).toMonoidHom) ξ = a
      generalize (Units.map (algebraMap F (Af F)).toMonoidHom) (ξf y0) = b
      rw [mul_comm a⁻¹ b, mul_assoc b, ← mul_assoc a⁻¹, ← mul_assoc a⁻¹, inv_mul_cancel, one_mul, ← mul_assoc]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl2_adelic_double_coset_decomposition_totally_real : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∃ Y : Finset (Af F)ˣ, (∀ y ∈ Y, AtP p δ y) ∧ ∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u := by
  first | exact @GlobalTheory.HilbertThetaSeries.finite_reps | exact GlobalTheory.HilbertThetaSeries.finite_reps | (intros; apply GlobalTheory.HilbertThetaSeries.finite_reps <;> assumption)
