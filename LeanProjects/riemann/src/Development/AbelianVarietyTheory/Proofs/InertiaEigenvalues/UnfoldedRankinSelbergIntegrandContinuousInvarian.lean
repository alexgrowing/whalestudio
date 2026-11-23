import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCellB

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem row_mul_of_mem_NA {ℓ : Fin a} (hℓ : (ℓ : ℕ) + 1 = a) {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a)
    (g : GA E a) : (u * g).val ℓ = g.val ℓ := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  funext j
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single ℓ]
  · rw [h2 ℓ, one_mul]
  · intro k _ hk
    have hlt : k < ℓ := by
      rcases lt_or_gt_of_ne hk with h | h
      · exact h
      · exact absurd k.2 (by have : (ℓ : ℕ) < k := h; omega)
    rw [h1 ℓ k hlt, zero_mul]
  · intro h; exact absurd (Finset.mem_univ ℓ) h

theorem det_of_mem_NA {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) : GeneralLinearGroup.det u = 1 := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_of_upperTriangular (fun i j h => h1 i j h)]
  simp [h2]

end GlobalTheory.RSCellB

namespace GlobalTheory.RSCellB

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem rsPsi_self_mul (ℓ : Fin a) {W : GA E a → ℂ} {u : GA E a} (hW : ∀ g, ‖W (u * g)‖ = ‖W g‖)
    (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (g : GA E a)
    (y : Fin a → Ad E) :
    GlobalTheory.RSTheta.rsPsi ℓ W W Φ J η (u * g) y = GlobalTheory.RSTheta.rsPsi ℓ W W Φ J η g y := by
  simp only [GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, mul_assoc u g, hW]

theorem bInt_continuous_invariant_finite : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E),
    Continuous (GlobalTheory.JSW.whit F) → (∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    Continuous (fun p : ℝ × GA E a => GlobalTheory.RSCell.bInt ℓ F Φ J η p.1 p.2) ∧
      (∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, GlobalTheory.RSCell.bInt ℓ F Φ J η x (u * g) = GlobalTheory.RSCell.bInt ℓ F Φ J η x g) ∧
      ∀ x g, GlobalTheory.RSCell.bInt ℓ F Φ J η x g ≠ ⊤ := by
  intro E _ _ _ a ℓ hℓ F Φ J η hWc hWu hΦc hΦs
  have hdet : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Continuous fun p : ℝ × GA E a => (p.2, p.2.val ℓ) :=
      continuous_snd.prodMk ((continuous_apply ℓ).comp ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Ad E))).comp continuous_snd))
    have h2 := (GlobalTheory.RSTheta.continuous_rsPsi hWc hWc hΦc hΦs J η).comp h1
    have h3 : Continuous fun p : ℝ × GA E a => (ideleModule E (GeneralLinearGroup.det p.2) : ℝ) ^ p.1 :=
      (hdet.comp continuous_snd).rpow continuous_fst fun p => Or.inl (ideleModule E (GeneralLinearGroup.det p.2)).2.ne'
    exact h2.enorm.ennreal_mul (ENNReal.continuous_ofReal.comp h3) (fun _ => Or.inr ENNReal.ofReal_ne_top)
      (fun _ => Or.inr enorm_ne_top)
  · intro x u hu g
    simp only [GlobalTheory.RSCell.bInt, row_mul_of_mem_NA hℓ hu, map_mul, det_of_mem_NA hu, one_mul]
    rw [rsPsi_self_mul ℓ (hWu u hu)]
  · intro x g
    exact ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top

end GlobalTheory.RSCellB

end
