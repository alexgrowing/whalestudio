import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSet
import GroundTheory.LocalFields.LocalZetaEpsilon
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.SmallSec

theorem ball_char_std {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)
    (hψ : IsStd ψ) (m : ℕ) (a : F) :
    ∫ t, (valBall F (-(m : ℤ)) : Set F).indicator (fun _ => (1 : ℂ)) t * (ψ (t * a) : ℂ)
        ∂selfDualMeasure ψ =
      (((selfDualMeasure ψ).real (valBall F (-(m : ℤ)) : Set F) : ℝ) : ℂ) *
        (valBall F (m : ℤ) : Set F).indicator (fun _ => (1 : ℂ)) a := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have h := localFourier_indicator_valBall (selfDualMeasure ψ) hc h1 (-(m : ℤ)) a
  rw [h0, zero_sub, neg_neg] at h
  exact h

theorem pFT_secFun_of_mem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)
    (hψ : IsStd ψ) (m : ℕ) (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F)
    (hA : A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧ A 1 0 ∈ valBall F (m : ℤ) ∧
      A 1 1 - 1 ∈ valBall F (m : ℤ)) :
    GL2LocalData.pFT ψ (secFun ψ m) A ξ =
      ((((selfDualMeasure ψ).real (valBall F (-(m : ℤ)) : Set F) : ℝ) : ℂ) *
        (valBall F (m : ℤ) : Set F).indicator (fun _ => (1 : ℂ)) (-ξ 0)) *
      ((((selfDualMeasure ψ).real (valBall F (-(m : ℤ)) : Set F) : ℝ) : ℂ) *
        (valBall F (m : ℤ) : Set F).indicator (fun _ => (1 : ℂ)) (1 - ξ 1)) := by
  obtain ⟨a1, a2, a3, a4⟩ := hA
  have e : ∀ y : Fin 2 → F, secFun ψ m (GL2LocalData.cat3 A y) * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) =
      ∏ i : Fin 2, (fun (i : Fin 2) (t : F) =>
        (valBall F (-(m : ℤ)) : Set F).indicator (fun _ => (1 : ℂ)) t *
          (ψ (t * ![-ξ 0, 1 - ξ 1] i) : ℂ)) i (y i) := by
    intro y
    rw [Fin.prod_univ_two]
    by_cases h0 : y 0 ∈ valBall F (-(m : ℤ))
    · by_cases h1 : y 1 ∈ valBall F (-(m : ℤ))
      · have hm : GL2LocalData.cat3 A y ∈ secSet F m := by
          simp only [secSet, GL2LocalData.cat3, Set.mem_setOf_eq]
          simpa using ⟨a1, a2, a3, a4, h0, h1⟩
        have hy : GL2LocalData.cat3 A y 1 2 = y 1 := by simp [GL2LocalData.cat3]
        simp only [secFun, Set.indicator_of_mem hm, hy,
          Set.indicator_of_mem (show y 0 ∈ (valBall F (-(m : ℤ)) : Set F) from h0),
          Set.indicator_of_mem (show y 1 ∈ (valBall F (-(m : ℤ)) : Set F) from h1), one_mul]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 2
        ring
      · have hm : GL2LocalData.cat3 A y ∉ secSet F m := by
          intro h
          apply h1
          simpa [GL2LocalData.cat3] using h.2.2.2.2.2
        simp only [secFun, Set.indicator_of_notMem hm,
          Set.indicator_of_notMem (show y 1 ∉ (valBall F (-(m : ℤ)) : Set F) from h1)]
        simp
    · have hm : GL2LocalData.cat3 A y ∉ secSet F m := by
        intro h
        apply h0
        simpa [GL2LocalData.cat3] using h.2.2.2.2.1
      simp only [secFun, Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (show y 0 ∉ (valBall F (-(m : ℤ)) : Set F) from h0)]
      simp
  unfold GL2LocalData.pFT LFS.vol2
  have key := integral_fintype_prod_eq_prod (μ := fun _ : Fin 2 => selfDualMeasure ψ)
    (fun (i : Fin 2) (t : F) => (valBall F (-(m : ℤ)) : Set F).indicator (fun _ => (1 : ℂ)) t *
      (ψ (t * ![-ξ 0, 1 - ξ 1] i) : ℂ))
  refine (integral_congr_ae (Filter.Eventually.of_forall e)).trans (key.trans ?_)
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ball_char_std ψ hψ, ball_char_std ψ hψ]

theorem pFT_secFun_of_notMem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)
    (m : ℕ) (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F)
    (hA : ¬ (A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧
      A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ))) :
    GL2LocalData.pFT ψ (secFun ψ m) A ξ = 0 := by
  have e : ∀ y : Fin 2 → F, secFun ψ m (GL2LocalData.cat3 A y) * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) = 0 := by
    intro y
    have hm : GL2LocalData.cat3 A y ∉ secSet F m := by
      intro h
      apply hA
      simpa [GL2LocalData.cat3] using (⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩ :
        GL2LocalData.cat3 A y 0 0 - 1 ∈ valBall F (m : ℤ) ∧ GL2LocalData.cat3 A y 0 1 ∈ valBall F (m : ℤ) ∧
        GL2LocalData.cat3 A y 1 0 ∈ valBall F (m : ℤ) ∧ GL2LocalData.cat3 A y 1 1 - 1 ∈ valBall F (m : ℤ))
    simp only [secFun, Set.indicator_of_notMem hm, zero_mul]
  unfold GL2LocalData.pFT
  simp_rw [e]
  simp

theorem pFT_secFun : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (m : ℕ) (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F),
  ((A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧ A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ) ∧ ξ 0 ∈ valBall F (m : ℤ) ∧ ξ 1 - 1 ∈ valBall F (m : ℤ)) → GL2LocalData.pFT ψ (secFun ψ m) A ξ = (((selfDualMeasure ψ).real (valBall F (-(m : ℤ)) : Set F) : ℝ) : ℂ) ^ 2) ∧
  (¬ (A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧ A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ) ∧ ξ 0 ∈ valBall F (m : ℤ) ∧ ξ 1 - 1 ∈ valBall F (m : ℤ)) → GL2LocalData.pFT ψ (secFun ψ m) A ξ = 0) := by
  intro F _ _ _ _ _ _ ψ hψ m A ξ
  have hneg : -ξ 0 ∈ valBall F (m : ℤ) ↔ ξ 0 ∈ valBall F (m : ℤ) := neg_mem_iff
  have hsub : 1 - ξ 1 ∈ valBall F (m : ℤ) ↔ ξ 1 - 1 ∈ valBall F (m : ℤ) := by
    rw [← neg_sub, neg_mem_iff]
  constructor
  · rintro ⟨a1, a2, a3, a4, x0, x1⟩
    rw [pFT_secFun_of_mem ψ hψ m A ξ ⟨a1, a2, a3, a4⟩,
      Set.indicator_of_mem (show -ξ 0 ∈ (valBall F (m : ℤ) : Set F) from hneg.mpr x0),
      Set.indicator_of_mem (show 1 - ξ 1 ∈ (valBall F (m : ℤ) : Set F) from hsub.mpr x1)]
    ring
  · intro h
    by_cases hA : A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧
        A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ)
    · obtain ⟨a1, a2, a3, a4⟩ := hA
      rw [pFT_secFun_of_mem ψ hψ m A ξ ⟨a1, a2, a3, a4⟩]
      by_cases x0 : ξ 0 ∈ valBall F (m : ℤ)
      · have x1 : ξ 1 - 1 ∉ valBall F (m : ℤ) := fun x1 => h ⟨a1, a2, a3, a4, x0, x1⟩
        rw [Set.indicator_of_notMem (show 1 - ξ 1 ∉ (valBall F (m : ℤ) : Set F) from
          fun hx => x1 (hsub.mp hx))]
        simp
      · rw [Set.indicator_of_notMem (show -ξ 0 ∉ (valBall F (m : ℤ) : Set F) from
          fun hx => x0 (hneg.mp hx))]
        simp
    · exact pFT_secFun_of_notMem ψ m A ξ hA

end GlobalTheory.CompanionTheory.SmallSec
