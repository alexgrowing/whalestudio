import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureTensorDecompositionLocal
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.FourierPlane

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def ft2 (ψ : AddChar F Circle) (φ : (Fin 2 → F) → ℂ) (ξ : Fin 2 → F) : ℂ :=
  ∫ y, φ y * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ

theorem integral_plane_measure_eq_prod (ψ : AddChar F Circle) (f : (Fin 2 → F) → ℂ) :
    ∫ y, f y ∂LFS.vol2 ψ =
      ∫ p : F × F, f ![p.1, p.2] ∂(selfDualMeasure ψ).prod (selfDualMeasure ψ) :=
  ((measurePreserving_finTwoArrow (selfDualMeasure ψ)).symm.integral_comp' f).symm

theorem inv_one {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {f : F → ℂ}
    (hf : f ∈ schwartzBruhat F) (z : F) :
    Integrable (fun u => localFourier (selfDualMeasure ψ) ψ f (-u) * (ψ (u * z) : ℂ)) (selfDualMeasure ψ) ∧
      ∫ u, localFourier (selfDualMeasure ψ) ψ f (-u) * (ψ (u * z) : ℂ) ∂selfDualMeasure ψ = f z := by
  have hT := localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hψ hψ1 hf
  have hI := integrable_mul_char_of_mem_schwartzBruhat (selfDualMeasure ψ) hψ hT (-z)
  have e : (fun u => localFourier (selfDualMeasure ψ) ψ f (-u) * (ψ (u * z) : ℂ)) =
      fun u => (fun v => localFourier (selfDualMeasure ψ) ψ f v * (ψ (v * (-z)) : ℂ)) (-u) := by
    funext u
    simp only [neg_mul_neg]
  rw [e]
  refine ⟨hI.comp_neg, ?_⟩
  rw [integral_neg_eq_self (fun v => localFourier (selfDualMeasure ψ) ψ f v * (ψ (v * (-z)) : ℂ))]
  have h := localFourier_localFourier_selfDual hψ hψ1 hf (-z)
  rw [neg_neg] at h
  exact h

theorem fourier_plane_product_sum {ψ : AddChar F Circle} (hψ : Continuous ψ) {n : ℕ} {f g : Fin n → F → ℂ}
    (hf : ∀ i, f i ∈ schwartzBruhat F) (hg : ∀ i, g i ∈ schwartzBruhat F) (ξ : Fin 2 → F) :
    ft2 ψ (fun y => ∑ i, f i (y 0) * g i (y 1)) ξ =
      ∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1) := by
  have e : ∀ p : F × F, (∑ i, f i p.1 * g i p.2) * (ψ (-(ξ 0 * p.1 + ξ 1 * p.2)) : ℂ) =
      ∑ i, (f i p.1 * (ψ (p.1 * -ξ 0) : ℂ)) * (g i p.2 * (ψ (p.2 * -ξ 1) : ℂ)) := by
    intro p
    have hc : (ψ (-(ξ 0 * p.1 + ξ 1 * p.2)) : ℂ) = (ψ (p.1 * -ξ 0) : ℂ) * (ψ (p.2 * -ξ 1) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [hc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold ft2
  rw [integral_plane_measure_eq_prod]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e]
  rw [integral_finsetSum _ fun i _ => Integrable.mul_prod
    (integrable_mul_char_of_mem_schwartzBruhat _ hψ (hf i) (-ξ 0))
    (integrable_mul_char_of_mem_schwartzBruhat _ hψ (hg i) (-ξ 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_prod_mul (fun x => f i x * (ψ (x * -ξ 0) : ℂ)) (fun x => g i x * (ψ (x * -ξ 1) : ℂ))

theorem inv_sum {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} {f g : Fin n → F → ℂ}
    (hf : ∀ i, f i ∈ schwartzBruhat F) (hg : ∀ i, g i ∈ schwartzBruhat F) (z : Fin 2 → F) :
    ∫ ξ : Fin 2 → F, (∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1)) * (ψ (ξ 0 * z 0 + ξ 1 * z 1) : ℂ) ∂LFS.vol2 ψ =
      ∑ i, f i (z 0) * g i (z 1) := by
  have e : ∀ p : F × F, (∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-p.1) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-p.2)) * (ψ (p.1 * z 0 + p.2 * z 1) : ℂ) =
      ∑ i, (localFourier (selfDualMeasure ψ) ψ (f i) (-p.1) * (ψ (p.1 * z 0) : ℂ)) *
        (localFourier (selfDualMeasure ψ) ψ (g i) (-p.2) * (ψ (p.2 * z 1) : ℂ)) := by
    intro p
    rw [AddChar.map_add_eq_mul, Circle.coe_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_plane_measure_eq_prod]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e]
  rw [integral_finsetSum _ fun i _ => Integrable.mul_prod
    (inv_one hψ hψ1 (hf i) (z 0)).1 (inv_one hψ hψ1 (hg i) (z 1)).1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_prod_mul (fun u => localFourier (selfDualMeasure ψ) ψ (f i) (-u) * (ψ (u * z 0) : ℂ))
    (fun u => localFourier (selfDualMeasure ψ) ψ (g i) (-u) * (ψ (u * z 1) : ℂ)),
    (inv_one hψ hψ1 (hf i) (z 0)).2, (inv_one hψ hψ1 (hg i) (z 1)).2]

omit [MeasurableSpace F] [BorelSpace F] in

theorem pure_mem {a b : F → ℂ} (ha : a ∈ schwartzBruhat F) (hb : b ∈ schwartzBruhat F) :
    (fun x : Fin 2 → F => a (x 0) * b (x 1)) ∈ GodementSectionLocal.schwartzBruhat2 F := by
  refine GodementSectionLocal.mem_schwartzBruhat2.2
    ⟨(ha.1.comp_continuous (continuous_apply 0)).mul (hb.1.comp_continuous (continuous_apply 1)), ?_⟩
  refine HasCompactSupport.intro
    ((ha.2.isCompact.prod hb.2.isCompact).image (Homeomorph.finTwoArrow (X := F)).symm.continuous) fun x hx => ?_
  by_contra hne
  refine hx ⟨(x 0, x 1), ⟨subset_tsupport _ fun h => hne ?_, subset_tsupport _ fun h => hne ?_⟩, ?_⟩
  · simp [h]
  · simp [h]
  · ext j
    fin_cases j <;> simp

omit [MeasurableSpace F] [BorelSpace F] in

theorem reflect_mem {a : F → ℂ} (ha : a ∈ schwartzBruhat F) : (fun x => a (-x)) ∈ schwartzBruhat F :=
  ⟨ha.1.comp_continuous continuous_neg, ha.2.comp_homeomorph (Homeomorph.neg F)⟩

omit [MeasurableSpace F] [BorelSpace F] in

theorem exists_pure {φ : (Fin 2 → F) → ℂ} (hφ : φ ∈ GodementSectionLocal.schwartzBruhat2 F) :
    ∃ (n : ℕ) (f g : Fin n → F → ℂ), (∀ i, f i ∈ schwartzBruhat F) ∧ (∀ i, g i ∈ schwartzBruhat F) ∧
      φ = fun y => ∑ i, f i (y 0) * g i (y 1) := by
  have hl : IsLocallyConstant fun p : F × F => φ ((Homeomorph.finTwoArrow (X := F)).symm p) :=
    hφ.1.comp_continuous (Homeomorph.finTwoArrow (X := F)).symm.continuous
  have hc : HasCompactSupport fun p : F × F => φ ((Homeomorph.finTwoArrow (X := F)).symm p) :=
    hφ.2.comp_homeomorph (Homeomorph.finTwoArrow (X := F)).symm
  obtain ⟨n, f, g, hf, hg, hfg⟩ := GlobalTheory.CompanionTheory.PureTensor.exists_pure_sum hl hc
  refine ⟨n, f, g, hf, hg, ?_⟩
  funext y
  rw [← hfg]
  congr 1
  ext j
  fin_cases j <;> rfl

theorem fourier_inversion_plane_explicit : ForS fun F _ _ _ _ _ _ ψ => ∀ φ : (Fin 2 → F) → ℂ,
    φ ∈ GodementSectionLocal.schwartzBruhat2 F →
    (fun ξ : Fin 2 → F => ∫ y, φ y * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ) ∈
        GodementSectionLocal.schwartzBruhat2 F ∧
      ∀ z : Fin 2 → F, ∫ ξ : Fin 2 → F, (∫ y, φ y * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ) *
        (ψ (ξ 0 * z 0 + ξ 1 * z 1) : ℂ) ∂LFS.vol2 ψ = φ z := by
  intro F _ _ _ _ _ _ ψ hstd φ hφ
  have hψ : Continuous ψ := hstd.1
  have hψ1 : ψ ≠ 1 := hstd.2.1
  obtain ⟨n, f, g, hf, hg, rfl⟩ := exists_pure hφ
  have e : (fun ξ : Fin 2 → F => ∫ y, (∑ i, f i (y 0) * g i (y 1)) *
      (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ) =
      fun ξ => ∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1) :=
    funext fun ξ => fourier_plane_product_sum hψ hf hg ξ
  refine ⟨?_, fun z => ?_⟩
  · rw [e]
    have : (fun ξ : Fin 2 → F => ∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1)) =
        ∑ i, fun ξ : Fin 2 → F => localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
          localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1) := by
      funext ξ
      simp
    rw [this]
    exact Submodule.sum_mem _ fun i _ => pure_mem
      (reflect_mem (localFourier_mem_schwartzBruhat _ hψ hψ1 (hf i)))
      (reflect_mem (localFourier_mem_schwartzBruhat _ hψ hψ1 (hg i)))
  · have := inv_sum hψ hψ1 hf hg z
    simp only [← congrFun e] at this
    exact this

end GlobalTheory.CompanionTheory.FourierPlane
