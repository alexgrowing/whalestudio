import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NomePowerSeriesDvdOfSumBoundedStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcReg

theorem valR_eq_ev {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = ev x U h f := by
  rw [valR, dif_pos h]; rfl

theorem not_pole_of_bounded : ∀ (X : Scheme.{0}) (U₀ W₀ : X.Opens) (f₀ : Γ(X, W₀)) (χ : Sp (PowerSeries ℂ) ⟶ X) (y : ℂ → (Sp ℂ ⟶ X)), IsAffineOpen U₀ → W₀ ≤ U₀ → ⊤ ≤ χ ⁻¹ᵁ U₀ → (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ⊤ ≤ y w ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (y w) U f)) → (∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ hy : ⊤ ≤ y w ⁻¹ᵁ W₀, ‖ev (y w) W₀ hy f₀‖ ≤ C) → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range := by
  intro X U₀ W₀ f₀ χ y hU₀ hWU hχ harc hbd h
  have hηW : (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) (default : PrimeSpectrum (LaurentSeries ℂ)) ∈ W₀ :=
    h trivial
  obtain ⟨s, hsW, hsη⟩ := hU₀.exists_basicOpen_le (V := W₀) ⟨_, hηW⟩ (hWU hηW)
  obtain ⟨n, t, ht⟩ := exists_eq_pow_mul_of_isAffineOpen X U₀ hU₀ s
    ((X.presheaf.map (homOfLE hsW).op).hom f₀)
  have hsU : X.basicOpen s ≤ U₀ := X.basicOpen_le s

  have key : ∀ (A : Type) [CommRing A] (z : Sp A ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ X.basicOpen s),
      valR z U₀ (t * s) = valR z U₀ (s ^ (n + 1)) * valR z W₀ f₀ := by
    intro A _ z hz
    have hzU : ⊤ ≤ z ⁻¹ᵁ U₀ := GlobalTheory.FlagMod.le_preimage_mono hsU hz
    have e := congrArg (GlobalTheory.HolHom.evalHom z _ hz) ht
    rw [map_mul, map_pow] at e
    simp only [← GlobalTheory.HolHom.valR_eq z _ hz] at e
    erw [GlobalTheory.HolHom.valR_res z hsU t hz, GlobalTheory.HolHom.valR_res z hsU s hz, GlobalTheory.HolHom.valR_res z hsW f₀ hz] at e
    rw [GlobalTheory.HolHom.valR_eq z U₀ hzU, GlobalTheory.HolHom.valR_eq z U₀ hzU, map_mul, map_pow,
      ← GlobalTheory.HolHom.valR_eq z U₀ hzU, ← GlobalTheory.HolHom.valR_eq z U₀ hzU, e]
    ring

  have hηs : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ X.basicOpen s := fun p _ => by
    obtain rfl : p = (default : PrimeSpectrum (LaurentSeries ℂ)) := Subsingleton.elim _ _
    exact hsη
  have hηU : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ U₀ := GlobalTheory.FlagMod.le_preimage_mono hsU hηs
  have hu : IsUnit (HahnSeries.ofPowerSeries ℤ ℂ (valR χ U₀ (s ^ (n + 1)))) := by
    rw [← GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, GlobalTheory.HolHom.valR_eq _ U₀ hηU, map_pow, ← GlobalTheory.HolHom.valR_eq _ U₀ hηU]
    exact ((GlobalTheory.ArcLie.le_basicOpen_iff_isUnit _ hηU s).1 hηs).pow _
  have kη := key _ _ hηs
  rw [GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, valR_eq_ev _ W₀ h] at kη
  have hH : valR χ U₀ (s ^ (n + 1)) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨T₁, h₁⟩ := harc U₀ (t * s) hχ
  obtain ⟨T₂, h₂⟩ := harc U₀ (s ^ (n + 1)) hχ
  obtain ⟨T₃, C, h₃⟩ := hbd
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.nomePowerSeries_dvd_of_sum_bounded (valR χ U₀ (t * s)) (valR χ U₀ (s ^ (n + 1))) (max T₁ (max T₂ T₃)) C
    (fun w => valAt' (y w) U₀ (t * s)) (fun w => valAt' (y w) U₀ (s ^ (n + 1))) hH (fun w hw => by
      have hw1 : T₁ < w.im := lt_of_le_of_lt (le_max_left _ _) hw
      have hw2 : T₂ < w.im := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hw
      have hw3 : T₃ < w.im := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hw
      obtain ⟨hyU, hG⟩ := h₁ w hw1
      obtain ⟨-, hH'⟩ := h₂ w hw2
      refine ⟨hG, hH', fun hne => ?_⟩
      have hys : ⊤ ≤ y w ⁻¹ᵁ X.basicOpen s := by
        rw [GlobalTheory.HolHom.le_basicOpen_iff (y w) hyU s]
        intro h0
        apply hne
        rw [GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_eq _ _ hyU, map_pow]
        rw [GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_eq _ _ hyU] at h0
        rw [h0, zero_pow (Nat.succ_ne_zero n)]
      have hyW : ⊤ ≤ y w ⁻¹ᵁ W₀ := GlobalTheory.FlagMod.le_preimage_mono hsW hys
      show ‖valR (y w) U₀ (t * s)‖ ≤ C * ‖valR (y w) U₀ (s ^ (n + 1))‖
      rw [key ℂ (y w) hys, valR_eq_ev (y w) W₀ hyW, norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (h₃ w hw3 hyW) (norm_nonneg _))
  rw [hQ, map_mul] at kη
  exact ⟨Q, hu.mul_left_cancel kη⟩

end GlobalTheory.ArcReg
