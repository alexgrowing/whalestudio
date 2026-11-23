import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyVariationInequality
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.SphericalWhittakerDualGL2

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem transpose_inv_diagonal_two (p q : Fˣ) : GL2LocalData.tinv (d2 p q) = d2 p⁻¹ q⁻¹ := by
  apply Units.ext
  have hinv : (d2 p q)⁻¹ = d2 p⁻¹ q⁻¹ := by
    apply Units.ext
    rfl
  show ((d2 p q)⁻¹ : GL (Fin 2) F).val.transpose = (d2 p⁻¹ q⁻¹).val
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d2]

theorem long_weyl2_mul_diagonal_two (p q : Fˣ) : (GL2LocalData.w2 : GL (Fin 2) F) * d2 p q = d2 q p * GL2LocalData.w2 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d2, GL2LocalData.w2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_mem_integral : (GL2LocalData.w2 : GL (Fin 2) F) ∈ GLnLocal.integralGL F 2 := by
  refine (GLnLocal.mem_integralGL_iff F 2).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]
  · show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]

theorem exists_unif_eq : ∃ e : 𝒪[F]ˣ, unifUnit F = Iwasawa.uniformizerUnit F * unitsIncl F e := by
  have hw : ord ((Iwasawa.uniformizerUnit F : Fˣ) : F) = 1 :=
    ord_uniformizer (GLnLocal.irreducible_uniformizer F)
  have hu : ord ((unifUnit F : Fˣ) : F) = 1 := by simpa using ord_unifUnit_zpow (K := F) 1
  have hmem : (Iwasawa.uniformizerUnit F)⁻¹ * unifUnit F ∈ (unitsIncl F).range := by
    rw [mem_range_unitsIncl_iff, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
      normalizedValuation_eq_exp_ord (Units.ne_zero _), normalizedValuation_eq_exp_ord (Units.ne_zero _),
      hw, hu]
    exact inv_mul_cancel₀ (by simp)
  obtain ⟨e, he⟩ := hmem
  exact ⟨e, by rw [he]; group⟩

theorem diag_uniformizer_zpow_torus_integral (c d : ℤ) : ∃ k ∈ GLnLocal.integralGL F 2,
    d2 (unifUnit F ^ c) (unifUnit F ^ d) = Iwasawa.torusPow F 2 ![c, d] * k := by
  obtain ⟨e, he⟩ := exists_unif_eq (F := F)
  refine ⟨_, Iwasawa.diagGL_map_mem_integralGL F 2 ![e ^ c, e ^ d], ?_⟩
  apply Units.ext
  have hz : ∀ m : ℤ, ((unifUnit F ^ m : Fˣ) : F) =
      ((Iwasawa.uniformizerUnit F ^ m : Fˣ) : F) * ((unitsIncl F (e ^ m) : Fˣ) : F) := by
    intro m
    rw [he, mul_zpow, map_zpow, Units.val_mul]
  have hc : ∀ m : ℤ, (((e ^ m : 𝒪[F]ˣ) : 𝒪[F]) : F) = ((e : 𝒪[F]) : F) ^ m := by
    intro m
    have h := congrArg Units.val (map_zpow (unitsIncl F) e m)
    rw [Units.val_zpow_eq_zpow_val, coe_unitsIncl, coe_unitsIncl] at h
    exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d2, Iwasawa.torusPow, Iwasawa.diagGL, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hz, hc]

theorem antitone_iff (a b : ℤ) : Antitone (![-b, -a] : Fin 2 → ℤ) ↔ b ≤ a := by
  constructor
  · intro h
    have := h (show (0 : Fin 2) ≤ 1 by decide)
    simpa using this
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem rhoPair_pair (a b : ℤ) : Spherical.rhoPair (![-b, -a] : Fin 2 → ℤ) = a - b := by
  simp [Spherical.rhoPair, Fin.sum_univ_two]
  ring

theorem spherical_whittaker_long_weyl2_transpose_inv (ψ₀ : AddChar F ℂ) (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (y : Fin 2 → ℂˣ) (a b : ℤ) :
    Spherical.sphericalWhittaker ψ₀ y (GL2LocalData.w2 * GL2LocalData.tinv (d2 (unifUnit F ^ a) (unifUnit F ^ b))) =
      if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * Spherical.evalAt y (Spherical.schur ![-b, -a])
      else 0 := by
  obtain ⟨k, hk, hd⟩ := diag_uniformizer_zpow_torus_integral (F := F) (-b) (-a)
  rw [transpose_inv_diagonal_two, long_weyl2_mul_diagonal_two, ← _root_.zpow_neg, ← _root_.zpow_neg, hd,
    Spherical.sphericalWhittaker_mul_right hψ₀ y _ weyl_mem_integral,
    Spherical.sphericalWhittaker_mul_right hψ₀ y _ hk,
    Spherical.sphericalWhittaker_torusPow hψ₀, Spherical.halfModulus_eq, rhoPair_pair]
  simp only [antitone_iff]

end

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (y : Fin 2 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ y (GL2LocalData.w2 * GL2LocalData.tinv (d2 (unifUnit F ^ a) (unifUnit F ^ b))) = if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * Spherical.evalAt y (Spherical.schur ![-b, -a]) else 0 :=
  fun _ _ _ _ _ ψ₀ hψ₀ y a b => spherical_whittaker_long_weyl2_transpose_inv ψ₀ hψ₀ y a b

end GlobalTheory.CompanionTheory.GL2Factorization.SphericalWhittakerDualGL2
