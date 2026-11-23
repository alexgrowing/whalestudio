import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformTorusVanishing

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.GIntIw

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_zpow_mul_ord_zero (a : Fˣ) :
    ∃ (m : ℤ) (e : Fˣ), ord (e : F) = 0 ∧ a = unifUnit F ^ m * e := by
  refine ⟨ord (a : F), (unifUnit F ^ ord (a : F))⁻¹ * a, ?_, by group⟩
  have h := ord_units_mul ((unifUnit F ^ ord (a : F))⁻¹) a
  rw [h, ord_units_inv, ord_unifUnit_zpow]
  simp

theorem diag_unit_mem_integral_gl_two {e f : Fˣ} (he : ord (e : F) = 0) (hf : ord (f : F) = 0) :
    Ad3.dg2 e f ∈ GLnLocal.integralGL F 2 := by
  rw [GLnLocal.mem_integralGL_iff]
  have h1 : (e : F) ∈ 𝒪[F] := GlobalTheory.CompanionTheory.RankinTorusVanishing.mem_of_ord_nonneg he.ge
  have h2 : (f : F) ∈ 𝒪[F] := GlobalTheory.CompanionTheory.RankinTorusVanishing.mem_of_ord_nonneg hf.ge
  have h3 : ((e⁻¹ : Fˣ) : F) ∈ 𝒪[F] :=
    GlobalTheory.CompanionTheory.RankinTorusVanishing.mem_of_ord_nonneg (by rw [ord_units_inv, he]; simp)
  have h4 : ((f⁻¹ : Fˣ) : F) ∈ 𝒪[F] :=
    GlobalTheory.CompanionTheory.RankinTorusVanishing.mem_of_ord_nonneg (by rw [ord_units_inv, hf]; simp)
  have h3' : (e : F)⁻¹ ∈ 𝒪[F] := by simpa using h3
  have h4' : (f : F)⁻¹ ∈ 𝒪[F] := by simpa using h4
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg2, h1, h2, h3', h4', zero_mem, one_mem]

theorem iwasawa_decomposition_gl_two :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (g : GL (Fin 2) F), ∃ (x : F) (m n : ℤ), ∃ κ ∈ GLnLocal.integralGL F 2,
        g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ := by
  intro F _ _ _ _ g
  obtain ⟨x, a, d, k, hk, rfl⟩ := GlobalTheory.CompanionTheory.RankinTorusVanishing.exists_iwasawa2 g
  obtain ⟨m, e, he, rfl⟩ := exists_zpow_mul_ord_zero a
  obtain ⟨n, f, hf, rfl⟩ := exists_zpow_mul_ord_zero d
  refine ⟨x, m, n, Ad3.dg2 e f * k,
    (GLnLocal.integralGL F 2).mul_mem (diag_unit_mem_integral_gl_two he hf) hk, ?_⟩
  rw [← GlobalTheory.CompanionTheory.RankinTorusVanishing.diagonal_mul_diagonal_alt]
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.GIntIw
