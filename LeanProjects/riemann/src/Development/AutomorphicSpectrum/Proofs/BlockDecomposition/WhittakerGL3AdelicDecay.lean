import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInvProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxCompactTransposeInvWeyl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTransformProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TrGauge

theorem ti_dg {R : Type*} [CommRing R] (x y z : Rˣ) :
    ti (dg x y z) = dg x⁻¹ y⁻¹ z⁻¹ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ti, dg]

theorem dg_mul {R : Type*} [CommRing R] (x y z x' y' z' : Rˣ) :
    dg x y z * dg x' y' z' = dg (x * x') (y * y') (z * z') := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_three]

theorem longWeyl_mul_diag_GL3 {R : Type*} [CommRing R] (x y z : Rˣ) :
    (w3 : GL (Fin 3) R) * dg x y z = dg z y x * w3 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, w3, Matrix.mul_apply, Fin.sum_univ_three]

theorem rational_sign_diag_adelic : dia dl3 = dg 1 (-1) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dl3, dg]

theorem transposeInv_rational_sign : ti (dia dl3) = dg 1 (-1) 1 := by
  rw [rational_sign_diag_adelic, ti_dg]
  simp

theorem c_mul_dg (x y z : (𝔸[ℚ])ˣ) :
    (w3 : G3) * ti (dia dl3) * dg x y z = dg z y x * ((w3 : G3) * ti (dia dl3)) := by
  rw [transposeInv_rational_sign, mul_assoc, dg_mul, longWeyl_mul_diag_GL3, longWeyl_mul_diag_GL3, ← mul_assoc, dg_mul]
  simp

theorem tr_dg_mul (W : G3 → ℂ) (hW : ∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g) (a b : (𝔸[ℚ])ˣ) (k : G3) :
    tr W (dg (a * b) b 1 * k) = W (dg (b * a) a 1 * ((w3 : G3) * ti (dia dl3) * ti k)) := by
  have hd : dg (a * b)⁻¹ (a * b)⁻¹ (a * b)⁻¹ * dg (b * a) a 1 = dg 1⁻¹ b⁻¹ (a * b)⁻¹ := by
    have e1 : (a * b)⁻¹ * (b * a) = 1⁻¹ := by rw [mul_comm b a, inv_mul_cancel, inv_one]
    have e2 : (a * b)⁻¹ * a = b⁻¹ := by
      rw [mul_inv, mul_comm a⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [dg_mul, e1, e2, mul_one]
  rw [GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic.main.1 W, ← hW (a * b)⁻¹ (dg (b * a) a 1 * _), (GlobalTheory.CompanionTheory.UnfoldingAlt.Ti.ti_alg.1 _ _ _ _).1, ti_dg,
    ← mul_assoc (dg (a * b)⁻¹ (a * b)⁻¹ (a * b)⁻¹), hd, ← mul_assoc ((w3 : G3) * ti (dia dl3)), c_mul_dg,
    inv_one, mul_assoc]

theorem c_ti_mem {k : G3} (hk : k ∈ (maxCompact : Subgroup G3)) :
    (w3 : G3) * ti (dia dl3) * ti k ∈ (maxCompact : Subgroup G3) :=
  mul_mem (mul_mem GlobalTheory.CompanionTheory.UnfoldingAlt.TiK.weyl_delta_ti_maxCompact.1 (GlobalTheory.CompanionTheory.UnfoldingAlt.TiK.weyl_delta_ti_maxCompact.2.2.2.2.1 _ GlobalTheory.CompanionTheory.UnfoldingAlt.TiK.weyl_delta_ti_maxCompact.2.1))
    (GlobalTheory.CompanionTheory.UnfoldingAlt.TiK.weyl_delta_ti_maxCompact.2.2.2.2.1 _ hk)

theorem tr_gauge : ∀ W : G3 → ℂ, (∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g) → (∃ Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact Ω ∧ ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[ℚ])ˣ,
    ∀ k ∈ (maxCompact : Subgroup G3), ∀ w : InfinitePlace ℚ,
      ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b) ^ T /
        ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) ^ N ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[ℚ]).2 ∈ Ω ∧ (b : 𝔸[ℚ]).2 ∈ Ω)) → (∃ Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact Ω ∧ ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[ℚ])ˣ,
    ∀ k ∈ (maxCompact : Subgroup G3), ∀ w : InfinitePlace ℚ,
      ‖(tr W) (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b) ^ T /
        ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) ^ N ∧
      ((tr W) (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[ℚ]).2 ∈ Ω ∧ (b : 𝔸[ℚ]).2 ∈ Ω)) := by
  rintro W hW ⟨Ω, hΩ, T, h⟩
  refine ⟨Ω, hΩ, T, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h N
  refine ⟨C, fun a b k hk w => ?_⟩
  obtain ⟨h1, h2⟩ := hC b a _ (c_ti_mem hk) w
  rw [tr_dg_mul W hW a b k]
  refine ⟨?_, fun hne => (h2 hne).symm⟩
  rw [mul_comm (IdeleGroup.ideleModule ℚ a : ℝ), mul_comm (1 + ‖(a : 𝔸[ℚ]).1 w‖)]
  exact h1

end GlobalTheory.CompanionTheory.UnfoldingAlt.TrGauge
