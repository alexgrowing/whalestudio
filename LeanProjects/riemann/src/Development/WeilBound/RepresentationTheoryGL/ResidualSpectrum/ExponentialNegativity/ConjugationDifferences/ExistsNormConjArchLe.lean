import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel

open Set Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section

namespace PositivityTheory.Rg.Rs.diffstep

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem conjArch_mul_right {r : ℕ} (y q : AdelicGLn.AdelicGL K n) (P : UPos n r → 𝔸[K]) :
    conjArch K n (y * q) P =
      archMat K n ((q⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * conjArch K n y P *
        archMat K n (q : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  have h : (((y * q)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry P *
      ((y * q : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ((q⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        (((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry P *
          (y : Matrix (Fin n) (Fin n) 𝔸[K])) * (q : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    rw [_root_.mul_inv_rev]
    simp only [Units.val_mul, Matrix.mul_assoc]
  change archMat K n _ = archMat K n _ * archMat K n _ * archMat K n _
  rw [h, map_mul, map_mul]

theorem exists_norm_conjArch_le {ω Q : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)))
    (hQ : IsCompact Q) {t : ℝ} (ht : 0 < t) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    {𝒮 : Set (InfiniteAdeleRing K)} (h𝒮 : IsCompact 𝒮) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ q ∈ Q, ∀ P : UPos n r → 𝔸[K], (∀ p, (P p).2 = 0) → (∀ p, (P p).1 ∈ 𝒮) →
        ‖conjArch K n (b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * q) P‖ ≤
          C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_archMat_conj_le hω hωB ht hr hrn h𝒮
  obtain ⟨c1, hc1⟩ := hQ.exists_bound_of_continuousOn
    (f := fun k : AdelicGLn.AdelicGL K n => archMat K n (k : Matrix (Fin n) (Fin n) 𝔸[K]))
    (continuous_archMat.comp Units.continuous_val).continuousOn
  obtain ⟨c2, hc2⟩ := hQ.exists_bound_of_continuousOn
    (f := fun k : AdelicGLn.AdelicGL K n =>
      archMat K n ((k⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))
    (continuous_archMat.comp Units.continuous_coe_inv).continuousOn
  set c := max (max c1 c2) 0
  have hc0 : 0 ≤ c := le_max_right _ _
  set C₁' := max C₁ 0
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  refine ⟨c * C₁' * c, by positivity, ?_⟩
  intro b hb ρ hρ hsieg q hq P hP2 hP1
  set a := diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i))
  set s := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩
  have hs : 0 ≤ s := div_nonneg (hρ _).le (hρ _).le
  have h1 := hC₁ b hb ρ hρ hsieg 1 (maxCompact (K := K) (n := n)).one_mem P hP2 hP1
  rw [mul_one] at h1
  have hY : ‖conjArch K n (b * a) P‖ ≤ C₁' * s :=
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hs)
  have hq1 : ‖archMat K n (q : Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤ c :=
    (hc1 q hq).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hq2 : ‖archMat K n ((q⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤ c :=
    (hc2 q hq).trans ((le_max_right _ _).trans (le_max_left _ _))
  rw [conjArch_mul_right]
  calc ‖archMat K n ((q⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        conjArch K n (b * a) P * archMat K n (q : Matrix (Fin n) (Fin n) 𝔸[K])‖
      ≤ ‖archMat K n ((q⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ *
          ‖conjArch K n (b * a) P‖ * ‖archMat K n (q : Matrix (Fin n) (Fin n) 𝔸[K])‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ c * (C₁' * s) * c := by gcongr
    _ = c * C₁' * c * s := by ring

end PositivityTheory.Rg.Rs.diffstep

end
