import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsHermiteReducedLatticeBasis

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped MatrixOrder

namespace GlobalTheory.RedTh.RedBasis

theorem sum_sum_eq_dotProduct {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * G i j = c ⬝ᵥ (G *ᵥ c) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_transpose_mul_self {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hs : Gᵀ = G)
    (hp : ∀ c : Fin n → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * G i j) :
    ∃ g : Matrix (Fin n) (Fin n) ℝ, g.det ≠ 0 ∧ gᵀ * g = G := by
  have hT : G.PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · show Gᴴ = G
      rw [conjTranspose_eq_transpose_of_trivial, hs]
    · by_cases hx : x = 0
      · simp [hx]
      · have := (hp x hx).le
        rw [sum_sum_eq_dotProduct] at this
        simpa using this
  have h0 : 0 ≤ G := Matrix.nonneg_iff_posSemidef.mpr hT
  have hsq : (CFC.sqrt G).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hsym : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have := hsq.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hgG : (CFC.sqrt G)ᵀ * CFC.sqrt G = G := by
    rw [hsym, CFC.sqrt_mul_sqrt_self G h0]
  refine ⟨CFC.sqrt G, fun hd => ?_, hgG⟩
  obtain ⟨v, hv, hgv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h := hp v hv
  rw [sum_sum_eq_dotProduct, ← hgG, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hgv] at h
  simp at h

theorem exists_siegel_basis : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] (b₀ : Module.Basis (Fin n) ℤ Y)
    (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ), (∀ y z, B y z = B z y) → IsPosDef B → ∃ (b : Module.Basis (Fin n) ℤ Y)
    (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧
    ∀ i j, B (b i) (b j) = gram d u i j := by
  intro n Y _ b₀ B hs hB
  let G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => B (b₀ i) (b₀ j)
  obtain ⟨g, hg, hgG⟩ := exists_transpose_mul_self G (by ext i j; simp [G, hs])
    (by simpa [G] using (isPosDef_iff_basis b₀ B).1 hB)
  obtain ⟨γ, k, a, m, hγ, hk, ha, h1, h0, hup, hstep, hdec⟩ :=
    GlobalTheory.ClassFin.HermiteReduction.exists_reduced n g hg
  have hu : IsUnit γ.det := by rcases hγ with h | h <;> rw [h] <;> simp
  let e : Y ≃ₗ[ℤ] Y := Matrix.toLinearEquiv b₀ γ hu
  have hbe : ∀ j, b₀.map e j = ∑ i, γ i j • b₀ i := fun j => by
    simp [e, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have hM : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) = gram (fun i => a i ^ 2) m := by
    have e1 : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) =
        (g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ)) := by
      rw [← hgG, transpose_mul]; simp only [Matrix.mul_assoc]
    have e2 : (k * diagonal a * m)ᵀ * (k * diagonal a * m) = mᵀ * (diagonal a * (kᵀ * k) * diagonal a) * m := by
      simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    rw [e1, hdec, e2, hk, Matrix.mul_one, diagonal_mul_diagonal, gram]
    simp only [sq]
  refine ⟨b₀.map e, fun i => a i ^ 2, m, ⟨fun i => sq_nonneg _, fun p q hq => ?_, h1, h0, hup⟩,
    fun i => pow_pos (ha i) 2, fun i j => ?_⟩
  · have h2 := hstep p q hq
    have h3 := ha p
    have h4 := ha q
    show a p ^ 2 ≤ 4 * a q ^ 2
    nlinarith
  · rw [← hM, hbe, hbe]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Matrix.mul_apply,
      transpose_apply, map_apply, G, of_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.RedTh.RedBasis
