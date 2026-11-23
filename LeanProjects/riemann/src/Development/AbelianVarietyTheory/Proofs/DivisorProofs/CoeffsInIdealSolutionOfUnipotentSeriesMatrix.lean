import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.InvSolve

theorem in_iff_mem {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (f : MvPowerSeries σ Q) :
    In N f ↔ ∀ α, coeff α f ∈ N.toAddSubmonoid.map (algebraMap B Q).toAddMonoidHom := by
  simp only [In, AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe]
  constructor
  · intro h α; obtain ⟨b, hb, e⟩ := h α; exact ⟨b, hb, e.symm⟩
  · intro h α; obtain ⟨b, hb, e⟩ := h α; exact ⟨b, hb, e.symm⟩

theorem in_mul_map {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (f : MvPowerSeries σ Q) (h : MvPowerSeries σ B) (hf : In N f) :
    In N (f * map (algebraMap B Q) h) := by
  classical
  rw [in_iff_mem] at hf ⊢
  intro α
  rw [coeff_mul]
  refine AddSubmonoid.sum_mem _ fun x _ => ?_
  obtain ⟨b, hb, e⟩ := AddSubmonoid.mem_map.1 (hf x.1)
  refine AddSubmonoid.mem_map.2 ⟨b * coeff x.2 h, N.mul_mem_right _ hb, ?_⟩
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at e ⊢
  rw [map_mul, e, coeff_map]

theorem in_sum {B Q σ ι : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (s : Finset ι) (f : ι → MvPowerSeries σ Q) (hf : ∀ i ∈ s, In N (f i)) :
    In N (∑ i ∈ s, f i) := by
  rw [in_iff_mem] at *
  intro α
  rw [map_sum]
  exact AddSubmonoid.sum_mem _ fun i hi => (in_iff_mem N (f i)).1 (hf i hi) α

theorem solve : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (N : Ideal B) (M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B)), (∀ i j, constantCoeff (M i j) = if i = j then 1 else 0) → ∀ (v g : Fin d → MvPowerSeries (Fin d) Q), (∀ i, ∑ j, v j * map (algebraMap B Q) (M j i) = g i) → (∀ i, In N (g i)) → ∀ j, In N (v j) := by
  intro B Q _ _ _ d N M hM v g hv hg j
  classical
  have hc : (constantCoeff : MvPowerSeries (Fin d) B →+* B).mapMatrix M = 1 := by
    ext i k; simp [hM, Matrix.one_apply]
  have hdet : IsUnit M.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hc, Matrix.det_one]
    exact isUnit_one
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  let φ : MvPowerSeries (Fin d) B →+* MvPowerSeries (Fin d) Q := map (algebraMap B Q)
  have h2 : φ.mapMatrix M * φ.mapMatrix M⁻¹ = 1 := by rw [← map_mul, h1, map_one]
  have hvg : Matrix.vecMul v (φ.mapMatrix M) = g := funext fun i => by
    simpa [Matrix.vecMul, dotProduct, φ] using hv i
  have hv' : v = Matrix.vecMul g (φ.mapMatrix M⁻¹) := by
    rw [← hvg, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
  rw [hv']
  simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, φ]
  exact in_sum N _ _ fun i _ => in_mul_map N _ _ (hg i)

end GlobalTheory.InvSolve
