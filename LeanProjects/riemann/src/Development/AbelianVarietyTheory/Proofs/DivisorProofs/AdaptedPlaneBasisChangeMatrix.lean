import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

namespace GlobalTheory.ThK.FrameDet

theorem frame_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d₁ r' s' i₀ i₁ : ℕ) (W : Spc F E (d₁ + 2)) (W₁ : Spc F E d₁) (H' : Plane E (d₁ + 2) d₁)
    (Q : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E), W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ →
    (∀ r a, Q r (Fin.castAdd 2 a) = H'.ι r a) → (∀ r, Q r (Fin.natAdd d₁ 0) = H'.x r) →
    (∀ r, Q r (Fin.natAdd d₁ 1) = H'.y r) → Q.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B d₁ r' s' i₀ i₁ W W₁ H' Q hW hH hι hx hy
  haveI := hW.lat
  have hrange : LinearMap.range Q.mulVecLin = ⊤ := by
    rw [eq_top_iff, ← Submodule.IsLattice.span_eq_top (M := W.L), Submodule.span_le]
    intro z hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
    refine ⟨Fin.addCases u ![s, t], ?_⟩
    ext r
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.addCases_left,
      Fin.addCases_right, Fin.sum_univ_two, hι, hx, hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hsurj : Function.Surjective Q.mulVec := by
    intro z
    obtain ⟨v, hv⟩ : z ∈ LinearMap.range Q.mulVecLin := hrange ▸ Submodule.mem_top
    exact ⟨v, hv⟩
  exact ((Matrix.isUnit_iff_isUnit_det Q).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)).ne_zero

end GlobalTheory.ThK.FrameDet
