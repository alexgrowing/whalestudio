import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisRestrict

theorem hE_swap_conj {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hJ]; ring

theorem hE_col0v_gram {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n r : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin (r + 1)) E) :
    hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) = (Formalism.UG.cT (σ : E →+* E) X * J * Y) 0 0 := by
  simp only [hE, Formalism.UG.hform, Formalism.UG.cT, GlobalTheory.EisMidHt.firstColumn, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end GlobalTheory.EisRestrict

open GlobalTheory.EisRestrict in

theorem GlobalTheory.EisRestrict.isHermND_restrictedForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    IsHermND σ (J0 σ J X Y) := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW
  have hσ : ∀ e, σ (σ e) = e := fun e => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm e
  set x₀ := GlobalTheory.EisMidHt.firstColumn X
  set y₀ := GlobalTheory.EisMidHt.firstColumn Y
  have hxy : hE σ J x₀ y₀ = 1 := by
    rw [hE_col0v_gram, hW.xy, Matrix.one_apply_eq]
  have hyx : hE σ J y₀ x₀ = 1 := by rw [hE_swap_conj σ J hσ hJ.1, hxy, map_one]
  have hxx : hE σ J x₀ x₀ = 0 := by
    rw [hE_col0v_gram σ J X X, hW.xx]; rfl
  have hyy : hE σ J y₀ y₀ = 0 := by
    rw [hE_col0v_gram σ J Y Y, hW.yy]; rfl
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [J0, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
      RingHom.coe_coe, hσ]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← hJ.1 l k]; ring
  · intro hdet
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    set z := ι σ J X Y u with hz
    have hzV : z ∈ V0 σ J X Y := ι_mem σ J X Y u

    have hV : ∀ v ∈ V0 σ J X Y, hE σ J z v = 0 := by
      intro v hv
      obtain ⟨u', rfl⟩ := exists_ι_eq σ J X Y hv
      rw [hE_swap_conj σ J hσ hJ.1, ← hE_J0, hE_eq_dot, hu, dotProduct_zero, map_zero]
    have hzV' := (mem_invariant_forms σ J X Y).1 hzV
    have hx : hE σ J z x₀ = 0 := by rw [hE_swap_conj σ J hσ hJ.1, hzV'.1, map_zero]
    have hy : hE σ J z y₀ = 0 := by rw [hE_swap_conj σ J hσ hJ.1, hzV'.2, map_zero]

    have hall : ∀ w, hE σ J z w = 0 := by
      intro w
      set w' := w - hE σ J y₀ w • x₀ - hE σ J x₀ w • y₀
      have hw' : w' ∈ V0 σ J X Y := by
        have h1 := (hRight σ J x₀).map_sub (w - hE σ J y₀ w • x₀) (hE σ J x₀ w • y₀)
        have h2 := (hRight σ J x₀).map_sub w (hE σ J y₀ w • x₀)
        have h3 := (hRight σ J y₀).map_sub (w - hE σ J y₀ w • x₀) (hE σ J x₀ w • y₀)
        have h4 := (hRight σ J y₀).map_sub w (hE σ J y₀ w • x₀)
        simp only [hRight, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.map_smul, smul_eq_mul] at h1 h2 h3 h4
        refine (mem_invariant_forms σ J X Y).2 ⟨?_, ?_⟩
        · rw [h1, h2, hxx, hxy]; ring
        · rw [h3, h4, hyx, hyy]; ring
      have hw : w = w' + hE σ J y₀ w • x₀ + hE σ J x₀ w • y₀ := by
        simp only [w']; abel
      have e := (hRight σ J z).map_add (w' + hE σ J y₀ w • x₀) (hE σ J x₀ w • y₀)
      have e2 := (hRight σ J z).map_add w' (hE σ J y₀ w • x₀)
      simp only [hRight, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.map_smul, smul_eq_mul] at e e2
      rw [hw, e, e2, hV w' hw', hx, hy]; ring
    have hJz : J *ᵥ z = 0 := by
      funext i
      have h := hall (Pi.single i 1)
      rw [hE_swap_conj σ J hσ hJ.1, hE_eq_dot] at h
      have h' : (fun k => σ ((Pi.single i (1 : E) : Fin n → E) k)) = Pi.single i 1 := by
        funext k; by_cases hk : k = i
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      rw [h', single_one_dotProduct] at h
      have := congrArg σ h
      rw [hσ, map_zero] at this
      simpa using this
    have hz0 : z = 0 := by
      by_contra hne
      exact hJ.2 (Matrix.exists_mulVec_eq_zero_iff.mp ⟨z, hne, hJz⟩)
    exact hu0 (ι_injective σ J X Y (by rw [← hz, hz0, map_zero]))
