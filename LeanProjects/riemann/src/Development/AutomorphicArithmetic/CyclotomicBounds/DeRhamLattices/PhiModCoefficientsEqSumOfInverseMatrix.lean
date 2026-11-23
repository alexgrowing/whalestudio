import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private theorem hat_mulVec' {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
    {ι : Type} [Fintype ι] {Y : Matrix ι ι K⟦X⟧} (hY : ∀ i j, Y i j ∈ RpiE O K l e) {m : ι → K⟦X⟧}
    (hm : ∀ j, m j ∈ RpiE O K l e) (i : ι) :
    hat O l e ((Y *ᵥ m) i) = ∑ j, hat O l e (Y i j) * hat O l e (m j) := by
  have : (Y *ᵥ m) i = ((∑ j, ⟨Y i j, hY i j⟩ * ⟨m j, hm j⟩ : RpiE O K l e) : K⟦X⟧) := by
    simp [Matrix.mulVec, dotProduct]
  rw [this, hat_coe, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hat_of_mem l e (hY i j), hat_of_mem l e (hm j)]

theorem _root_.UpperTheory.KN.phiMod_coefficients_eq_sum_of_inverse_matrix :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat O K l e),
    (∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) →
    ∀ j, (fun τ => c τ j) = ∑ k, s k * fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P n s m c h j
  funext τ
  apply algebraMap_AhatE_injective l e
  rw [h τ j, Finset.sum_apply, map_sum]
  simp only [GlobalTheory.BKGal.JumpDR.hsum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc (i : ι) : (coordL P (invL l (S O K e)) (m k) i τ : K⟦X⟧) ∈ Rpi O K l e :=
    invL_S_le_Rpi l e (coordL P (invL l (S O K e)) (m k) i τ).2
  have hm (i : ι) : (m k).1 τ i ∈ RpiE O K l e := by
    have := congrFun (mx_mulVec_coordL P (invL l (S O K e)) (m k) τ) i
    rw [← this]
    exact Subalgebra.sum_mem _ fun i' _ =>
      mul_mem (invE_A_le_RpiE l e (P.mx_mem τ i i')) (le_away _ _ (hc i'))
  have h1 : (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧) = (P.mxInv τ *ᵥ (m k).1 τ) j := rfl
  rw [Pi.mul_apply, map_mul, GlobalTheory.GalStep.hatR_of_mem (hc j), ← hat_coe_Rpi]
  change _ = _ * hat O l e (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧)
  rw [h1, hat_mulVec' (fun i i' => invE_A_le_RpiE l e (P.mxInv_mem τ i i')) hm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm]
  rfl
