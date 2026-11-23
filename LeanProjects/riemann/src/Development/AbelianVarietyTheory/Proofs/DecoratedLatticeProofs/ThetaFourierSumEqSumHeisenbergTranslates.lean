import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfFourier

theorem thetaAt_eq_sum_heis_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (ι : Type) (s : Finset ι) (K : ι → ℂ) (xs ys : ι → WO S T) (k : ℕ), 0 < k → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ i ∈ s, IsHalf e (xs i)) → (∀ i ∈ s, IsHalf (cA D e) (ys i)) → (∀ i ∈ s, ∀ u ∈ Λ, ψ (symplO S T (k • u) (ys i)) = 1) → (∀ t, Φ t = ∑ i ∈ s, K i * (ψ (symplO S T (t + xs i) (ys i)) * halfInd e Λ (t + xs i))) → f = ∑ i ∈ s, K i • heisO ψ S T (xs i) (heisO ψ S T (ys i) f₀) := by
  intro D ψ S T e Λ f₀ Φ f ι s K xs ys k hk hθ hx hy hΛ hΦ
  classical
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hvac : Tm (halfInd e Λ) = f₀ := by simpa using hTm.vac

  set g : ι → WO S T → ℂ := fun i t => ψ (symplO S T t (ys i)) * halfInd e Λ t with hg
  have hhalf : ∀ t, halfInd e Λ t ≠ 0 → t ∈ Λ ∧ IsHalf e t := by
    intro t ht
    by_contra h
    exact ht (by simp [halfInd, h])
  have hSB : ∀ i ∈ s, IsSBHalf e Λ (g i) := by
    intro i hi
    refine ⟨fun t ht => ?_, k, hk, fun u hu hh t => ?_, fun t ht => ?_⟩
    · exact (hhalf t (right_ne_zero_of_mul ht)).2
    · have hku : k • u ∈ Λ := Λ.nsmul_mem hu k
      have hkh : IsHalf e (k • u) := by
        intro a b
        change e * ((k • u : Matrix _ _ (AE D)) a b) = (k • u : Matrix _ _ (AE D)) a b
        rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hh a b]
      have hind : halfInd e Λ (t + k • u) = halfInd e Λ t := by
        have : (t + k • u ∈ Λ ∧ IsHalf e (t + k • u)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
          rw [Λ.add_mem_cancel_right hku]
          refine and_congr_right fun _ => forall_congr' fun a => forall_congr' fun b => ?_
          rw [Matrix.add_apply, mul_add, hkh a b, add_left_inj]
        simp only [halfInd, this]
      simp only [hg, hind, GlobalTheory.LatVac.symplO_add_left, AddChar.map_add_eq_mul, hΛ i hi u hu, mul_one]
    · exact Λ.nsmul_mem (hhalf t (right_ne_zero_of_mul ht)).1 k
  have hΦ' : Φ = ∑ i ∈ s, K i • fun t => g i (t + xs i) := by
    funext t
    rw [hΦ t, Finset.sum_apply]
    rfl
  rw [hall Tm hTm, hΦ', map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, hTm.trans _ (hSB i hi) (xs i) (hx i hi)]
  congr 2
  have : g i = fun t => ψ (symplO S T t (ys i)) * halfInd e Λ t := rfl
  rw [this, hTm.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) (ys i) (hy i hi), hvac]

end GlobalTheory.HalfFourier
