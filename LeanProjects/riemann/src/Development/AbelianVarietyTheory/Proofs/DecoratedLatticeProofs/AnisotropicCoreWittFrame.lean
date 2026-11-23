import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittFrameOfDec

theorem form_mulVec {D : D7} {n m : ℕ} (A : Matrix (Fin n) (Fin m) D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E)
    (w : Fin m → D.host.E) : star (A *ᵥ w) ⬝ᵥ (G *ᵥ (A *ᵥ w)) = star w ⬝ᵥ ((Aᴴ * G * A) *ᵥ w) := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem isWittFrame_of_hypDec (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (h : IsAniso T₀) :
    IsWittFrame D.sp.cm.sig T.gram d.e d.e' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cT_sig]; exact d.ee
  · rw [cT_sig]; exact d.e'e'
  · rw [cT_sig]
    have h1 := congrArg Matrix.conjTranspose d.e'e
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h1
    exact h1
  · intro z hX hY hz
    rw [cT_sig] at hX hY
    have hqY : d.qY *ᵥ z = 0 := hX
    have hqX : d.qX *ᵥ z = 0 := hY
    have hz0 : z = d.i₀ *ᵥ (d.q0 *ᵥ z) := by
      have := congrArg (fun M => M *ᵥ z) d.sum_eq_one_rat
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hqX, hqY,
        Matrix.mulVec_zero, zero_add, add_zero] at this
      exact this.symm
    obtain ⟨z₀, hz₀⟩ : ∃ w, w = d.q0 *ᵥ z := ⟨_, rfl⟩
    rw [← hz₀] at hz0
    by_cases h0 : z₀ = 0
    · rw [hz0, h0, Matrix.mulVec_zero]
    exfalso
    have e1 : hE D.sp.cm.sig T.gram z z = star z ⬝ᵥ (T.gram *ᵥ z) := by
      simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc]; rfl
    have hzz : star z₀ ⬝ᵥ (T₀.gram *ᵥ z₀) = 0 := by
      rw [← d.iso, ← form_mulVec, ← hz0, ← e1, hz]
    let C : Matrix (Fin T₀.rank) (Fin 1) D.host.E := Matrix.of fun i _ => z₀ i
    apply h 1 C
    refine ⟨Nat.one_pos, ?_, ?_⟩
    · change LinearIndependent D.host.E (fun _ : Fin 1 => z₀)
      exact linearIndependent_unique_iff.2 h0
    · rw [cT_sig]
      ext a b
      fin_cases a; fin_cases b
      have : (Cᴴ * T₀.gram * C) 0 0 = star z₀ ⬝ᵥ (T₀.gram *ᵥ z₀) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, C, Matrix.of_apply, dotProduct, Matrix.mulVec,
          Pi.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      simpa using this.trans hzz

end GlobalTheory.WittFrameOfDec
