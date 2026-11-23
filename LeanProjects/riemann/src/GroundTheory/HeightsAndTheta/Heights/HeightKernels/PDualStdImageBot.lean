import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.SingleMemDualLatticeStandard
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StandardDualImageBottom

open DualArithmeticVariety

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]

def genPt (K : Type) [Field K] (i : ℕ) : (Σ _ : Unit, Fin i) → ProjField K i :=
  fun q => algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X q.2)

omit [Fintype T] in

theorem aeval_eq_zero_of_mem (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    {f : MRing (dualBlocks T)} (hf : f ∈ dualIdeal b) : aeval (dualLatticeCoord b) f = 0 := by
  have h : ∀ g : MRing (dualBlocks T),
      MvPolynomial.eval (fun _ : Unit => (1 : ProjField K i)) (mConeMap (dualLatticeCoord b) g) =
        aeval (dualLatticeCoord b) g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp]
      simp [mConeMap]
  rw [← h f, show mConeMap (dualLatticeCoord b) f = 0 from hf, map_zero]

def evalQ (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MvPolynomial Unit (MRing (dualBlocks T) ⧸ dualIdeal b) →+* ProjField K i :=
  eval₂Hom (Ideal.Quotient.lift _ (aeval (dualLatticeCoord b)).toRingHom
    fun _ hf => aeval_eq_zero_of_mem b hf) fun _ => 1

theorem aeval_linForm (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (q : Σ _ : Unit, Fin i) :
    aeval (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) q) = genPt K i q := by
  obtain ⟨⟨⟩, j⟩ := q
  have hs := congrArg (evalForm (K := K) i) (dualStdCoordMat_sum b j)
  rw [map_sum, evalForm, Fintype.linearCombination_apply_single, one_smul, ← evalForm] at hs
  rw [genPt, ← hs, linForm, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, aeval_C, aeval_X, map_zsmul, ← dualLatticeCoord_eq, zsmul_eq_mul, eq_intCast]

theorem evalQ_graphMap (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (f : MRing (PBlk i)) :
    evalQ b (graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))
      (rename (inrV (ι := dualBlocks T) (ι₂ := PBlk i)) f)) = aeval (genPt K i) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap, evalQ]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, hp, map_mul, aeval_X, rename_X, ← aeval_linForm b q]
    simp [graphMap, inrV, evalQ]

theorem aeval_genPt_injective : Function.Injective (aeval (R := ℤ) (genPt K i)) := by
  have hK : AlgebraicIndependent ℤ fun j : Fin i =>
      algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j) :=
    (algebraicIndependent_gen i).restrictScalars (algebraMap ℤ K).injective_int
  have h := hK.comp (fun q : Σ _ : Unit, Fin i => q.2) (by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, c⟩ h
    cases h
    rfl)
  exact algebraicIndependent_iff_injective_aeval.mp h

end StandardDualImageBottom

open StandardDualImageBottom in

theorem DualStdImageBot.proof : DualStdImageBot.Statement := by
  intro K _ _ i T _ _ b
  refine eq_bot_iff.mpr fun f hf => (Ideal.mem_bot).mpr (aeval_genPt_injective (K := K) (i := i) ?_)
  have h0 : graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))
      (rename (inrV (ι := dualBlocks T) (ι₂ := PBlk i)) f) = 0 := hf
  rw [map_zero, ← evalQ_graphMap b, h0, map_zero]

end

end GroundTheory.Heights₂.Heights
