import Mathlib
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortGeneratorPlaceValuationBoundProofStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.WeightNormalizerAndExponentsOfWeightSumStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledThetaLatticeLeSupLatticeEveryWeightStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledShortLatticeLeOfShortGeneratorBoundStatement

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
namespace GlobalTheory.PlaceTop

set_option maxHeartbeats 4000000 in

theorem integralityCondition_of_addedPoints_secondNorm {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : GlobalTheory.RunIn.SecNorm B) (X : PJ D B P j)
    (E : PtExt X) (hM : IntAtExt X E) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (hX : H2 X S ka wL wF) :
    H2 (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (xplus X E hM)) (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF := hX

set_option maxHeartbeats 4000000 in

theorem integralityCondition_algebraicPoints (D : D7) (T : Top D) (h : LawsP T) (hs : LawsSh T) (j : ℕ) (hj : InR D j)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (ho : Oriented T EX) (p : ℕ) (hp : ∀ n, (T.dδ j n).pd = p)
    (ka wL wF : WeightFamilies.Wt D j) (T₀ nP : ℕ) (hF : IsF' ka wL wF T₀ nP) :
    H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF T₀) ka wL wF := by
  have key : ∀ (w : WeightFamilies.Wt D j) (k : ℕ), (∀ τ i, w.aP τ i = wF.aP τ i + k * wL.aP τ i) →
      (∀ τ i, w.aM τ i = wF.aM τ i + k * wL.aM τ i) →
      (recPJ h j hj).Thc ((zOwnP D p w : 𝓞 (recB h.toLawsCore).KO) * nnW (recB h.toLawsCore) hinj EX wL ^ k *
        nnW (recB h.toLawsCore) hinj EX wF *
        (pPow D (k * c2 D wL + c2 D wF) (k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF)
          (k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF) : 𝓞 (recB h.toLawsCore).KO)) w ≤
        (recB h.toLawsCore).Mlat j w := by
    intro w k h1 h2
    obtain ⟨e, a, b⟩ := GlobalTheory.T.nnW_eq_pow_mul_and_c2_cHalf_le_of_weight_sum D (recB h.toLawsCore) hinj EX j wL wF w k h1 h2
    refine GlobalTheory.T.scaledShortLattice_le_of_shortGenerator_bound GlobalTheory.T.shortGeneratorPlaceValuationBound_proof D T h hs j hj hinj EX ho w _ _ _ a b ?_
    rw [hp, e]
    exact congrArg (· * _) (mul_assoc _ _ _)
  refine ⟨GlobalTheory.T.scaledThetaLattice_le_supLattice_every_weight D T h j hj hinj EX ho wL, ?_, ?_, ?_⟩
  · refine GlobalTheory.T.scaledShortLattice_le_of_shortGenerator_bound GlobalTheory.T.shortGeneratorPlaceValuationBound_proof D T h hs j hj hinj EX ho wF _ _ _ le_rfl le_rfl ?_
    rw [hp]
    rfl
  · exact key (wadd wF (wsmul (WeightFamilies.dimY D j) wL)) (WeightFamilies.dimY D j) (fun _ _ => rfl) (fun _ _ => rfl)
  · exact key ka T₀ (fun τ i => by have := hF.2.1 τ i; zify; linarith)
      (fun τ i => by have := hF.2.2 τ i; zify; linarith)

theorem scaledRunLatticesInSupLattices_proof : ScaledLatticesInSupLattices := by
  intro D T h hs j hj hinj EX ho p hp ka wL wF T₀ nP hF
  have H := integralityCondition_algebraicPoints D T h hs j hj hinj EX ho p hp ka wL wF T₀ nP hF
  exact ⟨H, fun n => integralityCondition_of_addedPoints_secondNorm n _ _ _ _ ka wL wF H⟩

end GlobalTheory.PlaceTop
