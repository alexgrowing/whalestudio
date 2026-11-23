import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeightDataIntegralStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtWeights

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_data_integral_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) →
    ∃ c2 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c2 l j).1 ≤ (b0 l j).1) →
      ∃ wt : WtData D T, ∀ i j b (hj : 1 ≤ j) (hjm : j ≤ D.R.m),
        (wt.rhoW i j b).IsIrreducible ∧ NX.IsAlgWeightF D.host.E D.R.nV (FractionRing (T.O i)) (wt.rhoW i j b) ∧
        (∀ k, (rhoKT D T wt i j b k).IsIrreducible) ∧
        (∀ t, ∃ lam : Fin D.R.nV → ℤ, NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam) ∧
        ∀ (t : D.what₂.Tau) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
          D.naut.infG D.naut.etaT (embT D t) = {sh} → NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam →
          NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt | exact _root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt <;> assumption)
end
