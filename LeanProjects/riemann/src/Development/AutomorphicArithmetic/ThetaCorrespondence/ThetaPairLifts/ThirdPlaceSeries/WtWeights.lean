import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeightDataIntegral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShHalfStatement

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
attribute [local instance] algKkT
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem wt_weights_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
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
  intro _ D cf jE A _ _
  refine ⟨fun l _ j => ⟨⊥, inferInstance⟩, fun b0 b1 Sx T Sp _ => ?_⟩
  have hlam : ∀ (j : Fin D.R.m) (t : D.what₂.Tau), ∃ lam : DomWeight D.R.nV, ∀ sh : ℂ,
      D.naut.infG D.naut.etaT (embT D t) = {sh} → NG.infOf lam.w = NG.paramV D.R (D.hc t) j sh := by
    intro j t
    by_cases h : ∃ sh, D.naut.infG D.naut.etaT (embT D t) = {sh}
    · obtain ⟨sh, hs⟩ := h
      obtain ⟨lam, hl⟩ := GlobalTheory.T.liftWeightParam_eq_infinitesimalCharacter_of_halfInt D.R (D.hc t) j sh (_root_.GlobalTheory.T.infG_eq_half_integer D cf jE A t sh hs)
      refine ⟨lam, fun sh' hs' => ?_⟩
      rw [hs, Multiset.singleton_inj] at hs'
      rw [← hs']
      exact hl
    · exact ⟨⟨fun _ => 0, antitone_const⟩, fun sh hs => absurd ⟨sh, hs⟩ h⟩
  choose lamF hlamF using hlam
  let lamD : ℕ → D.what₂.Tau → DomWeight D.R.nV := fun j t =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then lamF ⟨j - 1, by omega⟩ t else ⟨fun _ => 0, antitone_const⟩
  have hc : NX.cE D = (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) :=
    RingHom.ext fun x => (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  refine ⟨{ Wt := fun i j _ => Module.Dual (FractionRing (T.O i)) (Formalism.L2.DIV.VV (FractionRing (T.O i)) (lamD j))
            fd := fun i j _ => GlobalTheory.AlgWtF.finDualVV (lamD j)
            rhoW := fun i j b => GlobalTheory.AlgWtF.wtRepF (kEmbT D T i b) (lamD j) }, fun i j b hj hjm => ?_⟩
  haveI := GlobalTheory.T.charZero_fractionRing_coefficientRing D T i
  have hE := GlobalTheory.T.cmTypeEmbeddingAtSide_distinct_nonconjugate D T i b
  have hl : lamD j = lamF ⟨j - 1, by omega⟩ := by
    simp only [lamD, dif_pos (And.intro hj hjm)]
  refine ⟨GlobalTheory.T.contragredient_isIrreducible_finiteDimensional _ _ _ _ (GlobalTheory.T.weightTensorRepOfEmbeddings_isIrreducible _ _ _ _ _ _ hE), GlobalTheory.T.isAlgWeightF_weightTensorDualRepOfEmbeddings _ _ _ _ _ _,
    fun k => @GlobalTheory.T.isIrreducible_baseChange_weightTensorDualRepOfEmbeddings _ _ _ _ _ _ _ _ _ _ _ _ hE (FractionRing (T.Ok i k)) _ (algKkT D T i k),
    fun t => ⟨_, hc ▸ GlobalTheory.T.weightTensorDualRep_dual_highestWeight_at_embedding _ _ _ _ _ _ hE t⟩, fun t sh lam hs hw => ?_⟩
  rw [hc] at hw
  have h1 := GlobalTheory.T.highestWeight_doubleDual_coefficientSpace_unique _ _ _ _ _ _ hE t lam hw
  rw [h1]
  show NG.infOf (lamD j t).w = _
  rw [hl]
  exact hlamF _ t sh hs
end GlobalTheory.HeightCounting.FormsStep
end
end
