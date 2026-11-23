import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGramPosSemidefAndNormAtPlace
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem datFramed_of_gram_posDef {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok)
    (hG : ∀ v : InfinitePlace K, (S.gramV.map v.embedding).PosDef) : DatFramed S h := by
  refine ⟨S.hDim h, (S.hB h).equivFun.symm, fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v),
    fun v => (frameOfSpec _ _ (GlobalTheory.PeriodClassSum.gramAt_posDef S h v (hG v))).1, fun v x => ?_⟩
  have h1 := (GlobalTheory.PeriodClassSum.isFormsOf_formsLat S h hG ⊥).2 v ((S.hB h).equivFun.symm x)
  have h2 : Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (S.hDim h))) (fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v)) v x =
      Formalism.HermitianLatticesTheory.normAt (S.hB h) (fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v)) v ((S.hB h).equivFun.symm x) := by
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    congr 2
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [h2]
  exact h1

theorem evGSD_datFramed : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (h : (evGSD W Ch sel mu P u).Ok), DatFramed (evGSD W Ch sel mu P u) h := by
  intro X _ Pr R W Ch sel Sg mu P u h
  refine datFramed_of_gram_posDef _ h fun v => ?_
  have e : (evGSD W Ch sel mu P u).gramV = GlobalTheory.TestLat.Compare.gramB X.K (W.lamTrue u R.m) := by
    ext i k
    show pairVr X.emb (W.lamTrue u R.m) 1 (bVV _ _ i) (bVV _ _ k) = _
    rw [GlobalTheory.ColNorms.pairVr_one_eq]
    exact GlobalTheory.PeriodClassSum.pairK_one_basis (W.lamTrue u R.m) i k
  rw [e]
  exact GlobalTheory.PeriodClassSum.gramB_posDef (W.lamTrue u R.m) v.embedding

end GlobalTheory.ColRows
