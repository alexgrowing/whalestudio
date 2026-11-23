import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)
open scoped ComplexOrder

namespace GlobalTheory.ColumnFamilyMetric

open GlobalTheory.PeriodClassSum GlobalTheory.TestLat.Compare

theorem chF_gramV (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg)
    (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (b : (chF W sel mu I u j).β) :
    ((chF W sel mu I u j).mem b).gramV = GlobalTheory.TestLat.Compare.gramB X.K (W.lamTrue u j) := by
  ext i k
  have e : gramKd X.emb (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) = fun _ => 1 := by
    funext τ
    rw [gramKd, Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]
  show pairK (W.lamTrue u j) (gramKd X.emb 1) (bVV _ _ i) (bVV _ _ k) = _
  rw [e]
  exact pairK_one_basis (W.lamTrue u j) i k

theorem famIpAt_nonneg : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (h : (chF W sel mu I u j).Ok) (v : InfinitePlace X.K) (φ : (chF W sel mu I u j).Forms), 0 ≤ (famIpAt (chF W sel mu I u j) h v φ φ).re := by
  intro X Pr R W sel Sg mu I u j h v φ
  refine (Complex.nonneg_iff.1 ?_).1
  unfold famIpAt
  refine Finset.sum_nonneg fun b _ => ?_
  have hG : ((((chF W sel mu I u j).mem b).gramV).map v.embedding).PosSemidef := by
    rw [chF_gramV]
    exact (gramB_posDef (W.lamTrue u j) v.embedding).posSemidef
  letI := (h b).fintypeCl
  exact (ipAt_eq _ (h b) v _ _).symm ▸ wForm_nonneg _ hG _

end GlobalTheory.ColumnFamilyMetric
