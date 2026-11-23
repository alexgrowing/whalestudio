import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPrincipalDegree
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  blockWeight)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem relDim_of_isProjVar {P : Ideal (MRing ι ℂ)} {e : ℕ} (h : IsProjVar P e) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim P = (e : ℕ) := by
  rw [GroundTheory.Heights₂.Heights.FieldNumbers.relDim_of_ringKrullDim_eq P _ h.2]
  show ((((e + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) =
    (((e : ℕ) : ℤ) : WithBot (WithTop ℤ))
  congr 1
  push_cast
  ring

theorem isProjVar_of_mem_comps {P : Ideal (MRing ι ℂ)} {e : ℕ} {s : MRing ι ℂ} {c : K → ℕ}
    (hP : IsProjVar P (e + 1)) (hs : IsMultiHomog s c) (hsP : s ∉ P) {W : Ideal (MRing ι ℂ)}
    (hW : W ∈ comps P s) : IsProjVar W e := by
  obtain ⟨hmin, hrel⟩ := hW
  have hWh : IsMultiHomogIdeal W := (GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff W).mpr
    (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
      ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff P).mp hP.1.multiHomog)
      ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff s c).mp hs) hmin)
  refine ⟨⟨hmin.1.1, hWh, hrel⟩, ?_⟩
  have := hP.1.isPrime
  have hPd := hP.2
  have key : ringKrullDim (MRing ι ℂ ⧸ W) + 1 = ringKrullDim (MRing ι ℂ ⧸ P) :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_quot_minimal_add_one hsP hmin (fun h => by
      rw [hPd] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
  rw [hPd, show e + 1 + Fintype.card K = (e + Fintype.card K) + 1 by ring] at key
  exact ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key

omit [∀ k, Fintype (ι k)] in

theorem exists_form {P : Ideal (MRing ι ℂ)} (hP : IsMultiProjPrime P) (c : K → ℕ) :
    ∃ s : MRing ι ℂ, IsMultiHomog s c ∧ s ∉ P := by
  choose i hi using hP.relevant
  have hpr := hP.isPrime
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have h : IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, i k⟩ : MRing ι ℂ) ^ c k)
        (∑ k, c k • blockWeight ι ⟨k, i k⟩) :=
      IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℂ _ _).pow (c k)
    have hw : (∑ k, c k • blockWeight ι ⟨k, i k⟩) = c := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hw] at h
    exact h
  · intro hm
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
    exact hi k (hpr.mem_of_pow_mem _ hk)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
