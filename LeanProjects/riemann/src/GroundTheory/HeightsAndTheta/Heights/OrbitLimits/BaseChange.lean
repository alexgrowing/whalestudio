import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsBaseChangeRelabel
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)

noncomputable section

universe u u' v w

namespace BaseChange

variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F'] {K : Type*} [Fintype K]
  {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isProjVarF_of_mem_minimalPrimes {V : Ideal (MRingOver F ι)} {n : ℕ} (hV : IsProjVarF V n)
    {W : Ideal (MRingOver F' ι)}
    (hW : W ∈ (V.map (MvPolynomial.map (algebraMap F F'))).minimalPrimes) : IsProjVarF W n := by
  classical
  have := hV.1.1
  have hc := BaseChangeMin.comap_of_mem_minimalPrimes_map V W hW
  have hVo : NumbersDVR.IsMultiProjPrime V := (Objects.isMultiProjPrime_iff V).mpr hV.1
  have hJ : NumbersDVR.IsMultiHomogIdeal (V.map (MvPolynomial.map (algebraMap F F'))) :=
    FieldNumbers.isMultiHomogIdeal_map hVo.multiHomog
  have hWo : NumbersDVR.IsMultiProjPrime W := by
    refine ⟨hW.1.1, FieldNumbers.PFContracted.isMultiHomogIdeal_of_mem_minimalPrimes hJ hW, ?_⟩
    intro k
    obtain ⟨i, hi⟩ := hVo.relevant k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hc, Ideal.mem_comap, MvPolynomial.map_X]
    exact hX
  refine ⟨(Objects.isMultiProjPrime_iff W).mp hWo, ?_⟩
  rw [BaseChangeMin.ringKrullDim_of_mem_minimalPrimes_map V W hW]
  exact hV.2

end BaseChange

open BaseChange

theorem BaseChange.of_found (hN : IntNumIsFieldIntersection.Statement.{u})
    (hUq : FieldNumbers.IntNumUnique.Statement.{u}) (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hN' : IntNumIsFieldIntersection.Statement.{u'})
    (hUq' : FieldNumbers.IntNumUnique.Statement.{u'})
    (hBase' : FieldNumbers.IntNumBase.Statement.{u'})
    (hBC : FieldNumbers.IntNumBaseChange.Statement.{u, u'}) (hAs : IntNumAssoc.Statement.{u'})
    (F : Type u) (F' : Type u') [Field F] [Field F'] [Algebra F F'] {K : Type} [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.BaseChangeStatement F F' ι := by
  classical
  intro I I' hI hI' V n L hV
  have hEU := ExistsUnique.of_found hN hUq hBase F ι
  have hEU' := ExistsUnique.of_found hN' hUq' hBase' F' ι
  have := hV.1.1
  set J := V.map (MvPolynomial.map (algebraMap F F')) with hJdef
  have hmin : ∀ W ∈ J.minimalPrimes, IsProjVarF W n :=
    fun W hW => isProjVarF_of_mem_minimalPrimes hV hW
  have hVo : NumbersDVR.IsMultiProjPrime V := (Objects.isMultiProjPrime_iff V).mpr hV.1
  have hJ : NumbersDVR.IsMultiHomogIdeal J := FieldNumbers.isMultiHomogIdeal_map hVo.multiHomog
  have hdim : ringKrullDim (MRingOver F' ι ⧸ J) < ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    refine lt_of_le_of_lt (BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes _
      (N := ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) fun Z hZ => (hmin Z hZ).2.le) ?_
    exact_mod_cast (show n + Fintype.card K < n + 1 + Fintype.card K by omega)
  rw [Numbers.agree_of_existsUnique hN hEU I hI V n L hV, ← (hBC.1 F F' K ι V).2 n L,
    hAs F' K ι n J hJ hdim L]
  unfold NumbersDVR.cycEval
  rw [finsum_mem_def]
  refine finsum_congr fun W => ?_
  unfold idealCycle
  by_cases hW : W ∈ J.minimalPrimes
  · have : W.IsPrime := hW.1.1
    have hWv := hmin W hW
    rw [dif_pos ⟨hW, (Objects.isMultiProjPrime_iff W).mpr hWv.1 |>.relevant⟩,
      Set.indicator_of_mem hW, Numbers.agree_of_existsUnique hN' hEU' I' hI' W n L hWv]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos this]
    rfl
  · rw [dif_neg (fun h => hW h.1), Set.indicator_of_notMem hW]
    simp

theorem BaseChange.full (F : Type u) (F' : Type u') [Field F] [Field F'] [Algebra F F'] {K : Type}
    [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.BaseChangeStatement F F' ι :=
  BaseChange.of_found IntNumIsFieldIntersection.full FieldNumbers.IntNumUnique.full
    FieldNumbers.IntNumBase.full IntNumIsFieldIntersection.full FieldNumbers.IntNumUnique.full
    FieldNumbers.IntNumBase.full FieldNumbers.IntNumBaseChange.full IntNumAssoc.full F F' ι

end

end GroundTheory.Heights₂.Heights.Targets
