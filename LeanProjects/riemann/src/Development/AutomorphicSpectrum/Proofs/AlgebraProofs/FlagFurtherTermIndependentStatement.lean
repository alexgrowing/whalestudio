import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisFurther
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagFurtherTermIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivFibreVariety
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagVertSymmIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagRestrict
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagFrameOfFullFlag
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumIntNumLClassListEqOfIsSymmetricStatement

namespace GlobalTheory.CompanionTheory.Ar.Num.FurtherIndep

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR

theorem polyNum_eq_sum {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (V : Ideal (MRing ι F)) (e : ℕ)
    (hV : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF V e) {N : ℕ} (d : Fin N → K → ℤ)
    (G : MvPolynomial (Fin N) ℤ) (c n : ℕ) (Y : Fin n → K → ℤ) (hG : G.IsHomogeneous c)
    (hcn : c + n = e) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I V e (Fin.append d Y)
                              (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j)) =
      ∑ μ ∈ G.support, G.coeff μ * intNumL F V (classList d μ ++ List.ofFn Y) := by
  rw [SegreFlagIndep.prod_X_natAdd, SegreFlagIndep.polyNum_mul_monomial, SegreFlagIndep.monoList_ones]
  refine Finset.sum_congr rfl fun α hα => ?_
  congr 1
  have hdeg : α.degree = c := by
    have := hG (mem_support_iff.mp hα)
    rwa [Finsupp.degree_eq_weight_one]
  have hlen : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList d α ++ List.ofFn Y).length = e := by
    rw [List.length_append, SegreFlagIndep.length_monoList, hdeg, List.length_ofFn, hcn]
  rw [SegreFlagIndep.listNum, dif_pos hlen,
    Numbers.agree FieldNumbers.IntNumUnique.full (IntNumPoint.proof FieldNumbers.IntNumBase.full)
      FieldNumbers.IntNumBase.full I hI V e _ hV,
    BundleExamples.intNum_get_cast F V _ e hlen]
  refine FlagTypings.intNumL_perm F V (List.Perm.append_right _ ?_)
  rw [BundleExamples.monoList_eq]
  exact FlagTypings.monoList_perm d α

theorem segreFlagIndep (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SegreFlagIndep.Statement.{0} F Ω ι := by
  classical
  intro x e hV N E _ _ B fl₁ fl₂ I hI G hG c n Y hGc hcn
  obtain ⟨w, hw⟩ := BundleExamples.FlagFrameOfFullFlag.proof F Ω K ι x e hV N E B fl₁
  obtain ⟨v, hv⟩ := BundleExamples.FlagFrameOfFullFlag.proof F Ω K ι x e hV N E B fl₂
  rw [polyNum_eq_sum I hI _ e hV _ G c n Y hGc hcn, polyNum_eq_sum I hI _ e hV _ G c n Y hGc hcn]
  have hI' := VocabMultiHomogIdeal.proof VocabMultiHomog.proof F K ι (pointIdeal F x)
  have hP : IsMultiProjPrime (pointIdeal F x) := ⟨hV.1.1, hI'.1 hV.1.2.1, hV.1.2.2⟩
  exact GlobalTheory.T.sum_intNumL_classList_eq_of_isSymmetric F Ω K ι x e hP hV.2 N E B w v _ _ hw hv c G hG hGc (List.ofFn Y)
    (by rw [List.length_ofFn]; omega)

end GlobalTheory.CompanionTheory.Ar.Num.FurtherIndep

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem flag_further_term_independent :
    GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorFibreVariety.proof
    (GroundTheory.Heights₂.Heights.NumbersDVR.FullFlagVerticalSymmetric.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorFibreVariety.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.FullFlagRestriction.proof
      FurtherIndep.segreFlagIndep)

end GlobalTheory.CompanionTheory.Ar.Num
