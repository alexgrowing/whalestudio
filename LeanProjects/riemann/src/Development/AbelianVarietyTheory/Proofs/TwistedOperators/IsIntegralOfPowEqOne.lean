import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section
namespace GlobalTheory.RowEx

theorem exists_nf_of_finite (S : Set ℂ) (hS : S.Finite) (hi : ∀ z ∈ S, IsIntegral ℚ z) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ S ⊆ Set.range (algebraMap M ℂ) := by
  haveI : Finite S := hS.to_subtype
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hi, fun z hz => ?_⟩
  exact ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩

theorem rootsOne_finite {n : ℕ} (hn : 0 < n) : {z : ℂ | z ^ n = 1}.Finite :=
  (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
    simpa [Polynomial.mem_nthRoots hn] using hz

theorem isIntegral_of_pow_eq_one {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z ^ n = 1) : IsIntegral ℚ z :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hn.ne', by simp [hz]⟩

theorem isIntegral_sqrt_nat (k : ℕ) : IsIntegral ℚ ((Real.sqrt k : ℝ) : ℂ) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C ((k : ℚ)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  have h0 : ((Real.sqrt k : ℝ) : ℂ) ^ 2 = (k : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  simp [Polynomial.eval₂_sub, h0]

end GlobalTheory.RowEx
end

namespace GlobalTheory.RowEx

theorem nfRoot : NFRoot := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hs ch _ _ => ?_⟩⟩
  haveI : Finite T := hs.fin
  classical
  set G := ch.G
  set S := ch.S.toGridChoice
  have hN : ∀ w : Pl D.host.E, 0 < Ideal.absNorm w.asIdeal ^ depthAt G w := fun w =>
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot)) _
  let P : Set (Pl D.host.E) := {w | w ∈ S.PA ∨ ∃ t, w ∈ locPl G t}
  have hP : P.Finite := by
    refine ((S.PA.finite_toSet).union (Set.finite_iUnion fun t => (locPl G t).finite_toSet)).subset ?_
    rintro w (hw | ⟨t, hw⟩)
    · exact Or.inl hw
    · exact Or.inr (Set.mem_iUnion.2 ⟨t, hw⟩)
  let Q : Set (Pl D.host.E) := ⋃ t, (locPl G t : Set (Pl D.host.E))
  have hQ : Q.Finite := Set.finite_iUnion fun t => (locPl G t).finite_toSet
  let X : Set ℂ := {z | z ^ 8 = 1} ∪ (⋃ w ∈ Q, {z : ℂ | z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1}) ∪
    (fun w : Pl D.host.E => ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ)) '' P
  have hX : X.Finite :=
    ((rootsOne_finite (by norm_num)).union (hQ.biUnion fun w _ => rootsOne_finite (hN w))).union (hP.image _)
  have hi : ∀ z ∈ X, IsIntegral ℚ z := by
    rintro z ((hz | hz) | ⟨w, -, rfl⟩)
    · exact isIntegral_of_pow_eq_one (by norm_num) hz
    · obtain ⟨w, -, hz⟩ := Set.mem_iUnion₂.1 hz
      exact isIntegral_of_pow_eq_one (hN w) hz
    · exact isIntegral_sqrt_nat _
  obtain ⟨M, hM, hMX⟩ := exists_nf_of_finite X hX hi
  refine ⟨M, hM, fun z hz => hMX (Or.inl (Or.inl hz)), fun t w hw z hz => hMX (Or.inl (Or.inr ?_)), fun w hw => hMX (Or.inr ⟨w, hw, rfl⟩)⟩
  exact Set.mem_iUnion₂.2 ⟨w, Set.mem_iUnion.2 ⟨t, hw⟩, hz⟩

end GlobalTheory.RowEx
