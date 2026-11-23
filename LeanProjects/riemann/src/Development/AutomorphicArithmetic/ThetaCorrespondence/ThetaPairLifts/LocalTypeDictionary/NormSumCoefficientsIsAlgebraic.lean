import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumPairCoordinateAlgebraic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumPairCoordinateAlgebraicStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.NormSum.CoordAlg
open Classical Formalism.UG Formalism.UG.P Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.IntOver GlobalTheory.NormSum.RepAt GlobalTheory.NormSum.PtsMem
theorem normSum_coordinate_isAlgebraic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ (D : D7) (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q)
    (h : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n), IsAlgebraic ℚ (P.coord h U) := by
  intro _hPr hI D δ t0 Q P h U
  obtain ⟨S, dl, hL⟩ := GlobalTheory.NormSum.Denom.exists_letters D
  obtain ⟨p, hpQ, hp, k', hk', htr⟩ := exists_prime_integralOver_gt D P.d h Q
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ0 := P.level_pos
  have hsp : p ∣ Q → SplitIn D p := fun hd => absurd (Nat.le_of_dvd hQ0 hd) (by omega)
  obtain ⟨hterm, -, -⟩ := GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D (hI D) ⊤ δ t0 Q P.crv P.pt0 P hQ0
  have hmem : P.coord h U ∈ Qbar := by
    unfold Pair.coord
    refine finsum_induction (· ∈ Qbar) (zero_mem _) (fun x y => add_mem) (fun x => ?_)
    refine mul_mem (inv_mem (natCast_mem _ _)) ?_
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := (hI D).rep P.a p hp x.out
    rw [← hterm γ (Subgroup.subset_closure ⟨γ', h1⟩) k (Subgroup.subset_closure h2)]
    exact (CoordBound.term_bound_of_jets GlobalTheory.T.jets_torsion_translates_cm_theta_product D (hI D) S dl hL δ t0 Q P p hsp
      (CoordBound.nonempty_place p).some _ h k' hk' h3 htr U).1
  exact mem_algebraicClosure_iff.1 hmem
end GlobalTheory.NormSum.CoordAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSum_coefficients_isAlgebraic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ (D : D7) (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q)
    (h : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n), IsAlgebraic ℚ (P.coord h U) := by
  first | exact @_root_.GlobalTheory.NormSum.CoordAlg.normSum_coordinate_isAlgebraic | exact _root_.GlobalTheory.NormSum.CoordAlg.normSum_coordinate_isAlgebraic | (intros; apply _root_.GlobalTheory.NormSum.CoordAlg.normSum_coordinate_isAlgebraic <;> assumption)
end
