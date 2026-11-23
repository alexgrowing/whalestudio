import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfGluedPullbacksReduced
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_glued_pullbacks_reduced : ∀ {S X₀ : Scheme.{0}} {I : Type} (V X : I → Scheme.{0}) (κ : ∀ i, V i ⟶ S) (g : ∀ i, X i ⟶ V i)
    (B : I → I → Scheme.{0}) (a : ∀ i k, B i k ⟶ X i) (b : ∀ i k, B i k ⟶ X k) (j : ∀ i, X₀ ⟶ X i)
    (jB : ∀ i k, X₀ ⟶ B i k), (∀ i, IsOpenImmersion (κ i)) →
    (∀ i k, IsPullback (a i k) (b i k ≫ g k) (g i ≫ κ i) (κ k)) →
    (∀ i k, IsPullback (b i k) (a i k ≫ g i) (g k ≫ κ k) (κ i)) → (∀ i, IsReduced (X i)) →
    (∀ i, (X i).IsSeparated) → (∀ i, IsDominant (j i)) → (∀ i k, jB i k ≫ a i k = j i) →
    (∀ i k, jB i k ≫ b i k = j k) →
    ∃ (A : Scheme.{0}) (F : A ⟶ S) (ψ : ∀ i, X i ⟶ A),
      (∀ i, IsPullback (ψ i) (g i) F (κ i)) ∧ ∀ i k, IsPullback (a i k) (b i k) (ψ i) (ψ k) := by
  first | exact @GlobalTheory.SchGlue.exists_glue_of_dense | exact GlobalTheory.SchGlue.exists_glue_of_dense | (intros; apply GlobalTheory.SchGlue.exists_glue_of_dense <;> assumption)
