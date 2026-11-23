import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackCoverModelsScheme
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
theorem _root_.GlobalTheory.T.pullback_cover_models_scheme : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F} {b : ∀ i, 𝓞 c.F →+* R i}
    {ω : ∀ i, R i →+* c.F} (C : ∀ i, Model Xo c (ω i)) (A : Scheme.{0}) (F : A ⟶ Sp (𝓞 c.F)) (ψ : ∀ i, (C i).X ⟶ A),
    IsCover (algebraMap (𝓞 c.F) c.F) R a b ω → (∀ i, IsPullback (ψ i) (C i).s F (spMap (b i))) →
    (∀ i k, (C i).j ≫ ψ i = (C k).j ≫ ψ k) →
    (∀ x : A, ∃ i, x ∈ Set.range (ψ i)) ∧ Geo.Tor.IsNormalScheme A ∧ Flat F ∧ (∃ z : A ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧
      ∀ i, IsPreimmersion ((C i).j ≫ ψ i) ∧ Flat ((C i).j ≫ ψ i) ∧ IsDominant ((C i).j ≫ ψ i) ∧
        QuasiCompact ((C i).j ≫ ψ i) := by
  first | exact @GlobalTheory.GlueLoc.glue_local | exact GlobalTheory.GlueLoc.glue_local | (intros; apply GlobalTheory.GlueLoc.glue_local <;> assumption)
