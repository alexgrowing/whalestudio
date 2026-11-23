import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianGluesOverCover
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
theorem _root_.GlobalTheory.T.semiabelian_glues_over_cover : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F} {b : ∀ i, 𝓞 c.F →+* R i}
    {ω : ∀ i, R i →+* c.F} (C : ∀ i, Model Xo c (ω i)) (A : Scheme.{0}) (F : A ⟶ Sp (𝓞 c.F)) (ψ : ∀ i, (C i).X ⟶ A)
    (t : SAB H A) (n : ∀ i, SABMap (C i).t t (ψ i)) (i₀ : I), IsCover (algebraMap (𝓞 c.F) c.F) R a b ω →
    (∀ i, IsPullback (ψ i) (C i).s F (spMap (b i))) → (∀ i k, (C i).j ≫ ψ i = (C k).j ≫ ψ k) →
    Geo.Tor.IsNormalScheme A → IsProjOver F → Flat F →
    ∃ (Z : GMod Xo c) (u : ∀ i, (C i).X ⟶ Z.X), ∀ i, IsChartOf Z (C i) (a i) (b i) (u i) := by
  first | exact @GlobalTheory.GlueModel.exists_gmod_charts | exact GlobalTheory.GlueModel.exists_gmod_charts | (intros; apply GlobalTheory.GlueModel.exists_gmod_charts <;> assumption)
