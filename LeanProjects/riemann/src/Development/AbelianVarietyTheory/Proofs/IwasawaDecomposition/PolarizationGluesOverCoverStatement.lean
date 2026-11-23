import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationGluesOverCover
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
theorem _root_.GlobalTheory.T.polarization_glues_over_cover : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F} {b : ∀ i, 𝓞 c.F →+* R i}
    {ω : ∀ i, R i →+* c.F} (C : ∀ i, Model Xo c (ω i)) (BD : ∀ i, EffCartierData (C i).X) (φ : InvFun (𝓞 E)) (m : ℕ)
    (A : Scheme.{0}) (F : A ⟶ Sp (𝓞 c.F)) (t : SAB H A) (ψ : ∀ i, (C i).X ⟶ A) (B : I → I → Scheme.{0})
    (p : ∀ i k, B i k ⟶ (C i).X) (q : ∀ i k, B i k ⟶ (C k).X), IsCover (algebraMap (𝓞 c.F) c.F) R a b ω →
    (∀ i, IsPullback (ψ i) (C i).s F (spMap (b i))) → (∀ i k, IsPullback (p i k) (q i k) (ψ i) (ψ k)) →
    (∀ i, Nonempty (SABMap (C i).t t (ψ i))) → (∀ i, IsPol φ m (C i) (BD i)) →
    (∀ i k, (BD i).idealSheaf.comap (p i k) = (BD k).idealSheaf.comap (q i k)) → IsProjOver F := by
  first | exact @GlobalTheory.GlueProj.isProjOver_of_glue | exact GlobalTheory.GlueProj.isProjOver_of_glue | (intros; apply GlobalTheory.GlueProj.isProjOver_of_glue <;> assumption)
