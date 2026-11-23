import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionFlatWeight
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_section_flat_weight : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  GlobalTheory.Published.PrismaticDieudonneHodge →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x →
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)),
  ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (ϖ : O) (_ : Irreducible ϖ) (Zs : Scheme.{0})
    (f : Zs ⟶ Spec (.of O)) (D : LB Zs),
    IsIntegral Zs ∧ (∀ z : Zs, IsIntegrallyClosed (Zs.presheaf.stalk z)) ∧ IsProper f ∧ Flat f ∧ D.IsLB ∧
    (∃ t : (D.pull (reducedSpecialι f)).Gen, t.IsGen) ∧
    ∃ (sig : (D.pull (genericι f)).Gen) (κ : ℝ), sig.IsGen ∧
      ∀ w ∈ htValOn Z la, ∃ (p : ℕ) (_ : Fact p.Prime) (R : Type) (_ : CommRing R) (_ : Algebra R ℂ_[p])
        (φ : O →+* R), (Valued.v : Valuation ℂ_[p] NNReal).Integers R ∧ Function.Injective φ ∧ IsLocalHom φ ∧
        ∃ (ybar : Spec (.of R) ⟶ Zs) (y : Spec (.of ℂ_[p]) ⟶ genericFibre f) (e : (D.pull ybar).Gen)
          (cc : ℂ_[p]ˣ),
          ybar ≫ f = Spec.map (CommRingCat.ofHom φ) ∧
          y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R ℂ_[p])) ≫ ybar ∧
          e.IsGen ∧ IsCoord f D sig ybar y e cc ∧
          w s.sig = val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (cc : ℂ_[p]) ∧
          val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (algebraMap R ℂ_[p] (φ ϖ)) = (κ : EReal) := by
  first | exact @GlobalTheory.FlatModel.exists_model | exact GlobalTheory.FlatModel.exists_model | (intros; apply GlobalTheory.FlatModel.exists_model <;> assumption)
