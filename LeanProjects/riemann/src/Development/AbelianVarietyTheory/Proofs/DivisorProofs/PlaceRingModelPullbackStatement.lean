import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingModelPullback
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_ring_model_pullback : GlobalTheory.Published.AbelianDeRham →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ), IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (L : Set E) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left),
      X.IsPullBy X₀ (spMap R.subtype) p → ∀ i : I, ∃ (e : X₀.Lie →ₗ[R] R) (a : ℂ), a ≠ 0 ∧ IsPeriodGen X₀ U p i e a ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e := by
  first | exact @GlobalTheory.LatModel.EigenForm.exists_periodGen | exact GlobalTheory.LatModel.EigenForm.exists_periodGen | (intros; apply GlobalTheory.LatModel.EigenForm.exists_periodGen <;> assumption)
