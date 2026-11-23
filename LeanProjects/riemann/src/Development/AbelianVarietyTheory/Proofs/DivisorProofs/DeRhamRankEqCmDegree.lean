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
open TensorProduct

set_option autoImplicit false

namespace GlobalTheory.DeRham

theorem hdR_rank_eq_finrank_cm : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔠 : FracId (FR E)) (R : Type)
    [CommRing R] [IsDomain R] (X : Obj (FR E) 𝔠 (Sp R)) (n : ℕ), (HdR X.A ≃ₗ[R] (Fin n → R)) → n = Module.finrank ℚ E := by
  intro H E _ _ _ 𝔠 R _ _ X n e
  letI := X.grp
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim H.1 X.ab X.dim
  haveI := hfin
  haveI := hproj
  let e1 : Module.Dual R (primDR X.A) ≃ₗ[R] (Fin n → R) := e
  let e2 : primDR X.A ≃ₗ[R] Module.Dual R (Fin n → R) :=
    (Module.evalEquiv R (primDR X.A)).trans e1.symm.dualMap
  have hP : ∀ p : PrimeSpectrum R, Module.rankAtStalk (primDR X.A) p = n := by
    intro p
    rw [Module.rankAtStalk_eq_of_equiv e2, Module.rankAtStalk_eq_finrank_of_free,
      Module.finrank_eq_card_basis (Pi.basisFun R (Fin n)).dualBasis, Fintype.card_fin]
    rfl
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have h1 := hrk p
  rw [hP p] at h1
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h3
  rw [h1, ← h3, mul_comm]

end GlobalTheory.DeRham
