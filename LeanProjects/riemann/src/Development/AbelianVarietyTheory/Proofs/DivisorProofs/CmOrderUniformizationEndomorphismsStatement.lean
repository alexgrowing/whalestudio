import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmOrderUniformizationEndomorphisms
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_order_uniformization_endomorphisms : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)), c ≠ ⊥ → ∀ (𝔠 : FracId (FR E)) (L : Set E) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X)
      (α : orderC c → (X.A ⟶ X.A)) [∀ a, IsMonHom (α a)],
      (∀ (a : orderC c) w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α a) →
      Fil X.A = ⨆ i, ⨅ a : orderC c,
        Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) := by
  first | exact @GlobalTheory.FilCx.fil_eq_iSup_eigenspace_bar | exact GlobalTheory.FilCx.fil_eq_iSup_eigenspace_bar | (intros; apply GlobalTheory.FilCx.fil_eq_iSup_eigenspace_bar <;> assumption)
