import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalClassTermEqVolumeMulProdOrbitalIntegrals
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalClassTerm_eq_volume_mul_prod_orbitalIntegrals : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) (qa : ∀ w : InfinitePlace F, XSet P w.Completion J), (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v).1) → (∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w).1) → Integrable (descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * ((∏ᶠ v, orbCls (μf v) (dtf v) (ff v) (qf v)) * ∏ w, orbCls (μa w) (dta w) (fa w) (qa w)) := by
  first | exact @GlobalTheory.TrClassTerm.class_term | exact GlobalTheory.TrClassTerm.class_term | (intros; apply GlobalTheory.TrClassTerm.class_term <;> assumption)
