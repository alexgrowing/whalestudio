import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCentralizerMeasuresFromUnitaryTorus
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_centralizer_measures_from_unitaryTorus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∃ ea ef e, IsCentProd L (ratEmb σ J γ) ea ef e ∧ (∃ 𝓣, IsFundamentalDomain ((ratPts σ J).subgroupOf (cent (ratEmb σ J γ))) 𝓣 e ∧ e 𝓣 = torVol P dt) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin r → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), gam h = proj σ J v (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dtf v)) f c ↔ HasOrbInt μ (proj σ J v (ratEmb σ J γ)) (ef v) f c) ∧ ∀ (w : InfinitePlace F) (x : plusUnits P w.Completion) (φ : (w.Completion ⊗[F] Fld P) ≃ₗ[w.Completion ⊗[F] E] (Fin r → w.Completion ⊗[F] E)) (h : IsIsom P w.Completion J x.1.1 φ), gam h = projArch σ J w (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dta w)) f c ↔ HasOrbInt μ (projArch σ J w (ratEmb σ J γ)) (ea w) f c := by
  first | exact @GlobalTheory.TrEllMeas.exists_isCentProd_torus | exact GlobalTheory.TrEllMeas.exists_isCentProd_torus | (intros; apply GlobalTheory.TrEllMeas.exists_isCentProd_torus <;> assumption)
