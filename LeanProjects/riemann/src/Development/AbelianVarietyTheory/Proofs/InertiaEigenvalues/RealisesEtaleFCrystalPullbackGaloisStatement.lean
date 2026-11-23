import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisesEtaleFCrystalPullbackGalois
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisesEtaleFCrystal_pullback_galois : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (E : FCrys l ↥(OL K)) (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∀ (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K)), (∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l)) → (∀ h ∈ GK K, g⁻¹ * h * g ∈ GK K) → ∀ (ρg : T ≃ₗ[ℤ_[l]] T), (∀ h h' : ↥(GK K), (h' : GQ l) = g⁻¹ * h * g → ∀ x, ρg (ρ h' x) = ρ h (ρg x)) → ∃ (gH : Hom (ainfObj K) ((ainfObj K).restrict σ)) (j' : (E.pullback σ).M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), (∀ x, gH.f x = Per.σA g x) ∧ Realises K (E.pullback σ) (ainfObj K) (ainfId K) T ρ j' ∧ ∀ z, j' (E.tr gH z) = TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j z) := by
  first | exact @GlobalTheory.Prism.PullGal.realises_pullback | exact GlobalTheory.Prism.PullGal.realises_pullback | (intros; apply GlobalTheory.Prism.PullGal.realises_pullback <;> assumption)
