import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeAdelicLatticeLocalizationEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionLattice_adelicLattice_localization_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E), (σ : E →+* E) = sp.cm.sig → ∀ (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (P : HeightOneSpectrum (𝓞 E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (compan (sp := sp) J a (latAd x Lb)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd x (compan (sp := sp) J a Lb)) := by
  first | exact @GlobalTheory.CompanLatAd.locP_companion_latAd | exact GlobalTheory.CompanLatAd.locP_companion_latAd | (intros; apply GlobalTheory.CompanLatAd.locP_companion_latAd <;> assumption)
