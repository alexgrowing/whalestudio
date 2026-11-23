import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CharacterLevelCondition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.RcUnlinkedChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalContragredientMonomial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl

open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem away_eq_of_plainTor : UpperTheory.Gal.ToralGalois.Inq → ToralGal → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ → PlainTor (algNorm σ) → (wdOf h hl ι r).mono0 ∧ ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → wdOf h hl ι r = rc (algNorm σ) := by
  intro hI hT E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w hl A h σ hσ hp
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.adicCompletion E) (algNorm σ) hp
  obtain ⟨a0, ha0⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  refine ⟨(hT E Ω l ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hs hu a0 ha0).1, ?_⟩
  rintro rc ⟨a, ha, H⟩
  obtain ⟨h1, h2⟩ := hT E Ω l ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hs hu a ha
  obtain ⟨h3, h4⟩ := GlobalTheory.RoadU.UnlinkedChars.rc_unlinked_chars hI Ω E w A h a ha rc H (algNorm σ) n ξ hξ hs hu
  exact GlobalTheory.WeakTheRep.eq_of_mono0_charPol _ _ h1 h3 fun g => (h2 g).trans (h4 g).symm

end GlobalTheory.RoadU
