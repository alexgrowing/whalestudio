import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulipointLiftToFinerLevelCompleteDVR
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulipoint_lift_to_finerLevel_completeDVR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l₂ : Level H) (Xo : Moduli Dw l) (Xo₂ : Moduli Dw l₂) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.Dvd l₂ → l₂.A = l.A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∃ (c₂ : Coeff l₂) (la₂ : HeightOneSpectrum (𝓞 c₂.F)) (T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V) (e' : ℕ) (io₂ : c₂.F →+* T'.Fr) (e₂ : ℕ) (x₂ : Sp T'.Fr ⟶ Xo₂.X) (r : Xo₂.X ⟶ Xo.X) (_ : SABMap Xo₂.univ.t Xo.univ.t r), 0 < e' ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e' : ℤ) * vV T.V a) ∧ (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) ∧ OverLa la₂ T'.V io₂ e₂ ∧ x₂ ≫ Xo₂.s = spMap (io₂.comp (IntermediateField.inclusion c₂.le).toRingHom) ∧ x₂ ≫ r = spMap iT ≫ x := by
  first | exact @GlobalTheory.LevelLift.lift_to_finer_level | exact GlobalTheory.LevelLift.lift_to_finer_level | (intros; apply GlobalTheory.LevelLift.lift_to_finer_level <;> assumption)
