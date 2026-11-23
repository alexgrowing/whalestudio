import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory

theorem fibre_comparison : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E)) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) , (∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la') → Module.finrank ℂ A.V = g → ∃ T₀ : ℝ, ∀ (w : ℂ) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr, T₀ < w.im → IsPeriod (Fu.Di i) ty P → Fu.u i P = y₀ → IsFibAt A Xo.univ.t lin cst w y₀ π fr → Function.Surjective π ∧ ∃ (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La), (∀ v, (Fu.ex i P (h v)).left = (π v).left) ∧ (∀ u, P u = h (A.Pw w (gam u))) ∧ (∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v) ∧ ∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k := by
  intro _ _ E _ _ _ H _ D l Xo σ g ty Fu A lin cst halt hdim
  refine ⟨0, fun w i P y₀ π fr _ hP hy hF => ?_⟩
  subst hy
  have hrk : Module.finrank ℤ A.La = 2 * g := by
    rw [A.finrank_La, ← Module.finrank_mul_finrank ℝ ℂ A.V, Complex.finrank_real_complex, hdim]
  obtain ⟨h, gam, h1, h2, h3, -, h5⟩ := fibre_hom_eq_exponential Fu i hP hdim hrk A.EF A.EF_bijective (A.Pw w) π
    hF.add hF.hol hF.per fr hF.fr_hol (fun j v hv => ((hF.frm v).1 j hv).ne_zero)
    (fun j j' v hv => (hF.frm v).2 j j' hv) (lin w) (cst w) (fun a j v hv => hF.fac a v j hv) (halt w)
  obtain ⟨h6, gamO, h7⟩ := h5 (fun e => A.actV e) hF.act (A.Pw_smul w)
  refine ⟨fun y => ?_, h.toContinuousLinearEquiv, gamO.symm, fun v => ?_, fun u => ?_, fun u v => ?_, h6⟩
  · obtain ⟨z, rfl⟩ := Fu.ex_onto i P hP y
    exact ⟨h.symm z, by rw [h1, h.apply_symm_apply]⟩
  · rw [h1]; rfl
  · change P u = h _
    rw [h2, ← h7, gamO.apply_symm_apply]
  · rw [← h3, ← h7, ← h7, gamO.apply_symm_apply, gamO.apply_symm_apply]

end GlobalTheory
