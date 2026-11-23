import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingConjugateComponentAdelic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marking_conjugate_component_adelic : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → (Dw.p = 0 ∨ Dw.q = 0 ∨ 3 ≤ Dw.p + Dw.q) → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (Cv : Curve H) (io : Cv.P.A.left ⟶ Cv.P.A.left) (s : ℤ × ℤ) (π : Fin C.F.n → Fin C.F.n), Cv.ActsBy τ io l.M s → ConjugationPermutesPeriods C.F τ π → ∀ h γ k h' γ', C.Mark h k γ → C.Mark h' (π k) γ' → ∃ δ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ finHom V (γ' * h') * finHom V u = finHom V δ * finHom V (γ * h) ∧ ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((wE H s ^ Dw.p * H.bar (wE H s) ^ Dw.q : 𝓞 D.host.E) : D.host.E)) - 1 ∈ GlobalTheory.AdLat.hat1 D.host.F ((algebraMap (𝓞 D.host.E) D.host.E) '' (l.Mb : Set (𝓞 D.host.E))) := by
  first | exact @GlobalTheory.ConjMark.marking_of_conjugate | exact GlobalTheory.ConjMark.marking_of_conjugate | (intros; apply GlobalTheory.ConjMark.marking_of_conjugate <;> assumption)
