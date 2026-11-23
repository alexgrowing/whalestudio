import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarryingSectionIntegralFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ErrorBudgetCondition

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovMult
open GlobalTheory.SlopeRec GlobalTheory.FlatLine GlobalTheory.RefSum
section Places
variable {K : Type} [Field K] [NumberField K]
end Places
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
theorem multC_of_refW_alt : _root_.GlobalTheory.RefSum.ReferenceWeight → (_root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) → _root_.GlobalTheory.CovHt.MultiplicityConstantCondition := by
  intro hR hK
  refine Closed.imp (Closed.and hR hK) fun _ _ _ ⟨⟨C₁, h₁, hR⟩, C₂, h₂, hK⟩ => ⟨C₁ + C₂, add_nonneg h₁ h₂, ?_⟩
  refine (hR.and hK).imp fun _ h x hx hle ι p hp i hi Y hY u1 hu => ?_
  obtain ⟨hR, hK⟩ := h x hx hle ι p hp
  obtain ⟨S, a, s, hS, hs, ha⟩ := hR i hi Y hY u1 hu
  obtain ⟨cc, hc0, hc, hZ⟩ := hK i hi Y hY u1 hu
  have hs0 : 0 ≤ s := (Finset.sum_nonneg fun q _ => mul_nonneg (hS.2.1 q) (Real.log_natCast_nonneg q)).trans hS.2.2.2
  exact ⟨cc + s, add_nonneg hc0 hs0, budget_add hs hc, fun Z => mult_of hY.1.unf hS ha (hZ Z)⟩
end GlobalTheory.CovMult
end
end
