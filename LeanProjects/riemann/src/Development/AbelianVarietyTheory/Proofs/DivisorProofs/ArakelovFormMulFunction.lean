import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar BottChern ArRing ArChow HolAtlas Alt IsType IsReal dens chPart tdPart hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ArFormMul

theorem isArForm_fn_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (t : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (j : ℕ) (θ : h.Fld), h.IsArForm 0 (fun σ => (h.atlas σ).fn (t σ)) → h.IsArForm j θ → h.IsArForm j ((fun σ => (h.atlas σ).fn (t σ)) * θ) := by
  intro k _ X p D h t j θ hf hθ
  have hpt : ∀ σ (x : (h.atlas σ).Pt), ((fun σ => (h.atlas σ).fn (t σ)) * θ) σ x =
      ((t σ x.pt : ℝ) : ℂ) • θ σ x := fun σ x => by
    show algebraMap ℂ _ _ * θ σ x = _
    rw [Algebra.smul_def]
  refine ⟨fun σ => ⟨GlobalTheory.CxForm.FormMul.isForm_mul _ _ _ (hf.1 σ).1 (hθ.1 σ).1, fun x => ?_⟩, ?_⟩
  · rw [hpt]
    obtain ⟨hT, hR⟩ := (hθ.1 σ).2 x
    refine ⟨fun S hS => hT S ?_, fun S => ?_⟩
    · intro h0; apply hS; rw [map_smul, Finsupp.smul_apply, h0, smul_zero]
    · rw [map_smul, map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, hR S, smul_eq_mul, smul_eq_mul, map_mul,
        Complex.conj_ofReal]
  · intro σ σ' x x' e hc
    have h0 := hf.2 σ σ' x x' e hc
    have h1 := hθ.2 σ σ' x x' e hc
    rw [pow_zero, one_smul] at h0
    show GlobalTheory.CxForm.swap ((h.atlas σ').fn (t σ') x' * θ σ' x') = _ • ((h.atlas σ).fn (t σ) x * θ σ x)
    rw [map_mul, h0, h1, mul_smul_comm]

end GlobalTheory.ArFormMul
