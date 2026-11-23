import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaOfPolAV

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.ArInt

namespace GlobalTheory.ThetaRR

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def IsTate (f : X ⟶ X) (hf : f ≫ p = p) (L : HermLB p) (w : LB.Iso (L.pull f hf).B (L.pow 4).B)
    (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) : Prop :=
  ∀ (σ : k →+* ℂ) (a : (L.pow 4).B.ι) (b : (L.pull f hf).B.ι) (y : CxPts p σ),
    y ∈ ptsIn p σ ((L.pow 4).B.U a) → y ∈ ptsIn p σ ((L.pull f hf).B.U b) →
      ((L.pow 4).φ σ).φ a y + 4 * u σ y = ((L.pull f hf).φ σ).φ b y + u σ (PtsOver.map f hf _ y) +
        Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2)

theorem exists_isTate_zero {f : X ⟶ X} {hf : f ≫ p = p} {L : HermLB p}
    (h : (L.pull f hf).Isometric (L.pow 4)) : ∃ w, w.IsGen ∧ IsTate f hf L w fun _ _ => 0 := by
  obtain ⟨w, hw, h⟩ := h
  exact ⟨w, hw, fun σ a b y ha hb => by simpa using h σ a b y ha hb⟩

theorem IsTate.isometric {f : X ⟶ X} {hf : f ≫ p = p} {L : HermLB p}
    {w : LB.Iso (L.pull f hf).B (L.pow 4).B} (hw : w.IsGen) {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ}
    (h : IsTate f hf L w u) (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) :
    ((L.raise u hu hc).pull f hf).Isometric ((L.raise u hu hc).pow 4) := by
  refine ⟨w, hw, fun σ a b y ha hb => ?_⟩
  have e := h σ a b y ha hb
  have e₁ : (((L.raise u hu hc).pow 4).φ σ).φ a y = ((L.pow 4).φ σ).φ a y + 4 * u σ y := by
    refine (((L.raise u hu hc).φ σ).zpow_φ _ a y).trans ?_
    refine Eq.trans ?_ (congrArg (· + 4 * u σ y) ((L.φ σ).zpow_φ _ a y).symm)
    change _ * (_ + _) = _
    push_cast
    ring
  have e₂ : (((L.raise u hu hc).pull f hf).φ σ).φ b y =
      ((L.pull f hf).φ σ).φ b y + u σ (PtsOver.map f hf _ y) :=
    (((L.raise u hu hc).φ σ).pull_φ f hf b y).trans
      (congrArg (· + u σ (PtsOver.map f hf _ y)) ((L.φ σ).pull_φ f hf b y).symm)
  rw [e₁, e₂]
  exact e

end GlobalTheory.ThetaRR
