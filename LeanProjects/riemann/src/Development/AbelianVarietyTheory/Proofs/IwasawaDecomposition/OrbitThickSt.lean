import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PrimAn
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound

noncomputable section

namespace GlobalTheory.CuspFrom

section Analytic

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD

def FlowMajSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom → ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0 →
      X.maj (X.flow ξ s x) τ v = X.maj x τ v +
        ‖X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ^ 2 *
          (X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) - X.maj x τ (Data.emb τ.1 ξ))) ∧
    ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (v w : Fin r → ℂ),
      ‖hermC τ.1 X.Gm v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w ∧ ‖X.Hf x τ v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w

def OrbitThickSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ →
    ∀ x ∈ X.dom, ∃ ε : ℝ, 0 < ε ∧ ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom →
      ∏ τ, X.tt ξ (X.flow ξ s x) τ = ∏ τ, X.tt ξ x τ → ε ≤ X.la1 (X.flow ξ s x)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def ThickBdd (φ : Frame X.Ψ r → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x ∈ X.dom, ε ≤ X.la1 x → φ x ≤ C

def FreqNonneg (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ

def StepBound (w : ℝ) (φ : Frame X.Ψ r → ℝ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ q : X.Ψ → ℝ, (∀ τ, 0 < q τ ∧ q τ ≤ 1) → ∀ B : ℝ,
    (∀ s : X.Ψ → ℝ, φ (X.flow ξ (fun τ => (s τ : ℂ) + I * (((q τ - 1) * X.tt ξ x τ : ℝ) : ℂ)) x) ≤ B) →
    φ x ≤ B * ∏ τ, q τ ^ (-w)

end Analytic

section Geometric

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Toroidal GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def FlowTie {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} [Algebra (FractionRing ℂ) ℂ] (Uw : UnfWit U)
    {O : Type} [CommRing O] {β : O →+* c.F} (a : ArcIn Dw l β ℂ (σ.comp β)) (k : U.Comp) (ξ' : Fin r → E)
    (x : Frame (U.X k).Ψ r) : Prop :=
  ∀ (Y : Model Xo c β) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F),
    ∃ (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)),
      (∀ τ, 0 < d τ) ∧ (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i j, z τ i j ≠ 0 → (Uw.e j).1 = τ) ∧
      ∀ w : ℂ, T < w.im → ∃ hx : (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom,
        AnLie Uw.F Ha.i (Ha.Pw w) (U.un k ⟨_, hx⟩) z

def BdExt {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {V K : Type} [CommRing V] [IsLocalRing V] [Field K]
    [Algebra V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K) : Prop :=
  ∃ (χ : Sp V ⟶ gen Z) (g : EigFrame Z φ (χ ≫ genι Z)), χ ≫ genStr Z = spMap φ ∧
    GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ ∧
    (∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y ∧
      w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (algebraMap V K)) ≫ g.v τ i) ∧
    χ (IsLocalRing.closedPoint V) ∈ genBd Z

end Geometric

end GlobalTheory.CuspFrom
