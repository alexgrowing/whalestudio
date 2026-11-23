import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.ReadingWithSpecialisation

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

def IsCover (d : DeltaDat Xo c n) : Prop :=
  d.IsLev ∧ Nat.Coprime d.pd l.A ∧
    (∃ j : KA l →+* KA d.l₂, (∀ t, ((j t : KA d.l₂) : ℂ) = ((t : KA l) : ℂ)) ∧ d.r ≫ Xo.s = d.Xo₂.s ≫ spMap j) ∧
    ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂

def IsModulus (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (w : E)
    (v : TF n g) (ρ : ℝ) : Prop :=
  ∀ x ∈ X.dom, IsUnitFr X x → ∀ θ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x X.Λ θ →
    MeanOne X bas idx x X.Λ θ → ∀ z : Fin n → Fin g → ℂ, ‖∏ b, θ (z b)‖ = ρ * ‖thA X bas idx v x z‖

def ReadsWith {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (W : UW U) (k : U.Comp)
    {a : (E →+* ℂ) × ℕ → ℕ} (D : Dic Dw c σ (U.X k) g q0 n a) (v : TF n g) (κ : ℂ) : Prop :=
  ∀ d : DeltaDat Xo c n, IsCover d →
  ∀ σ₂ : d.c₂.F →+* ℂ, (∀ t : c.F, σ₂ (d.eF t) = σ t) →
  ∀ cv : (Dw.La →ₗ[𝓞 E] (Fin r → E)) → ℂ,
    @CvIs E _ _ _ r g n H Dw l Xo c d σ₂.toAlgebra (U.X k) D.bas D.idx D.e (U.X k).Λ cv →
  ∀ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₂ →
    MarkOver l d.l₂ (U.X k).Λ (W.mark k) mk₂ →
  ∀ (Cl : Type) [Fintype Cl] (Vs : Type) [AddCommGroup Vs] [Module c.F Vs]
    (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F)
    (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs)
    (Y : Cl → (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E),
    LatsOK d.l₂.M La Nc → (∀ cl, 0 < gam cl) →
    (∀ cl, io (xs cl) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) →
    (∀ cl, IsRoots d.l₂ (U.X k).Λ mk₂ (Nc cl) (Y cl)) →
  ∀ f ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f →
  ∀ x ∈ (U.X k).dom,
    Formalism.L2.PjFree.rdU U f k x = κ * cv mk₂ *
      clsSum σ (U.X k) D.hr D.bas D.idx D.eL w La Nc gam vol ep (fun cl => io (xs cl)) (U.X k).Λ v Y x

def ClassSumValues : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r),
    Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U →
    ∀ (W : UW U) (k : U.Comp) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
    ∀ (g q0 : ℕ) (D : Dic Dw c σ (U.X k) g q0 n a) (v : TF n g),
      IsVac (U.X k) D.bas (H.w0 : E) (tens (stdLat E n) (U.X k).Λ) v →
      ∃ κ : ℂ, κ ≠ 0 ∧ IsModulus (U.X k) D.bas D.idx (H.w0 : E) v ‖κ‖ ∧ ReadsWith U W k D v κ

theorem IsModulus.unique {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {w : E}
    {v : TF n g} {ρ ρ' : ℝ} (h : IsModulus X bas idx w v ρ) (h' : IsModulus X bas idx w v ρ')
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hu : IsUnitFr X x) {θ : (Fin g → ℂ) → ℂ}
    (h1 : IsTheta1 X bas idx w x X.Λ θ) (h2 : MeanOne X bas idx x X.Λ θ) {z : Fin n → Fin g → ℂ}
    (hz : thA X bas idx v x z ≠ 0) : ρ = ρ' :=
  mul_right_cancel₀ (norm_ne_zero_iff.mpr hz) ((h x hx hu θ h1 h2 z).symm.trans (h' x hx hu θ h1 h2 z))

end

end GlobalTheory.IndefiniteRowSideFullHecke.ReadingWithSpecialisation
