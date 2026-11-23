import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

structure ArchSec (Z : Comp Xo c) (la : Weight Dw) : Type where

  sig : Rul Xo c

  inv : Rul Xo c
  sig_mem : sig ∈ secZ Xo c (exOf Dw la 0)
  inv_mem : inv ∈ secZ Xo c (-exOf Dw la 0)
  idem_sig : idem Z * sig = sig
  idem_inv : idem Z * inv = inv
  mul_inv : sig * inv = idem Z

  cInf : (c.F →+* ℂ) → ℝ
  cInf_pos : ∀ σ, 0 < cInf σ
  norm_inf : ∀ σ, homN (U (goodOf c σ)) x (wtOf Dw la 0) sig '' framesOn (U (goodOf c σ)) Z = {cInf σ}

variable {U x} in

def ArchSec.ofConst {Z : Comp Xo c} {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ) :
    ArchSec U x Z la :=
  ⟨s.sig, s.inv, s.sig_mem, s.inv_mem, s.idem_sig, s.idem_inv, s.mul_inv, s.cInf, s.cInf_pos, s.norm_inf⟩

example (Z : Comp Xo c) (h : HasPts U Z) : Nonempty (ArchSec U x Z 0) := ⟨.ofConst (ConstSec.one x h)⟩

def Onto : Prop :=
  ∀ σ, GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) →
    4 * (finrank ℚ E * r) + 4 ≤ n →
    holSub0 (U σ).X (laU (U σ) a n) ≤ Submodule.span ℂ (rdU (U σ) '' (cusp Xo c U a n : Set (Rul Xo c)))

structure Laws : Prop where
  pos : 1 ≤ Dw.p + Dw.q
  lev : l.A = 1
  good : ∀ p : ℕ, p.Prime → l.GoodAt p
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  geo : FnAlgClosed Xo c
  xi : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x
  chi : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1
  det : ∀ σ, GoodEmb c σ → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1
  onto : Onto U
  line : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0

def IsFlatQuot (Z : Comp Xo c) (τ : Psi H) (f g : Rul Xo c) : Prop :=
  ∀ σ, GoodEmb c σ → ∃ a : ℂ, a ≠ 0 ∧ ∀ k (hτ : relab c σ τ.1 ∈ ((U σ).X k).Ψ) y,
    (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      rdU (U σ) g k y = a * horizGen ⟨_, hτ⟩ y * rdU (U σ) f k y

def htValAt (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io) :
    Set (Rul Xo c → EReal) :=
  {w | ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra c.F ℂ_[p]) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p])
    (y : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y ∧
      w = fun f => val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (evR Xo c f y)}

def htValOn (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) :=
  {w | ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y₀ : IntFr Xo c T io),
    OverLa la T.V io e ∧ algOn Z T io y₀ ∧ w ∈ htValAt la y₀}

theorem htValOn_subset (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) : htValOn Z la ⊆ htValSet Xo c la := by
  rintro w ⟨T, io, e, y₀, ho, hz, p, hp, ha, k, y, hy, rfl⟩
  exact ⟨p, hp, ha, T, io, e, y₀, k, y, ho, hz.1, hy, rfl⟩

def Always (Q : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}, (∀ σ : c.F →+* ℂ, Unf Xo c σ r) → ℝ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → Q U x

def ArchEx : Prop := ∀ (Z : Comp Xo c) (τ : Psi H), Nonempty (ArchSec U x Z (flatWt Dw τ))

def HTConst : Prop :=
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)),
    ∃ ρ : ℝ, ∀ w ∈ htValOn Z la, w s.sig = (ρ : EReal)

variable (Xo c) in

def HTShift : Prop :=
  ∀ (τ : Psi H) (la : HeightOneSpectrum (𝓞 c.F)), ∃ κ : ℝ,
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y₀ : IntFr Xo c T io), OverLa la T.V io e → y₀.IsAlg →
      ∀ w ∈ htValAt la y₀, ∀ f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0), w f = nval T.V e (evI y₀ f) + (κ : EReal)

def FinConst : Prop :=
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)),
    ∃ ρ : ℝ, ∀ w ∈ valOn Z la, w s.sig = (ρ : EReal)

def FrameDeg (logOm : ℝ) : Prop :=
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ),
    (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) →
      (Function.support ρ).Finite ∧ lineDeg s.cInf ρ = ((Dw.p : ℝ) - Dw.q) / 2 * logOm

def CMDiffSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ →
    ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CM.CMObj H K ρ σ₁ p q)
      (F : CM.GenFib X.B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h →
      ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
        ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act τ) -
            ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) =
          ((p : ℝ) - q) / 2 * (CM.logOm E χ).re

def FlatDegreeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ →
    ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ),
      Laws U x → FlatDegree U x (CM.logOm E χ).re

end GlobalTheory.FlatCore

end
