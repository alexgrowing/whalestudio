import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

noncomputable section

namespace GlobalTheory.DefPt

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames
  GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev Mats (Dw : Datum H) (S : Type) : Type := ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S

def part (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℕ := fun τ i => a (τ, i)

def Reads (Z : Comp Xo c) (y₀ : FrPt Xo c c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : TIdx (part Dw a) → c.F) (f : Rul Xo c) :
    Prop :=
  f ∈ suppOn Z ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (s : S),
    (∀ τ, IsUnit (Y τ).det) → IsUnit s → FrMap (Algebra.ofId c.F S) y₀ z → FrChg (fun τ => (Y τ)ᵀ) s z y →
      evR Xo c f y = s ^ n * tval (part Dw a) (fun I => algebraMap c.F S (x I)) Y

def LocFr (y₀ : FrPt Xo c c.F) (w : HeightOneSpectrum (𝓞 c.F)) (a : c.F) (B : Mats Dw c.F) : Prop :=
  a ≠ 0 ∧ (∀ τ, (B τ).det ≠ 0) ∧
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa w T.V io e → letI := io.toAlgebra
      ∀ y z : FrPt Xo c T.Fr, Integral T io y → FrMap (Algebra.ofId c.F T.Fr) y₀ z → y.x = z.x →
        ∃ (Y : Mats Dw T.V) (u : T.Vˣ), (∀ τ, IsUnit (Y τ).det) ∧
          FrChg (fun τ => ((B τ).map io * (Y τ).map (algebraMap T.V T.Fr))ᵀ) (io a * algebraMap T.V T.Fr u) z y

def ArchFr (y₀ : FrPt Xo c c.F) (σ : c.F →+* ℂ) (N : ℝ) (X : Mats Dw ℂ) : Prop :=
  0 < N ∧ (∀ τ, (X τ).det ≠ 0) ∧
    ∀ z y : FrPt Xo c (CAt σ), FrMap (Algebra.ofId c.F (CAt σ)) y₀ z → FrChg (S := CAt σ) (fun τ => (X τ)ᵀ) 1 z y →
      GlobalTheory.LamT.IsMetric y N fun _ => 1

structure PtData (Z : Comp Xo c) : Type where

  y₀ : FrPt Xo c c.F
  on : LiesOn Z y₀
  only : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x

  a : HeightOneSpectrum (𝓞 c.F) → c.F

  B : HeightOneSpectrum (𝓞 c.F) → Mats Dw c.F
  loc : ∀ w, LocFr y₀ w (a w) (B w)
  fin : {w | ¬ (a w = 1 ∧ B w = 1)}.Finite

  N : (c.F →+* ℂ) → ℝ

  X : (c.F →+* ℂ) → Mats Dw ℂ
  arch : ∀ σ, ArchFr y₀ σ (N σ) (X σ)

namespace PtData

variable {Z : Comp Xo c} (P : PtData Z)

def degLie (τ : E →+* ℂ) : ℝ := detDeg (fun w => P.B w τ) fun σ => P.X σ τ

def degTh : ℝ := lineDeg (fun σ => (Real.sqrt (P.N σ))⁻¹) fun w => (vAdd w (P.a w) : ℝ)

def matA (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (w : HeightOneSpectrum (𝓞 c.F)) :
    Matrix (TIdx (part Dw a)) (TIdx (part Dw a)) c.F := fibA (part Dw a) (P.a w ^ n) (P.B w)

def matY (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (σ : c.F →+* ℂ) :
    Matrix (TIdx (part Dw a)) (TIdx (part Dw a)) ℂ := fibY (part Dw a) ((Real.sqrt (P.N σ))⁻¹ ^ n) (P.X σ)

end PtData

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ)

def FibreAt (Z : Comp Xo c) (G : WTZ E) (s : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (_ : Nonempty ι) (L : Submodule (𝓞 c.F) (ι → c.F))
    (Y : (c.F →+* ℂ) → Matrix ι ι ℂ) (φ : (ι → c.F) →ₗ[c.F] Rul Xo c),
    Submodule.IsLattice c.F L ∧ (∀ σ, (Y σ).det ≠ 0) ∧ s ≤ slope_sq (matNorm Y) L / 2 ∧ Function.Injective φ ∧
    LinearMap.range φ = cuspOn U Z G ∧ (∀ x ∈ L, ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (φ x)) ∧
    ∀ σ x, ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) ξ G (φ x) z ≤ matNorm Y σ x

def defBound (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ) : ℝ :=
  (∑ τ : Psi H, (((size (part Dw a τ.1) : ℝ) / Dw.p + (n : ℝ) / 2) * c₁ - Real.log (dim (part Dw a τ.1)) / 2)) +
    (n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)

structure DefCase : Prop where
  q : Dw.q = 0
  p : 1 ≤ Dw.p
  good : ∀ p : ℕ, p.Prime → l.GoodAt p
  A : l.A = 1
  geo : FnAlgClosed Xo c
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  xi : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ

variable (Xo c) in

def FreePt {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) : Prop :=
  ∀ (g : G) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), levR (lev g) y y' → y'.x = y.x → g = 1

example (lev : Unit → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) :
    FreePt Xo c (G := Multiplicative Unit) lev := fun _ _ _ _ _ _ _ _ => rfl

end Point

section Eigen

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ)

set_option synthInstance.maxHeartbeats 400000 in

def eigSub : Submodule c.F (Rul Xo c) :=
  ⨅ g : G, LinearMap.ker (actLev (Xo := Xo) c lev g - ((χ g : (c.F)ˣ) : c.F) • (LinearMap.id : Rul Xo c →ₗ[c.F] Rul Xo c))

def eigLat (W : WTZ D.host.E) : Submodule (𝓞 c.F) (cuspW Xo c U W) :=
  latW U W ⊓ ((eigSub lev χ).comap (cuspW Xo c U W).subtype).restrictScalars (𝓞 c.F)

theorem eigLat_le (W : WTZ D.host.E) : eigLat U lev χ W ≤ latW U W := inf_le_left

end Eigen

end GlobalTheory.DefPt

end
