import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.CechPic

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

structure MLine (p : X ⟶ Sp k) (σ : k →+* ℂ) where

  B : LB X

  φ : Weight p σ B

  cInf : φ.IsCInf

namespace MLine

def ofHerm (L : HermLB p) (σ : k →+* ℂ) : MLine p σ := ⟨L.B, L.φ σ, L.cInf σ⟩

def tens (A B : MLine p σ) : MLine p σ := ⟨CechPic.tens A.B B.B, A.φ.tens B.φ, A.cInf.tens B.cInf⟩

def dual (A : MLine p σ) : MLine p σ := ⟨CechPic.dual A.B, A.φ.dual, A.cInf.dual⟩

def pull (A : MLine p σ) {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : MLine q σ :=
  ⟨A.B.pull π, A.φ.pull π hπ, A.cInf.pull π hπ⟩

def ofFun (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) : MLine p σ :=
  ⟨LB.triv X, Weight.ofFun u, Weight.isCInf_ofFun hu⟩

def addFn (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) : MLine p σ :=
  ⟨A.B, A.φ.addFn u, A.cInf.addFn hu⟩

def Isom (L M : MLine p σ) : Prop :=
  ∃ w : LB.Iso L.B M.B, w.IsGen ∧ ∀ (a : M.B.ι) (b : L.B.ι) (y : CxPts p σ),
    y ∈ ptsIn p σ (M.B.U a) → y ∈ ptsIn p σ (L.B.U b) →
      M.φ.φ a y = L.φ.φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2)

def logSec (M : MLine p σ) (s : M.B.Sec) (y : CxPts p σ) : ℝ := Real.log (M.φ.nsq (secVal p σ s) y) / 2

end MLine

abbrev ptMap {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (σ : k →+* ℂ) : CxPts q σ → CxPts p σ :=
  PtsOver.map π hπ (spMap σ)

def dens (L : Fin D → MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) : ℝ :=
  (Real.pi ^ D)⁻¹ * (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
    c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB y) y j l).det).re

def part (L : Fin D → MLine p σ) (ε : ℤˣ) : Measure (CxPts p σ) :=
  glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal ((ε : ℤ) * dens L c y)

def Intg (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : Prop := Integrable f (part L 1) ∧ Integrable f (part L (-1))

def int (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : ℝ := ∫ y, f y ∂part L 1 - ∫ y, f y ∂part L (-1)

def clos (z : X) : Scheme.{0} := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subscheme

def closι (z : X) : clos z ⟶ X := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι

instance (z : X) : IsClosedImmersion (closι z) :=
  inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι)

def CycIntg (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) (z : X) : Prop :=
  Intg (fun i => (L i).pull (closι z) rfl) fun y => f (ptMap (closι z) rfl σ y)

def cycInt (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) (z : X) : ℝ :=
  int (fun i => (L i).pull (closι z) rfl) fun y => f (ptMap (closι z) rfl σ y)

def side [IsIntegral X] [IsLocallyNoetherian X] (N : MLine p σ) (L : Fin D → MLine p σ) (f g : CxPts p σ → ℝ)
    (Δ : CartierDiv X) : ℝ :=
  int (Fin.cons N L : Fin (D + 1) → MLine p σ) f + ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L g z

theorem dens_const (N : MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) :
    dens (fun _ => N) c y = c.chernDens N.φ y := by
  have e : (Matrix.of fun j l => c.hess N.φ (pick N.φ.isLB y) y j l) = c.hess N.φ (pick N.φ.isLB y) y := rfl
  simp only [dens, AlgChart.chernDens, e, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
  ring

theorem part_const (N : MLine p σ) (ε : ℤˣ) : part (fun _ : Fin D => N) ε = N.φ.chernPart D ε := by
  simp only [part, Weight.chernPart, dens_const]

section Generic

variable (t : X ⟶ Sp ℤ)

def gX : Scheme.{0} := pullback t (spMap (Int.castRingHom ℚ))

def gj : gX t ⟶ X := pullback.fst _ _

def gq : gX t ⟶ Sp ℚ := pullback.snd _ _

def gΦ (z : CxPts (gq t) (Rat.castHom ℂ)) : CxPts t (Int.castRingHom ℂ) :=
  ⟨z.1 ≫ gj t, specZIsTerminal.hom_ext _ _⟩

theorem continuous_gΦ : Continuous (gΦ t) := continuous_of_comp (f := gj t) fun _ => rfl

variable {t}

theorem cInfAt_gΦ {f : CxPts t (Int.castRingHom ℂ) → ℝ} {z : CxPts (gq t) (Rat.castHom ℂ)} (h : CInfAt f (gΦ t z)) :
    CInfAt (fun w => f (gΦ t w)) z := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have e (a : Γ(X, W)) (w : CxPts (gq t) (Rat.castHom ℂ)) :
      ev (gq t) _ (gj t ⁻¹ᵁ W) ((gj t).app W a) w = ev t _ W a (gΦ t w) := (valR_comp w.1 (gj t) W a).symm
  refine ⟨gj t ⁻¹ᵁ W, ι, inferInstance, fun a => (gj t).app W (g a), F, O, h₁, h₂, ?_, h₄, ?_⟩
  · simpa only [e] using h₃
  · simp only [e]
    exact (continuous_gΦ t).continuousAt.eventually h₅

def MLine.gen (A : MLine t (Int.castRingHom ℂ)) : MLine (gq t) (Rat.castHom ℂ) where
  B := A.B.pull (gj t)
  φ := A.φ.linComb (κ := PUnit) (fun _ => gj t) (fun _ => 1) (fun _ => gΦ t) fun _ _ => rfl
  cInf j z hz := (cInfAt_gΦ (A.cInf _ _ (mem_of_mem_linComb (m := fun _ => gΦ t z)
    (fun _ => rfl) hz PUnit.unit))).congr (.of_forall fun w => by simp [Weight.linComb])

end Generic

end GlobalTheory.Mix
