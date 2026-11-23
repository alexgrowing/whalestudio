import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity

set_option autoImplicit false

noncomputable section

open Set Topology
open ReciprocityTheory.AnForm.M (LocPot)

namespace GlobalTheory.ClopenPush

open scoped Classical

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (u : Y → X)

open scoped Classical in

def pot (hu : IsOpenEmbedding u) (hc : IsClosed (range u)) (P : LocPot Y) : LocPot X where
  U x := if h : x ∈ range u then u '' P.U h.choose else (range u)ᶜ
  isOpen_U x := by
    by_cases h : x ∈ range u
    · rw [dif_pos h]
      exact hu.isOpenMap _ (P.isOpen_U _)
    · rw [dif_neg h]
      exact hc.isOpen_compl
  mem_U x := by
    by_cases h : x ∈ range u
    · rw [dif_pos h]
      exact ⟨h.choose, P.mem_U _, h.choose_spec⟩
    · rw [dif_neg h]
      exact h
  φ x z := if h : x ∈ range u then (if hz : z ∈ range u then P.φ h.choose hz.choose else 0) else 0

open scoped Classical in

def sec (s : Y → Y → ℂ) : X → X → ℂ :=
  fun x z => if h : x ∈ range u then (if hz : z ∈ range u then s h.choose hz.choose else 0) else 0

variable {u}

omit [TopologicalSpace X] [TopologicalSpace Y] in

theorem choose_eq (hi : Function.Injective u) {y : Y} (h : u y ∈ range u) : h.choose = y :=
  hi h.choose_spec

variable (hu : IsOpenEmbedding u) (hc : IsClosed (range u)) (P : LocPot Y) (s : Y → Y → ℂ)

theorem pot_U_up (y : Y) : (pot u hu hc P).U (u y) = u '' P.U y := by
  change (if h : u y ∈ range u then u '' P.U h.choose else (range u)ᶜ) = _
  rw [dif_pos (mem_range_self y), choose_eq hu.injective]

theorem pot_φ_up (y y' : Y) : (pot u hu hc P).φ (u y) (u y') = P.φ y y' := by
  change (if h : u y ∈ range u then (if hz : u y' ∈ range u then P.φ h.choose hz.choose else 0)
    else 0) = _
  rw [dif_pos (mem_range_self y), dif_pos (mem_range_self y'), choose_eq hu.injective,
    choose_eq hu.injective]

theorem pot_U_subset {x : X} (hx : x ∈ range u) : (pot u hu hc P).U x ⊆ range u := by
  obtain ⟨y, rfl⟩ := hx
  rw [pot_U_up]
  exact image_subset_range _ _

theorem pot_U_of_not {x : X} (hx : x ∉ range u) : (pot u hu hc P).U x = (range u)ᶜ := by
  change (if h : x ∈ range u then u '' P.U h.choose else (range u)ᶜ) = _
  rw [dif_neg hx]

theorem pot_φ_of_not {x : X} (hx : x ∉ range u) (z : X) : (pot u hu hc P).φ x z = 0 := by
  change (if h : x ∈ range u then (if hz : z ∈ range u then P.φ h.choose hz.choose else 0)
    else 0) = _
  rw [dif_neg hx]

omit [TopologicalSpace X] [TopologicalSpace Y] in

theorem sec_up (hi : Function.Injective u) (y y' : Y) : sec u s (u y) (u y') = s y y' := by
  unfold sec
  rw [dif_pos (mem_range_self y), dif_pos (mem_range_self y'), choose_eq hi, choose_eq hi]

omit [TopologicalSpace X] [TopologicalSpace Y] in

theorem sec_of_not {x : X} (hx : x ∉ range u) (z : X) : sec u s x z = 0 := by
  unfold sec
  rw [dif_neg hx]

theorem normSec_up (y : Y) :
    GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.normSec (pot u hu hc P) (sec u s) (u y) = GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.normSec P s y := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.normSec, sec_up s hu.injective, pot_φ_up]

theorem normSec_of_not {x : X} (hx : x ∉ range u) :
    GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.normSec (pot u hu hc P) (sec u s) x = 0 := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.normSec, sec_of_not s hx, norm_zero, zero_mul]

end GlobalTheory.ClopenPush

namespace GlobalTheory.ClopenPush

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.ArchLim
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

def LiftsFns {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) : Prop :=
  ∀ (W : Y.Opens) (g : Γ(Y, W)) (y : CxPts q (σ.comp β)), y ∈ ptsIn q (σ.comp β) W →
    ∃ (V : (gen Z).Opens) (G : Γ(gen Z, V)), up j hj σ y ∈ ptsIn (genStr Z) σ V ∧
      ∀ y' : CxPts q (σ.comp β), up j hj σ y' ∈ ptsIn (genStr Z) σ V →
        y' ∈ ptsIn q (σ.comp β) W ∧ ev (genStr Z) σ V G (up j hj σ y') = ev q (σ.comp β) W g y'

end GlobalTheory.ClopenPush

end
