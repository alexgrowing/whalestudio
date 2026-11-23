import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IdxIs {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) (σ : c.F →+* ℂ) {r g : ℕ} (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r)
    (e : Fin g ≃ Lt1 Dw) : Prop :=
  (∀ x v j, pv X idx x v j = perFr X x v (relab c σ (e j).1) (e j).2) ∧ ∀ j, rowType X (idx j) = relab c σ (e j).1

def GenReads {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r g : ℕ} (U : Unf Xo c σ r) (k : U.Comp)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (x : (U.X k).dom) (ϑ : (Fin g → ℂ) → ℂ) : Prop :=
  letI : Algebra c.F ℂ := σ.toAlgebra
  ∃ A : AnFib (U.X k) bas idx e x.1 (U.X k).Λ (unC (Formalism.L2.PjFree.Unf.ofPj U) k x),
    A.Reads 1 (unC (Formalism.L2.PjFree.Unf.ofPj U) k x).s ϑ

variable {D : D7}

def AtComp (θ : InfFam D) (W : HSp D) {r : ℕ} (hr : W.rank = r) {Comp : Type} (X : Comp → Data D.host.E r)
    (dict : GA D W → Σ k, Frame (X k).Ψ r) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h γ : GA D W) : Prop :=
  γ ∈ GQ W ∧ latR hr (latG W (γ * h)) = (X (dict h).1).Λ ∧
    (dict h).2 = frMove θ W hr (X (dict h).1) (γ * h) (fun τ => x₀ τ.1)

def CcIs (θ : InfFam D) (V W : HSp D) {r : ℕ} (hr : W.rank = r) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (mu : GA D W → ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cc : U.Comp → ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ∀ h γ : GA D W, AtComp θ W hr U.X dict x₀ h γ →
    ∀ (hx' : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ)
      (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas →
      IdxIs c σ (U.X (dict h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads U (dict h).1 bas idx e ⟨(dict h).2, hx'⟩ ϑ →
      ∀ w : WO V W, w.map (finPart D) = 0 →
        om (1, γ * h) f₀ w = cc (dict h).1 * mu h *
          cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (U.X (dict h).1) bas idx (dict h).2
            (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b) (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b)) *
          ∏ b, ϑ (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b)

theorem CcIs.norm {θ : InfFam D} {V W : HSp D} {r : ℕ} {hr : W.rank = r} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r}
    {dict : GA D W → Σ k, Frame (U.X k).Ψ r} {mu : GA D W → ℂ} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ} {cc : U.Comp → ℂ}
    (h : CcIs θ V W hr U dict mu x₀ om f₀ cc) (k : U.Comp) : ‖cc k‖ = 1 := h.1 k

end

end GlobalTheory.AdTh
