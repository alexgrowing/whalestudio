import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.ExphOn

open Set GlobalTheory.ChartGlue

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

theorem dtrans_self (c : AlgChart p σ d) {y : CxPts p σ} (hy : y ∈ c.e.source) (ξ : Fin d → ℂ) :
    c.dtrans c y ξ = ξ := by
  have e : c.e ∘ c.e.symm =ᶠ[𝓝 (c.e y)] id :=
    eventually_of_mem (c.e.open_target.mem_nhds (c.e.map_source hy)) fun v hv => c.e.right_inv hv
  funext b
  simp only [AlgChart.dtrans, e.fderiv_eq, fderiv_id, ContinuousLinearMap.id_apply]

theorem dtrans_dtrans (c c' c'' : AlgChart p σ d) {y : CxPts p σ} (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source)
    (hy'' : y ∈ c''.e.source) (ξ : Fin d → ℂ) :
    c'.dtrans c'' y (c.dtrans c' y ξ) = c.dtrans c'' y ξ := by
  have ho := isOpen_over c.e c'.e.open_source
  have ho' := isOpen_over c'.e c''.e.open_source
  have h1 : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    (c.holo_trans c').differentiableAt (ho.mem_nhds (mem_over c.e hy hy'))
  have e1 : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have h2 : DifferentiableAt ℂ (c''.e ∘ c'.e.symm) ((c'.e ∘ c.e.symm) (c.e y)) := by
    rw [e1]
    exact (c'.holo_trans c'').differentiableAt (ho'.mem_nhds (mem_over c'.e hy' hy''))
  have e : (c''.e ∘ c'.e.symm) ∘ (c'.e ∘ c.e.symm) =ᶠ[𝓝 (c.e y)] c''.e ∘ c.e.symm :=
    eventually_of_mem (ho.mem_nhds (mem_over c.e hy hy')) fun v hv => by
      simp only [Function.comp_apply, c'.e.left_inv hv.2]
  have hc := fderiv_comp (c.e y) h2 h1
  rw [e.fderiv_eq] at hc
  funext b
  simp only [AlgChart.dtrans, hc, e1, ContinuousLinearMap.comp_apply]
  rfl

structure IsExphOn (a : ChartForm p σ d) (E : ChartMap p σ d) (W : Set (CxPts p σ)) (ε : ℝ) : Prop where

  trans : ∀ (c c' : AlgChart p σ d), ∀ y ∈ c.e.source, y ∈ c'.e.source → ∀ ξ, E c y ξ = E c' y (c.dtrans c' y ξ)

  cont : ∀ c : AlgChart p σ d, ∀ v ∈ c.e.target, c.e.symm v ∈ W → ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d,
    a c (c.e.symm v) ξ.ofLp < ε →
    ContinuousAt (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => E c (c.e.symm q.1) q.2.ofLp) (v, ξ)

  smooth : ∀ c c' : AlgChart p σ d, ∀ v ∈ c.e.target, c.e.symm v ∈ W → ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d,
    a c (c.e.symm v) ξ.ofLp < ε → E c (c.e.symm v) ξ.ofLp ∈ c'.e.source →
    ContDiffAt ℝ ∞ (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => c'.e (E c (c.e.symm q.1) q.2.ofLp)) (v, ξ)

  zero : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, y ∈ W → E c y 0 = y

  jets : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, y ∈ W → ∀ (ξ : ReciprocityTheory.L2DbarEstimates.V d) (n : ℕ),
    iteratedDeriv n (fun t : ℝ => c.e (E c y (t • ξ.ofLp))) 0 = jet (matIn a c) n (c.e y, ξ)

theorem IsExphOn.mono {a : ChartForm p σ d} {E : ChartMap p σ d} {W W' : Set (CxPts p σ)} {ε ε' : ℝ}
    (h : IsExphOn a E W ε) (hW : W' ⊆ W) (hε : ε' ≤ ε) : IsExphOn a E W' ε' where
  trans := h.trans
  cont c v hv hW' ξ hξ := h.cont c v hv (hW hW') ξ (hξ.trans_le hε)
  smooth c c' v hv hW' ξ hξ := h.smooth c c' v hv (hW hW') ξ (hξ.trans_le hε)
  zero c y hy hW' := h.zero c y hy (hW hW')
  jets c y hy hW' := h.jets c y hy (hW hW')

theorem isExphOn_empty (a : ChartForm p σ d) (ε : ℝ) : IsExphOn a (fun _ y _ => y) ∅ ε where
  trans _ _ _ _ _ _ := rfl
  cont _ _ _ h := h.elim
  smooth _ _ _ _ h := h.elim
  zero _ _ _ h := h.elim
  jets _ _ _ h := h.elim

end GlobalTheory.ChernReg.ExphOn
