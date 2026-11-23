import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CxStage

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.CxPts Formalism.BasicNotions

namespace GlobalTheory.ProjVar.Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv}

end GlobalTheory.ProjVar.Var

namespace GlobalTheory.TrueGeo

def cxSt (F : Type) [Field F] [NumberField F] : CxSt F := ProjVar.cxStage F

variable {F : Type} [Field F] [NumberField F]

theorem cxSt_cx : (cxSt F).cx = Var.cx := rfl

theorem cxSt_pn : (cxSt F).pn = Var.pn := rfl

variable {Y : Var F} {σ : F →+* ℂ} {Δ Δ' : Y.Dv}

example (n : ℕ) (y : Pts (proj F n) σ) : (cxSt F).mSmooth _ σ _ (projMet F σ n) ∧
    ∑ j, (cxSt F).pn _ σ _ (projMet F σ n)
      ((cxSt F).cx _ σ ((proj F n).coordFn (proj_gen_mem F n 0) j)) y = 1 ∧
    ((cxSt F).pn _ σ _ (projMet F σ n) ((cxSt F).cx _ σ 1) y = 0 ↔
      under y ∈ (proj F n).supp (projHyp F n)) := by
  have hy := (mSmooth_projMet F σ n).1 (mem_univ y)
  have he : (projHyp F n).Eff := (proj F n).eff_hyp _
  exact ⟨mSmooth_projMet F σ n, sum_pn_fsMet hy,
    ((pn_eq_zero_iff hy (secReg_cx_iff.2 (he _))).trans secZero_cx_iff).trans he.mem_supp_iff.symm⟩

example (c : ℂ) (y : Pts Y σ) :
    (cxSt F).pn Y σ 0 ((cxSt F).fsMet Y σ 0 fun _ : Unit => c • (cxSt F).cx Y σ 1)
      ((cxSt F).cx Y σ 1) y = 1 / ‖c‖ ^ 2 := by
  have hg : y ∈ eqnSet σ (0 : Y.Dv) 1 := isEqn_zero _
  have h₁ : HasVal y (Y.cx σ 1) 1 := map_one (Y.cx σ) ▸ hasVal_one
  change pn Y σ 0 (fsMet Y σ 0 fun _ : Unit => c • Y.cx σ 1) (Y.cx σ 1) y = _
  rw [pn_fsMet (fun _ => ⟨1, hg, ((h₁.smul c).mul h₁).regC⟩) hg, fval_one, h₁.val_eq]
  simp only [fval_one, (h₁.smul c).val_eq]
  simp

example : ¬ (cxSt F).mSmooth Y σ Δ ((cxSt F).fsMet Y σ Δ (k := Empty) Empty.elim) := fun h =>
  have ⟨y⟩ := nonempty_pts (Y := Y) (σ := σ)
  have ⟨k, _⟩ := (mSmooth_fsMet_iff.1 h y).2
  k.elim

end GlobalTheory.TrueGeo
