import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.MeasRd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

def ratAt : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i)

def ExactAt : Prop :=
  ∀ (σ : D.what₂.LL →+* ℂ) (f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n),
    nrmR p.R.toRealDat i σ ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) =
      Real.sqrt (ratAt p i) * petW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)
        (σ.comp (algebraMap p.T.Q.c.F D.what₂.LL)) f

theorem measAt_of (h : ExactAt p i) (hr : 0 < ratAt p i) {K₁ K₂ : ℝ} (h1 : 0 ≤ K₁) (h2 : 0 ≤ K₂)
    (hu : Real.log (ratAt p i) ≤ K₁ * unitE p) (hl : -(K₂ * unitE p) ≤ Real.log (ratAt p i)) :
    MeasAt p i ((K₁ + K₂) / 2) := by
  intro σ
  refine ⟨Real.sqrt (ratAt p i), Real.sqrt_pos.2 hr, ?_, fun f => h σ f⟩
  rw [Real.log_sqrt hr.le]
  have key : |Real.log (ratAt p i)| ≤ (K₁ + K₂) * unitE p := by
    rcases le_or_gt 0 (unitE p) with hu0 | hu0
    · rw [abs_le]; constructor <;> nlinarith
    · have hs : K₁ + K₂ = 0 := by nlinarith
      have e1 : K₁ = 0 := by linarith
      have e2 : K₂ = 0 := by linarith
      subst e1 e2
      have : Real.log (ratAt p i) = 0 := by
        apply le_antisymm <;> simp_all
      rw [this, hs]; simp
  rw [abs_div, abs_two]
  have : |Real.log (ratAt p i)| / 2 ≤ (K₁ + K₂) * unitE p / 2 := by linarith
  linarith [this, show (K₁ + K₂) * unitE p / 2 = (K₁ + K₂) / 2 * unitE p by ring]

end GlobalTheory.CovTop.MeasRd

end
