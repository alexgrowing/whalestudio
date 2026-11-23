import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Period
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchPack
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Branch

theorem periodNe_of_eigen : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.CuspRapidDecay → RealInputE → PeriodNe := by
  intro hHC hCW hCR hR
  have h0 := Cusp.exists_cusp_form_theta_period_ne_zero hHC hCW hCR (packEx_of_eigen hR) GlobalTheory.T.gridDepth_pays_every_loss
  intro ε CF hCF
  obtain ⟨x, hx⟩ := h0 ε CF hCF
  refine ⟨x, fun D large₂ e a b T L μ0 hL G W M hM M₀ MP t ht t0 w w0 => ?_⟩
  obtain ⟨y, hy, v, w', hp⟩ := hx D large₂ e a b T L μ0 hL G W M hM M₀ MP t ht t0
  obtain ⟨a', ha', hp'⟩ := GlobalTheory.PeriodNePf.exists_kf W M hM hCR hHC M₀ MP ht hy v w' hp w w0
  exact ⟨y, hy, a', ha', hp'⟩

end UpperTheory.Lit.Branch

end
