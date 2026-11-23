import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.StmtPhi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FmapOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PerCHk
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PhiAIter
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.MuNu
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.MuNu
import Development.WeilBound.CoreStatements.PadicHodgeComparison.KatzMessingTheorem.PullDSchMapId
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TiltSectionUnits.FcIsUnitSub
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.IsUOfIsUnit

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def pull' (Amp : ∀ M : Model l K, E.LineData M.X → Prop) {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p}
    {a : (dat Amp).Ch M} {b : (dat Amp).Ch N} (_ : (dat Amp).Mo u hu a b) (j : ℕ) :
    ((dat Amp).H' b).N j →+ ((dat Amp).H' a).N j :=
  (Model.pullH u hu true j).lim.toAddMonoidHom

theorem fmap (r : Res l K) [FiniteDimensional ℚ_[l] K] (Amp : ∀ M : Model l K, E.LineData M.X → Prop) :
    Nonempty (FMap Model.Sm r.perC r.iso (dat Amp) (pull' Amp)) := by
  obtain ⟨N, hT⟩ := teich r
  obtain ⟨F, -⟩ := fac_ex r hT (fun M n j x => Mid.mu_nu r N hT M n j x) (w_phi r) (fun g w => w_fix r g w)
  exact fmap_of r Amp N F _ r.perC.c r.perC.ι r.perC.φ r.perC.σ r.perC.q r.perC.k (factsC l K r).1 (facts l K)
    (perC_hk r) (perC_hl r) (perC_hφk r) (perC_hσk r) (w_fix r) (fun M hM j => lw_fin r M hM j)
    (fun M _ j x => CompanionTheory.KM.Cris.pullD_schMap_id l r.ρ M.p (Category.id_comp _) j x)

end CrystallineSemistableComparison.Pb
