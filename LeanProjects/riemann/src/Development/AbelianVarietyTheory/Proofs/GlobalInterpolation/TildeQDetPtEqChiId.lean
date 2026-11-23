import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MkDetPtEqRelDetQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubStdL

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.ChiDet

theorem tildeQ_detPt_eq_chiId : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ) (C : GlobalTheory.Mem.Chr.HFrame H e) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))), letI := H.cmStar; ∀ (p : DecoF H.E n ST SG Q), LevOk H SG SQ → ((tildeQ H SQ C.chiPsi (detPt H SQ p) : ℂˣ) : ℂ) = chiId C.chiPsi (Th.detId H (Th.stdL H n) p.deco.1.N) := by
  intro R H e C n ST SG Q SQ
  letI := H.cmStar
  intro p hL
  have hχ := C.isChi
  have hK := (GlobalTheory.Mem.KerDet.kernel_open_and_factor R H).2.2.2 C.chiPsi hχ.triv (fun v y hy _ => hχ.unr v y hy)
    fun v _ => hχ.unr v
  rw [tildeQ_eq_comp H SQ hK, MonoidHom.comp_apply]
  exact tildeD_eq_chiId R H C.chiPsi hχ n _ p.deco.2.lat _
    (congrArg (toDtTMod H SQ) (mk_detPt_eq_relDetQ R H n ST SG Q SQ p hL))

end GlobalTheory.Mem.ChiDet
