import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFormalGroupLawQuasiLogarithms
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstLiftXPowFrob
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_formalGroupLawQuasiLogarithms : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [Field k'] [CharP k' p] (σ : k →+* k') (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (hμ : IsLaw μ) (hμ' : IsLaw (fun i => MvPowerSeries.map σ (μ i))), ∀ f ∈ quasiLog p hμ, MvPowerSeries.map (frMap p σ) f ∈ quasiLog p hμ' ∧ (f ∈ intBy p k (Fin d) 1 → MvPowerSeries.map (frMap p σ) f ∈ intBy p k' (Fin d) 1) ∧ (∀ t, Red p (cob1 (fun i => Katz.lift p (μ i)) f) t → Red p (cob1 (fun i => Katz.lift p (MvPowerSeries.map σ (μ i))) (MvPowerSeries.map (frMap p σ) f)) (MvPowerSeries.map σ t)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (MvPowerSeries.map (frMap p σ) f)) (fun i => σ (w i)) := by
  first | exact @GlobalTheory.Katz.quasiLog_map | exact GlobalTheory.Katz.quasiLog_map | (intros; apply GlobalTheory.Katz.quasiLog_map <;> assumption)
