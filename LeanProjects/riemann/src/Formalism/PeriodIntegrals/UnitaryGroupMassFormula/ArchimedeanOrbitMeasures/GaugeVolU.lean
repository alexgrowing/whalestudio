import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstY

noncomputable section

namespace PI.AprimeInfW

def GaugeVolU : Prop := ∀ k : ℕ, Formalism.MainNotions.S.Gauge.GaugeDens (fun _ : Fin k => true) →
    Formalism.MainNotions.S.Gauge.muGauge (fun _ : Fin k => true) Set.univ = ENNReal.ofReal (Formalism.MainNotions.S.UnitaryVolumeMass.volU k)

theorem jm_true (k : ℕ) : Formalism.REAL.Jm (fun _ : Fin k => true) = 1 := by
  simp [Formalism.REAL.Jm]

end PI.AprimeInfW
