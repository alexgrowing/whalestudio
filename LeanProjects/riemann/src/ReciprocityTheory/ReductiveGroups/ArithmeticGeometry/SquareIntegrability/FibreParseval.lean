import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZeroModePointwiseBound

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem fibre_parseval (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) :
    HasSum (fun n => ‖zmC hI s n v‖ ^ 2)
      (∫ t in zmBox (Module.finrank ℝ (IR I)), ‖zmG I s (v + tb hI t)‖ ^ 2) :=
  tof_torus_parseval (fun t => zmG I s (v + tb hI t)) (fib_continuous hI hs v)
    (fun t n => fib_periodic hI hs v t n)

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
