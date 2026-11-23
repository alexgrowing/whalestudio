import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailInt

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

def fS {p m : ℕ} (s : Fin (p + 2) → ℝ) (x : Xp (p + 1) m) : ℝ≥0∞ :=
  ∏ l, ENNReal.ofReal (de x l ^ (-s l))

def rho (t : ℝ) : ℂ := (1 + t * Complex.I) ^ 2 / ((1 + t ^ 2 : ℝ) : ℂ)

def rot {p m : ℕ} (t : ℝ) (x : Xp p m) : Xp p m :=
  (fun j => rho t * x.1 j, fun j => rho t * x.2.1 j, fun i => rho t * x.2.2.1 i, x.2.2.2)

def scl {p m : ℕ} (τ : ℝ) (x : Xp (p + 1) m) : Xp (p + 1) m :=
  (Function.update x.1 0 (τ * x.1 0), Function.update x.2.1 0 (x.2.1 0 / τ), x.2.2.1, x.2.2.2)

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
