import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GeometricAbelianConnected

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.AI

def polar {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) (c : Fin n → σ → ℝ) : ℝ :=
  ∑ w : Fin n → σ, (∏ r, c r (w r)) * a w

namespace AnSq

variable {d : ℕ} {σ : Type} [Fintype σ] {SY : AnSys (d + 1) σ} {a₀ : σ} {ε : σ → ℤ} (Q : AnSq SY a₀ ε)

def pull0 (_Q : AnSq SY a₀ ε) (c : σ → ℝ) : Option σ → ℝ := fun o => o.elim 0 c

open Classical in

def pull1 (_Q : AnSq SY a₀ ε) (c : σ → ℝ) : Option σ → ℝ :=
  fun o => o.elim (c a₀) fun a => if a = a₀ then 0 else c a

def wcoef (c : σ → ℝ) (k i : ℕ) : Fin (d + 2) → Option σ → ℝ :=
  Fin.cons (α := fun _ => Option σ → ℝ) (Q.pull0 (fun a => (ε a : ℝ)) - Q.pull1 fun a => (ε a : ℝ))
    (word (d + 1) k i (Q.pull0 fun a => (ε a : ℝ)) (Q.pull1 fun a => (ε a : ℝ)) (Q.pull0 c))

def gT (t : ℝ) (x : Q.SW.X) : ℝ :=
  logNormSec Q.L' Q.v x + Q.cst + (1 / 2) * ∑ a, (ε a : ℝ) * (SY.phT a t (Q.q 0 x) + SY.phT a t (Q.q 1 x))

def gH (x : Q.SW.X) : ℝ :=
  logNormSec Q.L' Q.v x + Q.cst + (1 / 2) * ∑ a, (ε a : ℝ) * (SY.ph a (Q.q 0 x) + SY.ph a (Q.q 1 x))

end AnSq

end GlobalTheory.CompanionTheory.Ar.PB
