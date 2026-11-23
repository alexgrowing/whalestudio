import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.CentralizerFixed

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

def pb {q : ℕ} (g : Gp L N) (ω : Form (HS L N) q) : Form (HS L N) q :=
  fun h => (ω (actL g h)).compContinuousLinearMap (actL g)

def sc (t : InfinitePlace L → ℝ) : Gp L N :=
  scal L N fun w => Units.mk0 ((Real.exp (t w) : ℝ) : ℂ) (by exact_mod_cast (Real.exp_pos (t w)).ne')

def av {q : ℕ} (v : InfinitePlace L → ℝ) (ω : Form (HS L N) q) : Form (HS L N) q :=
  fun h => ∫ τ in (0 : ℝ)..1, pb (sc (τ • v)) ω h

def Fix {q : ℕ} (ω : Form (HS L N) q) : Set (InfinitePlace L → ℝ) :=
  {t | ∀ h ∈ Pos L N, pb (sc t) ω h = ω h}

def lg (u : (𝓞 L)ˣ) : InfinitePlace L → ℝ := fun w => Real.log (w ((u : 𝓞 L) : L))

end PositivityTheory.KB.CentralizerFixed

end
