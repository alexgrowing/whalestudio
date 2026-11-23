import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.TwentyWordsLeB
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

open Classical

variable {D : D7}

section Exp

variable (L : SizeData₂ D)

def hN : ℕ := ⌊Formalism.MainNotions.TwistedPlaces.hB L⌋₊

def eA (CA : ℝ) (l : ℕ) : ℕ :=
  ⌈CA * (1 + ((hN L + hN L : ℕ) : ℝ) / (l : ℝ) + (1 + Real.logb l (((hN L + hN L : ℕ) : ℝ) + 1)))⌉₊

end Exp

section RowA

def lenA (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (e' : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  if lam ∈ dc.col then (2 * (locDeg D.host.E lam : ℚ) * D.R.m + 1) * e' else 0

variable (L : SizeData₂ D) (tb : Formalism.MainNotions.TwistedPlaces.Tab L)
  (len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ)

end RowA

section Star

variable (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)

def localErrorBoundPlaces (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) : ℚ :=
  (∑ u ∈ dc.col, ((locDeg D.host.E u : ℚ) * (D.R.m : ℚ) * D.nd.vdel i + 2 * D.nd.vdel i + Br.h0W i u ρ π +
      (D.R.r : ℚ) * (c0 u : ℚ))) +
    (D.R.t : ℚ) * (∑ w ∈ dc.row, ((locDeg D.host.E w : ℚ) + 2) * (cB : ℚ)) +
    4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i +
    (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col

end Star

end Formalism.MainNotions.N

end
