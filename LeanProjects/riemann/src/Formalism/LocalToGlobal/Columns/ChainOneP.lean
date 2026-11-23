import Formalism.LocalToGlobal.Columns.ChainOne
import Formalism.LocalToGlobal.Columns.ChainInstS

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem oneYbSym {m2 : ℕ} (hc' : cOf R m2 = 1) (hc : cOf R (m2 + 1) = 0) (hs : cst.sharp = true) : OneYbSym Ch sel mu cst m2 :=
  fun P hP x₀ y' h l => psiAt_sym Ch sel mu cst hc' hc hs P hP x₀ y' h l

theorem oneYbSym_of_m {m2 : ℕ} (hm : R.m = m2 + 2) (hs : cst.sharp = true) : OneYbSym Ch sel mu cst m2 :=
  oneYbSym Ch sel mu cst (by unfold cOf; omega) (by unfold cOf; omega) hs

end Formalism.L2.Col
