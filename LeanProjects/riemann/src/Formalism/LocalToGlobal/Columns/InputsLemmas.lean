import Formalism.LocalToGlobal.Columns.Inputs
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.ColFormsLemmas
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.LocalToGlobal.Columns.CoefModAt
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.HermitianLatticesTheory MvPolynomial

theorem minkowskiBound_holds : MinkowskiBound := card_dvd_minkowskiNumber

section Stab

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

end Stab

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

section Loc

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Loc

section C2

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

end C2

section AtT

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end AtT

end Formalism.L2.Col
