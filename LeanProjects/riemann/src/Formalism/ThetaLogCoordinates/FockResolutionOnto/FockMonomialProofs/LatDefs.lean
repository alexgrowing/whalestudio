import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementG
import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas MvPolynomial Finset

noncomputable def Wtot (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  ⨆ o : ℕ, XSp p (setLast LL o) J M ρ

noncomputable def M2 (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) : Submodule ℤ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  ⨆ o : ℕ, Submodule.map (initL p (Fin.last K, ρ) 0)
    ((Y p (setLast LL o) J M).restrictScalars ℤ_[p] ⊓ IntPol p (Fin (K + 1) × Fin r))

end Formalism.InvariantFactorPaths.L4
