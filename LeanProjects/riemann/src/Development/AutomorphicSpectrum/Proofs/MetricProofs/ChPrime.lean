import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open ReciprocityTheory.AnForm.R

def chPrime {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (g : MvPolynomial (Fin m) ℂ) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  (Ideal.span {algebraMap _ (locRing I t) g}).comap (algebraMap _ (locRing I t))

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
