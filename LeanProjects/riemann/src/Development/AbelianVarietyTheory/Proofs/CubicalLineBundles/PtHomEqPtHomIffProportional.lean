import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero

namespace GlobalTheory.AddLaw

open GlobalTheory.WeierstrassCurve

theorem ptHom_eq_ptHom_iff_proportional (R : Type) [CommRing R] (W : WeierstrassCurve R)
    (A : Type) [CommRing A] (ρ : R →+* A) (P Q : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q) :
    ptHom W ρ P hP = ptHom W ρ Q hQ ↔ Proportional P Q :=
  ptHom_eq_ptHom_iff_minors W hP hQ

end GlobalTheory.AddLaw
