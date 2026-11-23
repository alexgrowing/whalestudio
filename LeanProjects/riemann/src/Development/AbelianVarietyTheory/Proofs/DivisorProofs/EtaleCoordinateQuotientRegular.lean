import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularMapCAppendMapLinForm

open MvPolynomial TensorProduct

namespace GlobalTheory

theorem isRegularRing_quotient_etaleCoordinate : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale →
    ∀ j : Fin n, IsRegularRing (A ⧸ Ideal.span {t j}) := by
  intro p _ A _ _ n t het j
  let B := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra B A := (MvPolynomial.aeval (R := ZMod p) t).toRingHom.toAlgebra
  have : Algebra.Etale B A := het
  let I : Ideal B := Ideal.span (X '' ({j} : Set (Fin n)))
  have hQ : IsRegularRing (B ⧸ I) :=
    IsRegularRing.of_ringEquiv (quotientSpanXEquiv (ZMod p) ({j} : Set (Fin n))).symm.toRingEquiv
  have : IsRegularRing (TensorProduct B (B ⧸ I) A) := isRegularRing_of_etale (B ⧸ I) _
  have hI : I.map (algebraMap B A) = Ideal.span {t j} := by
    simp only [I, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    congr 2
    show MvPolynomial.aeval t (X j) = t j
    simp
  have e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).toRingEquiv.trans
    (Algebra.TensorProduct.comm B A (B ⧸ I)).toRingEquiv
  rw [hI] at e
  exact IsRegularRing.of_ringEquiv e.symm

end GlobalTheory
