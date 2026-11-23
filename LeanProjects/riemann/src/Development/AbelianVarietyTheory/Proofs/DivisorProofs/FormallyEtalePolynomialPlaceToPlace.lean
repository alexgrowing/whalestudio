import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtale
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.PolyPlaceEt

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

def inclRing {Q : Subring K} {P : Place c} (h : P.Contains Q) : Q →+* P.ring :=
  Q.subtype.codRestrict P.ring fun q => h q q.2

theorem isUnit_of_ord_zero (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0)
    (h : P.ord (b : K) = 0) : IsUnit b := by
  have h1 : (b : K)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hb)).1 (by rw [P.ord_inv, h]; rfl)
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ hb))

theorem isLocalization_ring {Q : Subring K} {P : Place c} (h : P.IsPrimeOf Q) :
    letI := (inclRing h.1).toAlgebra
    IsLocalization ((IsUnit.submonoid P.ring).comap (inclRing h.1)) P.ring := by
  letI := (inclRing h.1).toAlgebra
  rw [isLocalization_iff]
  refine ⟨fun y => y.2, fun f => ?_, fun {a b} e => ⟨1, ?_⟩⟩
  · obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := h.2 f f.2
    exact ⟨⟨⟨a, ha⟩, ⟨⟨b, hb⟩, isUnit_of_ord_zero P ⟨b, h.1 b hb⟩ hb0 hbo⟩⟩, Subtype.ext e⟩
  · have : (a : K) = b := congrArg (fun z : P.ring => (z : K)) e
    rw [Subtype.ext this]

end PolyPlaceEt

open PolyPlaceEt in

theorem formallyEtale_polyPlace : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K)
    (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL) (P0 : Place cK)
    (j : K →+* L), IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T → P0.IsPrimeOf R →
    (∀ g : R, j (g : K) = (ι g : L)) → ∀ (hA : ∀ f ∈ P0.ring, j f ∈ P.ring)
    (hτ : ∀ i, (τ i : L) ∈ P.ring),
    (MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))).FormallyEtale := by
  intro K L _ _ cK cL r R T ι ψ τ P P0 j hE hP hP0 hj hA hτ
  letI : Algebra R P0.ring := (inclRing hP0.1).toAlgebra
  letI : Algebra T P.ring := (inclRing hP.1).toAlgebra
  haveI h0 := isLocalization_ring hP0
  haveI h1 := isLocalization_ring hP
  letI : Algebra (MvPolynomial (Fin r) R) (MvPolynomial (Fin r) P0.ring) :=
    MvPolynomial.algebraMvPolynomial
  haveI := MvPolynomial.isLocalization (σ := Fin r) ((IsUnit.submonoid P0.ring).comap (inclRing hP0.1)) P0.ring
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) (MvPolynomial (Fin r) P0.ring) :=
    Algebra.FormallyEtale.of_isLocalization
      (((IsUnit.submonoid P0.ring).comap (inclRing hP0.1)).map MvPolynomial.C)
  have hc : ((algebraMap T P.ring).comp (MvPolynomial.eval₂Hom ι τ)).FormallyEtale :=
    RingHom.FormallyEtale.comp hE.etale (RingHom.formallyEtale_algebraMap.2
      (Algebra.FormallyEtale.of_isLocalization ((IsUnit.submonoid P.ring).comap (inclRing hP.1))))
  letI : Algebra (MvPolynomial (Fin r) R) P.ring :=
    ((algebraMap T P.ring).comp (MvPolynomial.eval₂Hom ι τ)).toAlgebra
  letI : Algebra (MvPolynomial (Fin r) P0.ring) P.ring :=
    (MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin r) R) (MvPolynomial (Fin r) P0.ring) P.ring := by
    apply IsScalarTower.of_algebraMap_eq'
    apply MvPolynomial.ringHom_ext
    · intro g
      change inclRing hP.1 (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C g)) =
        MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))
          (MvPolynomial.map (inclRing hP0.1) (MvPolynomial.C g))
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      apply Subtype.ext
      exact (hj g).symm
    · intro i
      change inclRing hP.1 (MvPolynomial.eval₂Hom ι τ (MvPolynomial.X i)) =
        MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))
          (MvPolynomial.map (inclRing hP0.1) (MvPolynomial.X i))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      rfl
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) P.ring := hc
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) P0.ring) P.ring :=
    Algebra.FormallyEtale.of_restrictScalars (R := MvPolynomial (Fin r) R)
  exact RingHom.formallyEtale_algebraMap.2 this

end GlobalTheory.FieldPair
