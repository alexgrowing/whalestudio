import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialIdealEqBotOfPderivStableNoConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicIndependentEtaleTowerCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOverMvPolynomialRangeEtaleTowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicMvPolynomialEvalAdjoinEtaleTowerCoordStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfSubringIsAlgebraicStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem IsEtTower.eval₂Hom_pderiv_eq_zero {K L : Type} [Field K] [Field L] {cK : ℂ →+* K} {cL : ℂ →+* L} {r : ℕ}
    {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T}
    (h : IsEtTower cK R cL T ι ψ τ) (P : MvPolynomial (Fin r) R) (i : Fin r)
    (hP : MvPolynomial.eval₂Hom ι τ P = 0) :
    MvPolynomial.eval₂Hom ι τ (MvPolynomial.pderiv i P) = 0 := by
  letI : Algebra R T := ι.toAlgebra
  letI : Algebra (MvPolynomial (Fin r) R) T := (MvPolynomial.eval₂Hom ι τ).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin r) R) T := IsScalarTower.of_algebraMap_eq' (by
    ext a; simp [RingHom.algebraMap_toAlgebra])
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) T := h.etale
  let d : Derivation R (MvPolynomial (Fin r) R) T :=
    (Algebra.linearMap (MvPolynomial (Fin r) R) T).compDer (MvPolynomial.pderiv i)
  let f : Ω[MvPolynomial (Fin r) R⁄R] →ₗ[MvPolynomial (Fin r) R] T := d.liftKaehlerDifferential
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale R (MvPolynomial (Fin r) R) T
  let g : Ω[T⁄R] →ₗ[T] T := hb.lift f
  have key : g (KaehlerDifferential.D R T (algebraMap (MvPolynomial (Fin r) R) T P)) =
      algebraMap (MvPolynomial (Fin r) R) T (MvPolynomial.pderiv i P) := by
    rw [← KaehlerDifferential.map_D R R (MvPolynomial (Fin r) R) T]
    erw [hb.lift_eq]
    simp [f, d]
  have h0 : algebraMap (MvPolynomial (Fin r) R) T P = 0 := hP
  rw [h0, map_zero, map_zero] at key
  exact key.symm

theorem charZero_subring_of_complex {K : Type} [Field K] (cK : ℂ →+* K) (R : Subring K) :
    CharZero R := by
  haveI : CharZero K := charZero_of_injective_ringHom cK.injective
  exact ⟨fun a b h => by
    have := congrArg (fun t : R => (t : K)) h
    simpa using this⟩

theorem IsEtTower.eval₂Hom_injective {K L : Type} [Field K] [Field L] {cK : ℂ →+* K}
    {cL : ℂ →+* L} {r : ℕ} {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R}
    {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ) :
    Function.Injective (MvPolynomial.eval₂Hom ι τ) := by
  haveI := charZero_subring_of_complex cK R
  have hI := GlobalTheory.T.mvPolynomial_ideal_eq_bot_of_pderiv_stable_no_constants r (RingHom.ker (MvPolynomial.eval₂Hom ι τ))
    (fun P hP i => h.eval₂Hom_pderiv_eq_zero P i hP)
    (fun a ha => by
      rw [RingHom.mem_ker, MvPolynomial.eval₂Hom_C] at ha
      simpa [h.retr] using congrArg ψ ha)
  exact (RingHom.injective_iff_ker_eq_bot _).2 hI

theorem isFreeGen_dForm_tower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L)
    (n r : ℕ) (R : Subring K) (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T)
    (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  IsFreeGen L (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  intro K L _ _ cK cL n r R T ι ψ τ x h hx
  have hinj := h.eval₂Hom_injective
  letI := cL.toAlgebra
  have hind := GlobalTheory.T.algebraicIndependent_etaleTower_coordinates cK cL n r R T ι ψ τ x h hx hinj
  have halg : Algebra.IsAlgebraic
      (Algebra.adjoin ℂ (Set.range (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))) L := by
    refine ⟨fun z => GlobalTheory.T.isAlgebraic_of_isAlgebraic_over_algebraic_subring _ _ z ?_ (GlobalTheory.T.isAlgebraic_over_mvPolynomial_range_etaleTower cK cL r R T ι ψ τ h hinj z)⟩
    rintro b ⟨a, rfl⟩
    exact GlobalTheory.T.isAlgebraic_mvPolynomialEval_adjoin_etaleTowerCoords cK cL n r R T ι ψ τ x h hx a
  have htr : TrBasis cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))) :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2 ⟨hind, halg⟩
  exact isFreeGen_dForm_of_trBasis cL htr

end GlobalTheory.FieldPair
