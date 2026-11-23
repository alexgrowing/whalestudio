import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceCentreOnBaseOfEtaleTowerOverNormalLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceOrdEqAlongEtaleTowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderDifferentialFormEtTowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderWedgeEqOfEtaleTowerHeightOnePrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenTopFormEtaleTowerTranscendenceBasisStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem effAt_etTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (φ : R →₀ ℚ) (θ : T →₀ ℚ),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → (∀ g ∈ φ.support, g ≠ 0) →
  (∀ g ∈ θ.support, (g : L) ≠ 0 ∧ 0 ≤ θ g) →
  EffAt cK n R (dForm cK (fun i => (x i : K))) (Finsupp.mapDomain (fun g : R => (g : K)) φ) →
  EffAt cL (r + n) T (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))
    (Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  intro K L _ _ cK cL n r R T ι ψ τ x φ θ hT hx hφ hθ hE
  have hinj : Function.Injective ι := fun a b h => by
    have := congrArg ψ h
    rwa [hT.retr, hT.retr] at this
  have hi : Function.Injective (fun g : R => (ι g : L)) := Subtype.val_injective.comp hinj
  have hι0 : ∀ g : R, g ≠ 0 → (ι g : L) ≠ 0 := fun g hg h =>
    hg (hinj (Subtype.ext (by simpa using h)))
  refine ⟨fun h => ?_, ?_, fun P hP => ?_⟩
  · have hC := GlobalTheory.T.isFreeGen_topForm_etaleTower_transcendenceBasis cK cL n r R T ι ψ τ x hT hx
    exact one_ne_zero (hC.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  · rw [Finsupp.add_apply]
    have h1 : Finsupp.mapDomain (fun g : R => (ι g : L)) φ 0 = 0 := by
      have e := Finsupp.mapDomain_apply hi φ 0
      simp only [map_zero, ZeroMemClass.coe_zero] at e
      rw [e]
      exact Finsupp.notMem_support_iff.1 fun h => hφ 0 h rfl
    have h2 : Finsupp.mapDomain (fun g : T => (g : L)) θ 0 = 0 := by
      have e := Finsupp.mapDomain_apply Subtype.val_injective θ 0
      simp only [ZeroMemClass.coe_zero] at e
      rw [e]
      exact Finsupp.notMem_support_iff.1 fun h => (hθ 0 h).1 rfl
    rw [h1, h2, add_zero]
  · have hq : ∀ {M : Type} [Field M] (c : ℂ →+* M) (E : Place c) {A : Type} (f : A → M)
        (ξ : A →₀ ℚ), E.ordQ (Finsupp.mapDomain f ξ) = ξ.sum fun g t => t * (E.ord (f g) : ℚ) := by
      intro M _ c E A f ξ
      rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
      rfl
    have hθ' : 0 ≤ P.ordQ (Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
      rw [hq]
      refine Finset.sum_nonneg fun g hg => mul_nonneg (hθ g hg).2 ?_
      exact_mod_cast (P.ord_nonneg_iff (hθ g hg).1).2 (hP.1 _ g.2)
    rw [hq] at hθ'
    rw [Place.disc, map_add]
    rcases GlobalTheory.T.dvrPlace_centre_on_base_of_etaleTowerOverNormalLocal cK cL r R T ι ψ τ P hT hP with h0 | ⟨P0, hP0, h0⟩
    · rw [GlobalTheory.T.order_differential_form_et_tower cK cL n r R T ι ψ τ x P hT hx hP h0, hq, hq]
      have : (φ.sum fun g t => t * (P.ord (ι g : L) : ℚ)) = 0 :=
        Finset.sum_eq_zero fun g hg => by dsimp only; rw [h0 g (hφ g hg)]; simp
      rw [this]
      push_cast
      linarith
    · have h1 := GlobalTheory.T.dvrPlace_ord_eq_along_etaleTower cK cL r R T ι ψ τ P P0 hT hP hP0 h0
      have hd := hE.2.2 P0 hP0
      rw [Place.disc, hq] at hd
      rw [GlobalTheory.T.formOrder_wedge_eq_of_etaleTower_heightOnePrime cK cL n r R T ι ψ τ x P P0 hT hx hP hP0 h1, hq, hq]
      have : (φ.sum fun g t => t * (P.ord (ι g : L) : ℚ)) =
          φ.sum fun g t => t * (P0.ord (g : K) : ℚ) :=
        Finset.sum_congr rfl fun g hg => by dsimp only; rw [h1 g (hφ g hg)]
      rw [this]
      linarith

end GlobalTheory.FieldPair
