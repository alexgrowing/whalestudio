import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv GlobalTheory.ExpUniqCh0

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpUniqCh0

theorem jetMap_mk_X' {S : Type} [CommRing S] {α β : Type} {m : ℕ} (φ : α → MvPolynomial β S)
    (hφ : ∀ i, φ i ∈ orig S β) (r : α) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ (MvPolynomial.X r)) = Ideal.Quotient.mk _ (φ r) := by
  simp only [jetMap, liftJet, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  simp

theorem jetMap_mk' {S : Type} [CommRing S] {α β : Type} {m : ℕ} (φ : α → MvPolynomial β S)
    (hφ : ∀ i, φ i ∈ orig S β) (P : MvPolynomial α S) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ P) := by
  simp only [jetMap, liftJet, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

end GlobalTheory.ExpUniqCh0

theorem GlobalTheory.ExpUniqCh0.diag_comp_jet : ∀ {S : Type} [CommRing S] {ρ : Type} (m : ℕ),
    (GlobalTheory.ExpUniqCh0.diag m).comp (jetSum (Finset.univ : Finset (Fin 2))) = (jetScale (fun _ => (2 : S)) : Jet S ρ m →ₐ[S] Jet S ρ m) ∧
    ∀ i : Fin 2, (GlobalTheory.ExpUniqCh0.diag m).comp (jetIn i) = AlgHom.id S (Jet S ρ m) := by
  intro S _ ρ m
  refine ⟨?_, fun i => ?_⟩
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro r
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, jetSum, jetScale, diag, jetMap_mk_X', jetMap_mk',
      map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Fin.sum_univ_two]
    rw [← map_mul, map_add, MvPolynomial.aeval_X, MvPolynomial.aeval_X, ← two_mul]
    congr 1
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro r
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, jetIn, diag, jetMap_mk_X', AlgHom.id_apply]
