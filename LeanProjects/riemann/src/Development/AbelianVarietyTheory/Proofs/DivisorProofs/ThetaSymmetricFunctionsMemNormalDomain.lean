import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFunctionsFiniteFlatCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListFieldExtensionEqUpToPermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendElementOfFieldEqualizerFaithfullyFlatStatement
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UMin.SymRing

theorem exists_common_field : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁], Module.FaithfullyFlat R R₁ → ∀ (K : Type) [Field K] (i : R →+* K), ∃ (K' : Type) (_ : Field K') (φ : K →+* K') (i₁ : R₁ →+* K'), i₁.comp (algebraMap R R₁) = φ.comp i := by
  intro R R₁ _ _ _ hff K _ i
  letI : Algebra R K := i.toAlgebra
  haveI : Nontrivial (K ⊗[R] R₁) := Module.FaithfullyFlat.rTensor_nontrivial R R₁ K
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K ⊗[R] R₁)
  letI : Field ((K ⊗[R] R₁) ⧸ M) := Ideal.Quotient.field M
  refine ⟨(K ⊗[R] R₁) ⧸ M, inferInstance,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := K) (B := R₁)).toRingHom,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := R₁)).toRingHom, ?_⟩
  ext r
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgHom.commutes, show i r = algebraMap R K r from rfl, AlgHom.commutes]

theorem symTup_map' {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun a => i (c a)) j := by
  simp only [symTup, Finset.esymm_map_val, map_pow, map_sum, map_prod]

theorem symTup_perm' {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    symTup (fun b => c (σ b)) = symTup c := by
  funext j
  show _ = (Finset.univ.val.map c).esymm _ ^ _
  rw [symTup, ← Function.comp_def c σ, ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem sym_ring : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → R, SymAt G L ρ m x θ e := by
  intro S G _ _ L ρ hL hρ g m N R _ _ _ _ _ x θ hm hmu hN hP
  obtain ⟨R₁, _, _, c, hfin, hff, hc⟩ := GlobalTheory.T.theta_constants_functions_finite_flat_cover S G L ρ hL hρ g m N R x θ hm hmu hN hP
  have hP' : ∀ j, ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) →
      i₁ (symTup c j) = i₂ (symTup c j) := by
    intro j K _ i₁ i₂ h
    obtain ⟨pt₁, h₁⟩ := hc K (i₁.comp (algebraMap R R₁)) i₁ rfl
    obtain ⟨pt₂, h₂⟩ := hc K (i₁.comp (algebraMap R R₁)) i₂ h.symm
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.thetaConstantList_fieldExtension_eq_up_to_perm S G L ρ hL hρ g m R x θ hm hmu hP K K _ _ (RingHom.id K) (RingHom.id_comp _) N pt₁ _ pt₂ _ h₁ h₂
    rw [symTup_map', symTup_map', funext hσ]
    exact (symTup_perm' (fun b => i₁ (c b)) σ).symm ▸ rfl
  choose e he using fun j => GlobalTheory.T.descend_element_of_field_equalizer_faithfully_flat R R₁ hfin hff (symTup c j) (hP' j)
  refine ⟨e, fun K _ i pt c' hl j => ?_⟩
  obtain ⟨K', _, φ, i₁, hφ⟩ := exists_common_field R R₁ hff K i
  obtain ⟨pt₁, h₁⟩ := hc K' (φ.comp i) i₁ hφ
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.thetaConstantList_fieldExtension_eq_up_to_perm S G L ρ hL hρ g m R x θ hm hmu hP K K' i (φ.comp i) φ rfl N pt c' pt₁ _ hl h₁
  apply φ.injective
  have h1 : φ (i (e j)) = i₁ (algebraMap R R₁ (e j)) := by rw [← RingHom.comp_apply, ← RingHom.comp_apply, hφ]
  rw [h1, ← he j K' i₁, symTup_map', symTup_map', funext hσ]
  exact congrFun (symTup_perm' (fun a => φ (c' a)) σ) j

end GlobalTheory.UMin.SymRing

end
