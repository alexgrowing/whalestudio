import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveOfIsIntegral
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompleteDvrEmbedding

theorem exists_injective_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal) (hv : v.Integers O)
    [Algebra A B] [Algebra.IsIntegral A B] (hφ : Function.Injective (algebraMap A B)) (j : A →+* O)
    (hj : Function.Injective ((algebraMap O C).comp j)) :
    ∃ j' : B →+* O, Function.Injective ((algebraMap O C).comp j') := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_14 h_15; revert A B O C h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 v hv h_14 h_15 hφ j hj; exact @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral)
  | exact @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral
  | exact _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral
  | (apply _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral ..)

theorem exists_embedding_padicComplexInt :
    ∀ T : CDVR, T.FinRes → ∃ (p : ℕ) (_ : Fact p.Prime) (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p]), ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a) := by
  intro T hT
  haveI : Finite (IsLocalRing.ResidueField T.V) := hT
  obtain ⟨p, hp, _, hfin⟩ := GlobalTheory.exists_padicInt_algebra_finite T.V
  have hinj : Function.Injective (algebraMap ℤ_[p] T.V) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0
      (PadicInt.irreducible_p (p := p))
    rw [map_mul, map_pow, map_natCast] at ha
    exact mul_ne_zero (u.isUnit.map _).ne_zero
      (pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) ha
  have hj : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (padicIntHom p)) :=
    (algebraMap ℚ_[p] ℂ_[p]).injective.comp Subtype.val_injective
  obtain ⟨kO, hkO⟩ := exists_injective_of_integral _ (PadicComplexInt.integers p) hinj (padicIntHom p) hj
  exact ⟨p, hp, IsFractionRing.lift (K := T.Fr) hkO, kO, fun a => (IsFractionRing.lift_algebraMap hkO a).symm⟩

end GlobalTheory.CompleteDvrEmbedding
