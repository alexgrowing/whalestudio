import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermOriginConstantSectionEqOriginStalkConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldEvalOriginEqTangentDerivativStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginAddTangentVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginSmulTangentVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqOfTangentDerivativeAtOriginEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorOfOriginDerivationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginLocalRingNoetherianFreeUnitSectionConormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationFamilyCotangentBasisStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

namespace GlobalTheory.CoordsOrigin

theorem coords_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ δ : Fin n → Derivation ℤ (G.left.presheaf.stalk (origin G)) (G.left.presheaf.stalk (origin G)), (∀ a O (hO : origin G ∈ O) f, δ a ((G.left.presheaf.germ O (origin G) hO).hom f) = (G.left.presheaf.germ O (origin G) hO).hom (dd a O f)) → ∃ z : Fin n → G.left.presheaf.stalk (origin G), (∀ i, evO G (z i) = 0) ∧ (∀ a i, evO G (δ a (z i)) = if a = i then 1 else 0) ∧ maximalIdeal (G.left.presheaf.stalk (origin G)) = (maximalIdeal R).map (constO G) ⊔ Ideal.span (Set.range z) := by
  intro R _ _ _ _ G _ _ hsm n v dd hinv δ hδ
  letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra
  obtain ⟨hN, hF, hFin⟩ := GlobalTheory.T.originLocalRing_noetherian_free_unitSectionConormal R G hsm
  have key : ∀ a f, evO G (δ a f) = tanDer G (v a) f := by
    intro a f
    obtain ⟨O, hx, g, rfl⟩ := G.left.presheaf.exists_germ_eq f
    rw [hδ a O hx g]
    exact GlobalTheory.T.invariantVectorField_eval_origin_eq_tangentDerivative R G (v a) (dd a) (hinv a) O hx g
  have hadd : ∀ a x y, tanDer G (v a) (x + y) = tanDer G (v a) x + tanDer G (v a) y := by
    intro a x y
    rw [← key, ← key, ← key, map_add, map_add]
  have hmul : ∀ a x y, tanDer G (v a) (x * y) = evO G x * tanDer G (v a) y + evO G y * tanDer G (v a) x := by
    intro a x y
    rw [← key, ← key, ← key, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
  have hc : ∀ a r, tanDer G (v a) (algebraMap R _ r) = 0 := by
    intro a r
    rw [← key]
    show evO G (δ a (constO G r)) = 0
    rw [← GlobalTheory.GermConst.germ_constFn_origin R G ⊤ trivial r, hδ a ⊤ trivial,
      GlobalTheory.Heat.isInv_constFn R G (v a) (dd a) (hinv a) ⊤ r, map_zero, map_zero]
  let φ : TanM (𝟙 (Sp R)) G →+ (G.left.presheaf.stalk (origin G) → R) :=
    { toFun := fun w => tanDer G w
      map_zero' := funext fun f => by
        have h := GlobalTheory.T.tangentDerivativeAtOrigin_smul_tangentVector R G 0 0 f
        rwa [zero_smul, zero_mul] at h
      map_add' := fun u w => funext fun f => GlobalTheory.T.tangentDerivativeAtOrigin_add_tangentVector R G u w f }
  have hlin : ∀ (c : Fin n → R) f, tanDer G (∑ a, c a • v a) f = ∑ a, c a * tanDer G (v a) f := by
    intro c f
    have h1 : tanDer G (∑ a, c a • v a) f = φ (∑ a, c a • v a) f := rfl
    rw [h1, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => GlobalTheory.T.tangentDerivativeAtOrigin_smul_tangentVector R G (c a) (v a) f
  have hbasis : ∀ D : G.left.presheaf.stalk (origin G) → R, (∀ x y, D (x + y) = D x + D y) →
      (∀ x y, D (x * y) = evO G x * D y + evO G y * D x) → (∀ r, D (algebraMap R _ r) = 0) →
      ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * tanDer G (v a) x := by
    intro D h1 h2 h3
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_tangentVector_of_originDerivation R G D h1 h2 h3
    refine ⟨fun a => v.repr w a, ?_, ?_⟩
    · intro x
      rw [← hw x, ← hlin]
      congr 1
      exact (v.sum_repr w).symm
    · intro c hc'
      have hw' : ∑ a, c a • v a = w := GlobalTheory.T.tangentVector_eq_of_tangentDerivativeAtOrigin_eq R G _ _ fun f => by rw [hlin, hw, hc' f]
      funext a
      rw [← hw', v.repr_sum_self]
  obtain ⟨z, hz0, hz1, hz2⟩ := GlobalTheory.T.derivation_family_cotangent_basis R _ (evO G) (GlobalTheory.FormalOrigin.evO_constO R G) hF hFin n
    (fun a => tanDer G (v a)) hadd hmul hc hbasis
  exact ⟨z, hz0, fun a i => by rw [key]; exact hz1 a i, hz2⟩

end GlobalTheory.CoordsOrigin
