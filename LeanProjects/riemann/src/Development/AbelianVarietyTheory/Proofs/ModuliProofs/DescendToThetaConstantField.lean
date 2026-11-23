import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem descend_to_theta_field : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (K₀ K : Type) [Field K₀] [Field K] [IsAlgClosed K] (β : o →+* K₀) (e : K₀ →+* K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (v : Ix g ((n ^ j) ^ 2) → K₀), s = spMap e ≫ spMap β → t.Shape Mat κ → t.Prim w w' → t.HasTh (𝟙 _) (fun a => e (v a)) → ∃ t₀ : TObj g ((n ^ j) ^ 2) J b (spMap β), TMap t t₀ (spMap e) ∧ t₀.Shape Mat κ ∧ t₀.Prim w w' ∧ t₀.HasTh (𝟙 _) v := by
  intro hL hL2 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b K₀ K _ _ _ β e s t v hs hsh hpr hth => ?_⟩
  subst hs

  have hdense : VeryDense (objPrimes b Mat κ β v) := by
    intro q f hq hf
    have hq0 : q = ⊥ := (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
    have hker : RingHom.ker e = q := by
      rw [hq0]; exact (RingHom.injective_iff_ker_eq_bot e).mp e.injective
    exact ⟨q, ⟨K, inferInstance, inferInstance, e, t, hker, hsh, hth⟩, hq, le_rfl, hf⟩
  obtain ⟨t₀, hth₀, hu⟩ := hj₀ j hj o b K₀ β v hdense

  have hmap : TMap t t₀ (spMap e) := hu K e t hsh hth
  obtain ⟨-, -, hdesc⟩ := GlobalTheory.shape_prim_pull_and_descend o g ((n ^ j) ^ 2) J b Mat κ w w' _ _ _ _ _ t₀ t hmap
  obtain ⟨hS, hP⟩ := hdesc K₀ rfl inferInstance inferInstance
  exact ⟨t₀, hmap, hS hsh, hP inferInstance hpr, hth₀⟩

end GlobalTheory.ZM
