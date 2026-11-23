import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelStructureDescendsFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountableStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELFrom

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) : Countable o := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have hc : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (MvPolynomial.cardinalMk_le_max).trans ?_
    simp
  exact hf.countable

theorem fromC_of_isPEL : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (τ : SAB H S), IsPEL D a bas ρ t τ → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (PELClass (b := b) D a bas ρ em) t x := by
  intro hL _ E _ _ _ H D g J _ a w w' bas _ _ _ _ hcl N' o _ b em ρ _ hb S s t τ hτ K _ _ x
  obtain ⟨β', hβ'⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨β, hβ⟩ : ∃ β : o →+* K, x ≫ s = spMap β := ⟨β'.hom, hβ'.symm⟩
  obtain ⟨tx, htx⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b S (Sp K) s (spMap β) x t hβ
  obtain ⟨τx, hτx⟩ := GlobalTheory.PELPull.isPEL_pull E H D g (N' ^ 2) J a bas o b ρ S (Sp K) s (spMap β) x t tx τ hβ htx hτ
  obtain ⟨K₀, β₀, t₀, hβ₀, hcount, -, ht₀⟩ := GlobalTheory.T.thetaLevel_object_descends_fg_subfield o g (N' ^ 2) J b K β tx
  haveI : Countable K₀ := hcount (countable_of_finiteType o hb.2.1)
  have hcomp : spMap β = spMap K₀.subtype ≫ spMap β₀ := by
    rw [← hβ₀, ← Spec.map_comp]; rfl
  obtain ⟨τ₀, hτ₀⟩ := GlobalTheory.T.pelStructure_descends_field_extension hL E H D g (N' ^ 2) J a bas o b ρ K₀ K K₀.subtype β₀ (spMap β) t₀ tx τx
    hcl hcomp ht₀ hτx
  obtain ⟨-, j, hj⟩ := GlobalTheory.T.exists_ringHom_complex_comp_eq_of_countable_field o em K₀ β₀ hb.1 hb.2.1 hb.2.2
  have hjc : spMap j ≫ spMap β₀ = spMap em := by
    rw [← hj, ← Spec.map_comp]; rfl
  obtain ⟨tc, htc⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b (Sp K₀) (Sp ℂ) (spMap β₀) (spMap em) (spMap j) t₀ hjc
  have hc := GlobalTheory.PELPull.isPEL_pull E H D g (N' ^ 2) J a bas o b ρ (Sp K₀) (Sp ℂ) (spMap β₀) (spMap em) (spMap j)
    t₀ tc τ₀ hjc htc hτ₀
  unfold FromC
  rw [hβ]
  exact ⟨K₀, inferInstance, β₀, K₀.subtype, j, t₀, tx, tc, hj, hcomp, htx, ht₀, htc, hc⟩

end GlobalTheory.PELFrom
