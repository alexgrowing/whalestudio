import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompatOfLocal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.TUniq

namespace GlobalTheory.TUniq

private theorem exists_algClosed_compositum {k K K₀ : Type} [Field k] [Field K] [Field K₀]
    (φ : k →+* K) (ψ : k →+* K₀) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (j : K₀ →+* Ω),
      i.comp φ = j.comp ψ := by
  letI : Algebra k K := φ.toAlgebra
  letI : Algebra k K₀ := ψ.toAlgebra
  haveI : Nontrivial (K ⊗[k] K₀) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k K K₀
      φ.injective ψ.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[k] K₀)
  letI : Field (K ⊗[k] K₀ ⧸ m) := Ideal.Quotient.field m
  let emb : K ⊗[k] K₀ →+* AlgebraicClosure (K ⊗[k] K₀ ⧸ m) :=
    (algebraMap (K ⊗[k] K₀ ⧸ m) (AlgebraicClosure (K ⊗[k] K₀ ⧸ m))).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure (K ⊗[k] K₀ ⧸ m), inferInstance, inferInstance,
    emb.comp Algebra.TensorProduct.includeLeftRingHom,
    emb.comp (Algebra.TensorProduct.includeRight : K₀ →ₐ[k] K ⊗[k] K₀).toRingHom, ?_⟩
  ext a
  simp only [RingHom.comp_apply]
  congr 1
  show (algebraMap k K a) ⊗ₜ[k] (1 : K₀) = (1 : K) ⊗ₜ[k] (algebraMap k K₀ a)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

private theorem pt_eq_lemma_2 {K : Type} [Field K] (q r : PrimeSpectrum K) : q = r :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime q.asIdeal).trans (Ideal.eq_bot_of_prime r.asIdeal).symm)

theorem exists_algClosed_join_of_mem_range {S : Scheme.{0}} {K K₀ : Type} [Field K] [Field K₀]
    (x : Sp K ⟶ S) (x₀ : Sp K₀ ⟶ S) (p : Sp K) (p₀ : Sp K₀) (h : x p = x₀ p₀) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (j : K₀ →+* Ω),
      spMap i ≫ x = spMap j ≫ x₀ := by
  have e : p = IsLocalRing.closedPoint K := pt_eq_lemma_2 _ _
  have e₀ : p₀ = IsLocalRing.closedPoint K₀ := pt_eq_lemma_2 _ _
  subst e e₀
  have hx := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S x
  have hx₀ := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K₀ S x₀
  generalize S.descResidueField (Scheme.stalkClosedPointTo x) = φ at hx
  generalize S.descResidueField (Scheme.stalkClosedPointTo x₀) = φ₀ at hx₀
  obtain ⟨Ω, hΩ, hΩc, i, j, hij⟩ := exists_algClosed_compositum φ.hom ((S.residueFieldCongr h).hom ≫ φ₀).hom
  refine ⟨Ω, hΩ, hΩc, i, j, ?_⟩
  have hx₀' : Spec.map ((S.residueFieldCongr h).hom ≫ φ₀) ≫
      S.fromSpecResidueField (x (IsLocalRing.closedPoint K)) = x₀ := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField, hx₀]
  have hc : φ ≫ CommRingCat.ofHom i = ((S.residueFieldCongr h).hom ≫ φ₀) ≫ CommRingCat.ofHom j := by
    ext a
    exact RingHom.congr_fun hij a
  show Spec.map (CommRingCat.ofHom i) ≫ x = Spec.map (CommRingCat.ofHom j) ≫ x₀
  conv_lhs => rw [← hx]
  conv_rhs => rw [← hx₀']
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hc]

theorem geoGood_commonFibres : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (t t' : TObj g k J b s), GeoGood t t' {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (u : TObj g k J b (x ≫ s)), p ∈ Set.range x ∧ TMap u t x ∧ TMap u t' x} := by
  intro o _ g k J b S s t t' K _ x hx
  obtain ⟨K₁, hK₁, x₁, u₁, ⟨p₁, hp₁⟩, hu, hu'⟩ := hx ⟨IsLocalRing.closedPoint K, rfl⟩
  obtain ⟨Ω, hΩ, hΩc, i, j, hij⟩ :=
    exists_algClosed_join_of_mem_range x x₁ (IsLocalRing.closedPoint K) p₁ hp₁.symm
  obtain ⟨u, hu₀⟩ := GlobalTheory.tObj_pull o g k J b (Sp K₁) (Sp Ω) (x₁ ≫ s) (spMap i ≫ x ≫ s) (spMap j) u₁
    (by rw [← Category.assoc, ← hij, Category.assoc])
  have hT := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b S (Sp K₁) (Sp Ω) s (x₁ ≫ s) (spMap i ≫ x ≫ s) t u₁ u).2
    x₁ (spMap j) hu).1 hu₀
  have hT' := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b S (Sp K₁) (Sp Ω) s (x₁ ≫ s) (spMap i ≫ x ≫ s) t' u₁ u).2
    x₁ (spMap j) hu').1 hu₀
  rw [← hij] at hT hT'
  obtain ⟨ψ, hψ⟩ := (tMap_iff u t _).1 hT
  obtain ⟨ψ', hψ'⟩ := (tMap_iff u t' _).1 hT'
  exact ⟨Ω, hΩ, hΩc, i, spMap i ≫ x ≫ s, u, ψ, ψ', hψ, hψ'⟩

end GlobalTheory.TUniq
