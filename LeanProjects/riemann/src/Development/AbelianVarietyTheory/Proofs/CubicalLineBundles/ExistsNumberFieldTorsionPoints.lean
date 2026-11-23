import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.TorsionField

theorem exists_field_alg (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (B : Type) [CommRing B] [Algebra k B]
    [Module.Finite k B] : ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧
      ∀ (φ : B →ₐ[k] ℂ) (b : B), φ b ∈ k₁ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := B)
  let S : Set ℂ := ⋃ b ∈ s, (minpoly k b).rootSet ℂ
  have hS : S.Finite := s.finite_toSet.biUnion fun b _ => Polynomial.rootSet_finite _ _
  have hint : ∀ b : B, _root_.IsIntegral k b := fun b => Algebra.IsIntegral.isIntegral b
  have hI : ∀ x ∈ S, _root_.IsIntegral k x := fun x hx => by
    simp only [S, Set.mem_iUnion] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ⟨minpoly k b, minpoly.monic (hint b), (Polynomial.mem_rootSet.1 hb).2⟩
  have : Finite S := hS
  have hfd : FiniteDimensional k (IntermediateField.adjoin k S) := IntermediateField.finiteDimensional_adjoin hI
  have hfd' : FiniteDimensional ℚ (IntermediateField.adjoin k S) := Module.Finite.trans k _
  refine ⟨(IntermediateField.adjoin k S).restrictScalars ℚ, hfd', fun x hx => ?_, fun φ b => ?_⟩
  · exact (IntermediateField.adjoin k S).algebraMap_mem ⟨x, hx⟩
  · change φ b ∈ IntermediateField.adjoin k S
    have hb : b ∈ Submodule.span k (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine IntermediateField.subset_adjoin _ _ ?_
      simp only [S, Set.mem_iUnion]
      refine ⟨b, hb, Polynomial.mem_rootSet.2 ⟨minpoly.ne_zero (hint b), ?_⟩⟩
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact IntermediateField.smul_mem _ ha

theorem exists_field_finite (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (Z : Over (Sp k)) [IsFinite Z.hom] :
    ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧
      ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ y : Over.mk (spMap (algebraMap k ℂ)) ⟶ Z,
        ∃ y₂ : Over.mk (spMap (IntermediateField.inclusion h₂).toRingHom) ⟶ Z,
          spMap (algebraMap k₂ ℂ) ≫ y₂.left = y.left := by
  have : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let φ : CommRingCat.of k ⟶ Γ(Z.left, ⊤) := Spec.preimage (Z.left.isoSpec.inv ≫ Z.hom)
  have hφ : Spec.map φ = Z.left.isoSpec.inv ≫ Z.hom := Spec.map_preimage _
  have h₁ : φ.hom.Finite := by rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  let := φ.hom.toAlgebra
  have : Module.Finite k Γ(Z.left, ⊤) := h₁
  obtain ⟨k₁, hfd, hk, H⟩ := exists_field_alg k Γ(Z.left, ⊤)
  refine ⟨k₁, hfd, hk, fun k₂ h₂ h₁₂ y => ?_⟩
  let y' : Sp ℂ ⟶ Z.left := y.left
  have hy : y' ≫ Z.hom = spMap (algebraMap k ℂ) := Over.w y
  let ψ : Γ(Z.left, ⊤) ⟶ CommRingCat.of ℂ := Spec.preimage (y' ≫ Z.left.isoSpec.hom)
  have hψ : Spec.map ψ = y' ≫ Z.left.isoSpec.hom := Spec.map_preimage _
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap k ℂ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]
  have hc' : ∀ c : k, ψ.hom (φ.hom c) = (c : ℂ) := fun c => congrArg (fun f => f.hom c) hc
  let ψa : Γ(Z.left, ⊤) →ₐ[k] ℂ := { ψ.hom with commutes' := hc' }
  let ψ₂ : Γ(Z.left, ⊤) →+* k₂ := ψ.hom.codRestrict k₂ fun b => h₁₂ (H ψa b)
  refine ⟨Over.homMk (spMap ψ₂ ≫ Z.left.isoSpec.inv) ?_, ?_⟩
  · change (Spec.map (CommRingCat.ofHom ψ₂) ≫ Z.left.isoSpec.inv) ≫ Z.hom =
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h₂).toRingHom)
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext c
    exact hc' c
  · change Spec.map (CommRingCat.ofHom (algebraMap k₂ ℂ)) ≫ Spec.map (CommRingCat.ofHom ψ₂) ≫ Z.left.isoSpec.inv = y'
    rw [← Category.assoc, ← Spec.map_comp, Iso.comp_inv_eq, ← hψ]
    rfl

end GlobalTheory.TorsionField

namespace GlobalTheory

theorem exists_numberField_torsion_points : Out.Laws → ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (P : Out.PolAV (Sp k)) (n : ℕ), 0 < n → ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ x : Over.mk (spMap (algebraMap k ℂ)) ⟶ P.A, x ^ n = 1 → ∃! x₂ : Over.mk (spMap (IntermediateField.inclusion h₂).toRingHom) ⟶ P.A, spMap (algebraMap k₂ ℂ) ≫ x₂.left = x.left := by
  intro _ k _ P n hn
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    have h : IsUnit (n : k) := (Nat.cast_ne_zero.2 hn.ne').isUnit
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨-, hfin, -⟩ := GrpTangent.finiteEtale_mulN_torsion P.A (hG := P.isAb) hu
  obtain ⟨k₁, hfd, hk, H⟩ := TorsionField.exists_field_finite k (torsion P.A n)
  refine ⟨k₁, hfd, hk, fun k₂ h₂ h₁₂ x hx => ?_⟩
  obtain ⟨y, hy, -⟩ := LatticeTorsion.existsUnique_torsion P.A n x hx
  obtain ⟨y₂, hy₂⟩ := H k₂ h₂ h₁₂ y
  have : Flat (spMap (algebraMap k₂ ℂ)) := inferInstance
  have : Surjective (spMap (algebraMap k₂ ℂ)) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have : Epi (spMap (algebraMap k₂ ℂ)) := Flat.epi_of_flat_of_surjective _
  refine existsUnique_of_exists_of_unique ⟨y₂ ≫ torsion.ι P.A n, ?_⟩ fun a b ha hb => ?_
  · rw [← hy, Over.comp_left, Over.comp_left, ← hy₂]
    exact (Category.assoc _ _ _).symm
  · exact Over.OverMorphism.ext ((cancel_epi (spMap (algebraMap k₂ ℂ))).1 (ha.trans hb.symm))

end GlobalTheory
