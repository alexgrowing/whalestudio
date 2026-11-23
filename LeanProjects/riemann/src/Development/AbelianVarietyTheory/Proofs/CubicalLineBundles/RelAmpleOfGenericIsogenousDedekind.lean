import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecNeZeroOfLbIso

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.AmpleDedekind

theorem range_spMap_fractionRing (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Set.range (spMap (algebraMap R K)) = {genericPoint (Sp R)} := by
  have h : ∀ p : Sp K, spMap (algebraMap R K) p = genericPoint (Sp R) := fun p => by
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap R K) (PrimeSpectrum.asIdeal p) = ⊥
    have hp : PrimeSpectrum.asIdeal p = ⊥ := Ideal.eq_bot_of_prime (K := K) _ (h := p.isPrime)
    rw [hp]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  exact Set.eq_singleton_iff_unique_mem.2
    ⟨⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), h _⟩, by rintro _ ⟨p, rfl⟩; exact h p⟩

theorem relAmple_of_generic_of_isogenous : Out.Laws → Out.Laws2 → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp R)) (B : Over (Sp R)) [GrpObj B] (Ψ : P.A ⟶ B) (M : LB B.left) (B₀ : Over (Sp K)) [GrpObj B₀] (φ : B₀.left ⟶ B.left) (M₀ : LB B₀.left), IsAbelianScheme B → M.IsLB → M₀.IsLB → IsFinite Ψ.left → Flat Ψ.left → Surjective Ψ.left → IsGrpPullback B₀ B (spMap (algebraMap R K)) φ → LBIso M₀ (M.pull φ) → Out.RelAmple B₀ M₀ → Out.RelAmple B M := by
  intro h₁ h₂ R K _ _ _ _ _ P B _ Ψ M B₀ _ φ M₀ hB hM hM₀ hfin hfl hsurj hpb hiso hamp
  have := hB.proper
  have := P.isAb.proper
  have hsq := hpb.1
  have : IsProper B₀.hom := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : IsLocallyNoetherian (Sp R) := inferInstance
  have a₀ : IsAmpleLB (M.pull φ) :=
    (isAmpleLB_congr hM₀ (LB.isLB_pull hM φ) hiso).1 ((relAmple_iff_isAmpleLB_of_isAffine B₀ hM₀).1 hamp)
  let x := spMap (algebraMap R K)
  let g : pullback P.A.hom x ⟶ B₀.left :=
    hsq.lift (pullback.fst P.A.hom x ≫ Ψ.left) (pullback.snd P.A.hom x)
      (by rw [Category.assoc, Over.w Ψ]; exact pullback.condition)
  have e₁ : g ≫ φ = pullback.fst P.A.hom x ≫ Ψ.left := hsq.lift_fst _ _ _
  have e₂ : g ≫ B₀.hom = pullback.snd P.A.hom x := hsq.lift_snd _ _ _
  have sq : IsPullback (pullback.fst P.A.hom x) g Ψ.left φ := by
    refine IsPullback.of_bot ?_ e₁.symm hsq
    rw [e₂, Over.w Ψ]
    exact IsPullback.of_hasPullback _ _
  have : IsFinite g := MorphismProperty.of_isPullback (P := @IsFinite) sq hfin
  have hΨ := LB.isLB_pull hM Ψ.left
  have a₁ : IsAmpleLB ((M.pull Ψ.left).pull (pullback.fst P.A.hom x)) :=
    (isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hM φ) g) (LB.isLB_pull hΨ _)
      (FiniteAmple.lbIso_pull_pull φ hM e₁)).1 (a₀.pull_of_isFinite g)
  have : IsProper ((Over.pullback x).obj P.A).hom :=
    inferInstanceAs (IsProper (pullback.snd P.A.hom x))
  have a₂ : Out.RelAmple P.A (M.pull Ψ.left) :=
    AmpleSpecialisation.relAmple_of_genericFibre h₁ h₂ (Sp R) P (M.pull Ψ.left) K x hΨ (range_spMap_fractionRing R K)
      ((relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback x).obj P.A) (LB.isLB_pull hΨ _)).2 a₁)
  exact (relAmple_finite_pow_iso (Sp R) P.A B Ψ M 1 one_pos P.isAb hB hM hfin).2.2.1 hfl hsurj a₂

end GlobalTheory.AmpleDedekind
