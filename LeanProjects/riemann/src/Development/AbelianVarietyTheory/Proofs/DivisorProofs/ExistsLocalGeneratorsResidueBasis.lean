import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FibreBasisSpread

theorem exists_away_linearCombination_bijective : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (J : Type) [Fintype J] (v : J → M) (p : Ideal R) [p.IsPrime],
    Function.Bijective (Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i)) →
    ∃ g : R, g ∉ p ∧ (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R v c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R v c = 0 → ∃ n : ℕ, g ^ n • c = 0) := by
  intro R _ M _ _ _ _ J _ v p _ hbij
  classical
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let Rp := Localization.AtPrime p
  have hloc : Function.Bijective (IsLocalizedModule.map p.primeCompl
      (Finsupp.mapRange.linearMap (Algebra.linearMap R Rp)) (TensorProduct.mk R Rp M 1)
      (Finsupp.linearCombination R v)) := by
    rw [IsLocalizedModule.map_linearCombination, LinearMap.coe_restrictScalars]
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    rw [← (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).comp_bijective]
    have heq : (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).toLinearMap ∘ₗ
        Finsupp.linearCombination p.ResidueField
          (TensorProduct.mk Rp p.ResidueField (Rp ⊗[R] M) 1 ∘ (TensorProduct.mk R Rp M 1 ∘ v)) =
        Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i) := by
      ext i
      simp
    convert hbij using 1
    rw [← heq, LinearMap.coe_comp]
    rfl
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective
    (Finsupp.linearCombination R v) p _ _ hloc
  refine ⟨g, hg, fun x => ?_, fun c hc => ?_⟩
  · obtain ⟨y, hy⟩ := h.2 (LocalizedModule.mk x 1)
    induction y using LocalizedModule.induction_on with
    | h c s =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hy
      obtain ⟨⟨u, hu⟩, hu'⟩ := hy
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, hb⟩ := s.2
      refine ⟨a + b, g ^ a • c, ?_⟩
      have hb' : (s : R) = g ^ b := hb.symm
      simp only [Submonoid.smul_def, one_smul] at hu'
      rw [map_smul, hu', hb', smul_smul, pow_add]
  · have h0 : LocalizedModule.map (Submonoid.powers g) (Finsupp.linearCombination R v)
        (LocalizedModule.mk c 1) = LocalizedModule.map (Submonoid.powers g)
        (Finsupp.linearCombination R v) 0 := by
      rw [LocalizedModule.map_mk, hc, map_zero, LocalizedModule.zero_mk]
    have h1 := h.1 h0
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
    obtain ⟨⟨u, hu⟩, hu'⟩ := h1
    obtain ⟨a, rfl⟩ := hu
    exact ⟨a, by simpa [Submonoid.smul_def] using hu'⟩

end GlobalTheory.FibreBasisSpread
