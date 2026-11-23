import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreMapsToZeroIdeal
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.GenericFibreInj

theorem asIdeal_genericPoint {F : Type} [Field F] [NumberField F] {X : Scheme.{0}} [IsIntegral X]
    {q : X ⟶ Sp (𝓞 F)} {d : ℕ} (hq : IsArithVar q d) : (q (genericPoint X)).asIdeal = ⊥ := by
  refine IsArithVar.asIdeal_eq_bot_of_under_eq_bot F X q d hq _ (eq_bot_iff.2 fun c hc => ?_)
  rw [GlobalTheory.SteinFibre.mem_under_iff, ← Scheme.mem_basicOpen X (U := ⊤) _ _ trivial] at hc
  by_contra h0
  apply hc
  have hne : (X.basicOpen c : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    exact h0 ((basicOpen_eq_bot_iff c).1 (TopologicalSpace.Opens.ext he))
  exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen c).isOpen).2 (by simpa using hne)

theorem isDominant {F : Type} [Field F] [NumberField F] {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {s : W ⟶ Sp F}
    {jB : W ⟶ X} {d : ℕ} (hq : IsArithVar q d) (pb : IsPullback jB s q (spMap (algebraMap (𝓞 F) F))) :
    IsDominant jB := by
  have := hq.isIntegral
  have e : q (genericPoint X) = spMap (algebraMap (𝓞 F) F) (⊥ : PrimeSpectrum F) := by
    apply PrimeSpectrum.ext
    rw [asIdeal_genericPoint hq]
    change ⊥ = Ideal.comap (algebraMap (𝓞 F) F) ⊥
    exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)).symm
  obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback pb _ _ e
  refine ⟨Dense.mono (Set.singleton_subset_iff.2 ⟨w, hw⟩) ?_⟩
  exact dense_iff_closure_eq.2 (genericPoint_spec X)

theorem app_injective : ∀ {F : Type} [Field F] [NumberField F] {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)}
    {s : W ⟶ Sp F} {jB : W ⟶ X} {d : ℕ},
    IsArithVar q d → IsPullback jB s q (spMap (algebraMap (𝓞 F) F)) → ∀ (V : X.Opens), IsAffineOpen V →
    Function.Injective (jB.app V) := by
  intro F _ _ X W q s jB d hq pb V _
  have := hq.isIntegral
  have := isDominant hq pb
  have : QuasiCompact jB := MorphismProperty.of_isPullback pb.flip inferInstance
  have := IsSchemeTheoreticallyDominant.of_isDominant jB
  exact jB.app_injective V

end GlobalTheory.GenericFibreInj
