import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.LidxAntisymm

noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs

theorem localization_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (p : Ideal R) [p.IsPrime]
    (X : ∀ i, Submodule R (M i)) :
    localization₂ p (Submodule.pi Set.univ X) = Submodule.pi Set.univ (fun i => localization₂ p (X i)) := by
  classical
  ext x
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, mem_locP]
  constructor
  · rintro ⟨s, hs, hsx⟩ i
    exact ⟨s, hs, by simpa using hsx i⟩
  · intro h
    choose s hs hsx using h
    refine ⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, fun i => ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Pi.smul_apply, mul_smul]
    exact (X i).smul_mem _ (hsx i)

theorem rlen_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (X Z : ∀ i, Submodule R (M i)) :
    relative₂ (Submodule.pi Set.univ X) (Submodule.pi Set.univ Z) = ∑ i, relative₂ (X i) (Z i) := by
  classical
  let φ : (Submodule.pi Set.univ Z) →ₗ[R] (Π i, Z i ⧸ (X i).comap (Z i).subtype) :=
    LinearMap.pi fun i => ((X i).comap (Z i).subtype).mkQ ∘ₗ
      (LinearMap.codRestrict (Z i) (LinearMap.proj i ∘ₗ (Submodule.pi Set.univ Z).subtype)
        (fun z => z.2 i (Set.mem_univ i)))
  have hsurj : Function.Surjective φ := by
    intro q
    choose z hz using fun i => Submodule.Quotient.mk_surjective _ (q i)
    refine ⟨⟨fun i => (z i).1, fun i _ => (z i).2⟩, ?_⟩
    funext i
    rw [← hz i]
    rfl
  have hker : LinearMap.ker φ = (Submodule.pi Set.univ X).comap (Submodule.pi Set.univ Z).subtype := by
    ext z
    simp [φ, funext_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_pi]
    rfl
  unfold relative₂
  rw [((Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)).length_eq,
    Module.length_pi_of_fintype]

end PI.IsoDetW.Loc
