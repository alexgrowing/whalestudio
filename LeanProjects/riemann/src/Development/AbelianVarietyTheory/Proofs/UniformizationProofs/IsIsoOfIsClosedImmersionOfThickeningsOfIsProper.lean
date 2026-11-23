import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ThickeningClosed in

theorem isIso_of_isClosedImmersion_of_thickenings_of_isProper {R : Type} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (Y : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] {Z : Scheme.{0}} (j : Z ⟶ Y.left)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : (thickObj R I n Y).left ⟶ Z, l ≫ j = (fstG I n Y).left) : IsIso j := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have h' : ∀ n : ℕ, ∃ l : pullback Y.hom (thick R I n) ⟶ Z, l ≫ j = pullback.fst Y.hom (thick R I n) :=
    fun n => h n
  have hnear : ∀ x : Y.left, x ∈ zeroLocusOpen j.ker := by
    by_contra hne
    simp only [not_forall] at hne
    obtain ⟨x₀, hx₀⟩ := hne
    have hSc : IsClosed (zeroLocusOpen j.ker)ᶜ := (isOpen_zeroLocusOpen j.ker).isClosed_compl
    have hT : IsClosed (Y.hom '' (zeroLocusOpen j.ker)ᶜ) := Y.hom.isClosedMap _ hSc
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal (Y.hom x₀).asIdeal (Y.hom x₀).isPrime.ne_top
    have hcl : (⟨m, hm.isPrime⟩ : PrimeSpectrum (CommRingCat.of R)) ∈ closure {Y.hom x₀} :=
      (PrimeSpectrum.le_iff_mem_closure _ _).mp hpm
    obtain ⟨x, hxS, hx⟩ :=
      closure_minimal (Set.singleton_subset_iff.mpr
        (Set.mem_image_of_mem _ hx₀ : Y.hom x₀ ∈ Y.hom '' (zeroLocusOpen j.ker)ᶜ)) hT hcl
    apply hxS
    refine ThickeningClosed.mem_of_thickenings I Y.hom j h' x ?_
    rw [hx]
    exact hI.trans (sInf_le ⟨bot_le, hm⟩)
  have hker : j.ker = ⊥ := by
    ext U a
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Submodule.mem_bot]
    constructor
    · intro ha
      have hJ : LinearMap.ker (LinearMap.toSpanSingleton Γ(Y.left, U) Γ(Y.left, U) a) = ⊤ := by
        by_contra hJ
        obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal _ hJ
        obtain ⟨s, hs, hsa⟩ :=
          ThickeningClosed.exists_mul_eq_zero_of_mem j.ker U ⟨q, hq.isPrime⟩ (hnear _) ha
        exact hs (hJq (by simp [LinearMap.mem_ker, hsa]))
      have h1 : (1 : Γ(Y.left, U)) ∈ LinearMap.ker (LinearMap.toSpanSingleton Γ(Y.left, U) Γ(Y.left, U) a) :=
        hJ ▸ Submodule.mem_top
      simpa using h1
    · rintro rfl
      exact zero_mem _
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker

theorem hom_eq_of_thickenings_of_isProper : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y Z : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] [IsSeparated Z.hom] (f g : Y ⟶ Z), (∀ e, (fstG I e Y).left ≫ f.left = (fstG I e Y).left ≫ g.left) → f = g := by
  intro R _ _ _ I hI Y Z _ _ f g hfg
  have hf : f.left ≫ Z.hom = Y.hom := Over.w f
  have hg : g.left ≫ Z.hom = Y.hom := Over.w g
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.left ⟶ pullback Z.hom Z.hom,
      φ = pullback.lift f.left g.left (hf.trans hg.symm) := ⟨_, rfl⟩
  have hφ1 : φ ≫ pullback.fst Z.hom Z.hom = f.left := by rw [hφ, pullback.lift_fst]
  have hφ2 : φ ≫ pullback.snd Z.hom Z.hom = g.left := by rw [hφ, pullback.lift_snd]
  have hι : IsIso (pullback.fst φ (pullback.diagonal Z.hom)) := by
    refine isIso_of_isClosedImmersion_of_thickenings_of_isProper I hI Y _ fun n => ?_
    refine ⟨pullback.lift (fstG I n Y).left ((fstG I n Y).left ≫ f.left) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp [hφ1]
    · simp [hφ2, hfg n]
  have key : φ = inv (pullback.fst φ (pullback.diagonal Z.hom)) ≫
      pullback.snd φ (pullback.diagonal Z.hom) ≫ pullback.diagonal Z.hom := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  apply Over.OverMorphism.ext
  rw [← hφ1, ← hφ2, key]
  simp

end GlobalTheory
