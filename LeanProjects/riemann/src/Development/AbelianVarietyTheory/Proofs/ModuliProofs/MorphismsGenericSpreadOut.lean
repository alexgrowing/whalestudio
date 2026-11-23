import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.GenericSpread

theorem exists_away_of_fg {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (S : Subalgebra R K) (hS : S.FG) :
    ∃ (f : R) (_ : f ≠ 0) (g : S →ₐ[R] Localization.Away f) (l : Localization.Away f →ₐ[R] K),
      ∀ x, l (g x) = x := by
  classical
  obtain ⟨t, rfl⟩ := hS
  choose p hp using fun x : K => IsLocalization.surj (nonZeroDivisors R) x
  set f : R := ∏ x ∈ t, ((p x).2 : R) with hf_def
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => nonZeroDivisors.ne_zero (p x).2.2
  have hfK : IsUnit (algebraMap R K f) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hf0).isUnit
  have hpow : ∀ y : Submonoid.powers f, IsUnit (algebraMap R K y) := by
    rintro ⟨_, n, rfl⟩
    simpa using hfK.pow n
  let l : Localization.Away f →ₐ[R] K :=
    ⟨IsLocalization.lift (M := Submonoid.powers f) (S := Localization.Away f) hpow,
      fun r => IsLocalization.lift_eq hpow r⟩
  have hl : Function.Injective l := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
    have h1 := congrArg l (IsLocalization.mk'_spec (Localization.Away f) a s)
    rw [map_mul, hz, zero_mul, AlgHom.commutes] at h1
    have ha : a = 0 := (IsFractionRing.injective R K) (by rw [← h1, map_zero])
    subst ha
    exact IsLocalization.mk'_zero s
  have hle : Algebra.adjoin R (↑t : Set K) ≤ l.range := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, AlgHom.mem_range]
    have hdvd : ((p x).2 : R) ∣ f := Finset.dvd_prod_of_mem _ (Finset.mem_coe.mp hx)
    have hu : IsUnit (algebraMap R (Localization.Away f) ((p x).2 : R)) :=
      isUnit_of_dvd_unit (map_dvd _ hdvd) (IsLocalization.Away.algebraMap_isUnit f)
    refine ⟨algebraMap R _ (p x).1 * ↑hu.unit⁻¹, ?_⟩
    have hne : algebraMap R K ((p x).2 : R) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero (p x).2.2)
    apply mul_right_cancel₀ hne
    calc l (algebraMap R _ (p x).1 * ↑hu.unit⁻¹) * algebraMap R K ((p x).2 : R)
        = l (algebraMap R _ (p x).1 * ↑hu.unit⁻¹ * algebraMap R _ ((p x).2 : R)) := by
          rw [map_mul l _ (algebraMap R _ _), AlgHom.commutes]
      _ = l (algebraMap R _ (p x).1) := by rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
      _ = algebraMap R K (p x).1 := AlgHom.commutes l _
      _ = x * algebraMap R K ((p x).2 : R) := (hp x).symm
  refine ⟨f, hf0, (AlgEquiv.ofInjective l hl).symm.toAlgHom.comp (Subalgebra.inclusion hle), l,
    fun x => ?_⟩
  show l ((AlgEquiv.ofInjective l hl).symm (Subalgebra.inclusion hle x)) = x
  rw [← AlgEquiv.ofInjective_apply l hl, AlgEquiv.apply_symm_apply]
  rfl

end GlobalTheory.GenericSpread

namespace GlobalTheory

theorem morphisms_generic_spread_out :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B Z : Scheme.{0}) (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R) (I : Type) [Finite I] (u : I → (pullback pB (spMap (algebraMap R K)) ⟶ Z)), QuasiCompact pB → QuasiSeparated pB → LocallyOfFinitePresentation pZ → (∀ i, u i ≫ pZ = pullback.fst _ _ ≫ pB) → ∃ (f : R) (_ : f ≠ 0) (u' : I → (pullback pB (spMap (algebraMap R (Localization.Away f))) ⟶ Z)), ∀ i, u' i ≫ pZ = pullback.fst _ _ ≫ pB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → j ≫ u' i = u i := by
  intro R K _ _ _ _ _ _ B Z pB pZ I _ u hqc hqs hlfp hu
  have := hqc
  have := hqs
  have := hlfp
  obtain ⟨S, ψ, hSfg, -, hψ⟩ :=
    GlobalTheory.Spread.exists_fg_forall_comp_eq pB pZ u hu ⊥ Subalgebra.fg_bot
  obtain ⟨f, hf0, g, l, hgl⟩ := GlobalTheory.GenericSpread.exists_away_of_fg S hSfg
  have hmono : Mono (spMap (algebraMap R (Localization.Away f))) := inferInstance
  refine ⟨f, hf0, fun i => GlobalTheory.Spread.bcMap pB g ≫ ψ i, fun i => ⟨?_, fun j hj => ?_⟩⟩
  · rw [Category.assoc, (hψ i).1, ← Category.assoc, GlobalTheory.Spread.bcMap_fst]
  · have hj2 : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap l.toRingHom := by
      apply (cancel_mono (spMap (algebraMap R (Localization.Away f)))).mp
      rw [Category.assoc, Category.assoc, GlobalTheory.Spread.spMap_algHom_comp, ← pullback.condition,
        ← pullback.condition, ← Category.assoc, hj]
    have hjb : j = GlobalTheory.Spread.bcMap pB l := GlobalTheory.Spread.eq_bcMap pB l hj hj2
    rw [hjb, ← Category.assoc, GlobalTheory.Spread.bcMap_comp_of_eq pB g l S.val hgl]
    exact (hψ i).2

end GlobalTheory
