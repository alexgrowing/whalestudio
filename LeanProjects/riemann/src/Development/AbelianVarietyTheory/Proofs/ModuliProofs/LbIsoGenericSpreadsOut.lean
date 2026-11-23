import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericLB

open Spread

private theorem lbIso_pull_iff_lbIso_pull_pull_of_eq_comp {W X Y : Scheme.{0}} {M N : LB X} (hM : M.IsLB) (hN : N.IsLB) {a : Y ⟶ X}
    (j : W ⟶ Y) {a' : W ⟶ X} (ha : a' = j ≫ a) :
    LBIso (M.pull a') (N.pull a') ↔ LBIso ((M.pull a).pull j) ((N.pull a).pull j) := by
  have hM' := pull_isLB hM a'
  have hN' := pull_isLB hN a'
  have hMj := pull_isLB (pull_isLB hM a) j
  have hNj := pull_isLB (pull_isLB hN a) j
  constructor
  · intro h
    exact LBIso.trans hMj hM' hNj (LBIso.symm (lbIso_pull_pull hM j ha))
      (LBIso.trans hM' hN' hNj h (lbIso_pull_pull hN j ha))
  · intro h
    exact LBIso.trans hM' hMj hN' (lbIso_pull_pull hM j ha)
      (LBIso.trans hMj hNj hN' h (LBIso.symm (lbIso_pull_pull hN j ha)))

theorem exists_finset_lbIso {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {B : Scheme.{0}} (pB : B ⟶ Sp k)
    [QuasiCompact pB] [QuasiSeparated pB] {M N : LB B} (hM : M.IsLB) (hN : N.IsLB)
    (H : LBIso (M.pull (pullback.fst pB (spMap (algebraMap k A)))) (N.pull (pullback.fst pB (spMap (algebraMap k A))))) :
    ∃ s : Finset A, LBIso (M.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A))))))
      (N.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A)))))) := by
  classical
  obtain ⟨j, g, hg⟩ := exists_lbIso_of_isLimit (D := bcDiagram pB A)
    (π := fun s => bcMap pB (Algebra.adjoin k (s.unop : Set A)).val)
    (w := fun {s t} f => bcMap_comp_of_eq pB _ _ _ fun _ => rfl)
    (hc := isLimitBcCone pB A) (i := Opposite.op ∅)
    (M := M.pull (pullback.fst _ _)) (N := N.pull (pullback.fst _ _))
    (hM := pull_isLB hM _) (hN := pull_isLB hN _)
    (h := (lbIso_pull_iff_lbIso_pull_pull_of_eq_comp hM hN _ (bcMap_fst pB _).symm).mp H)
  exact ⟨j.unop, (lbIso_pull_iff_lbIso_pull_pull_of_eq_comp hM hN ((bcDiagram pB A).map g) (bcMap_fst pB _).symm).mpr hg⟩

theorem exists_denom {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (s : Finset K) : ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      ∃ ψ : Algebra.adjoin R (s : Set K) →+* R', ψ.comp (algebraMap R _) = φ := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) s
  refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
  intro R' _ φ hφ
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hunit : IsUnit (algebraMap R K (b : R)) := IsLocalization.map_units K b
  let g0 : Localization.Away (b : R) →+* K := IsLocalization.Away.lift (b : R) hunit
  have hg0 : ∀ r : R, g0 (algebraMap R _ r) = algebraMap R K r := fun r => IsLocalization.lift_eq _ r
  let g : Localization.Away (b : R) →ₐ[R] K := { g0 with commutes' := hg0 }
  have hinj : Function.Injective g := by
    change Function.Injective g0
    refine (IsLocalization.lift_injective_iff _).mpr fun x y => ?_
    exact ((IsLocalization.injective (Localization.Away (b : R))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hb0)).eq_iff).trans
      (IsFractionRing.injective R K).eq_iff.symm
  have hle : Algebra.adjoin R (s : Set K) ≤ g.range := by
    refine Algebra.adjoin_le fun x hx => ?_
    obtain ⟨a, ha⟩ := hb x hx
    refine ⟨IsLocalization.mk' (Localization.Away (b : R)) a ⟨(b : R), Submonoid.mem_powers _⟩, ?_⟩
    show IsLocalization.Away.lift (b : R) hunit _ = x
    unfold IsLocalization.Away.lift
    rw [IsLocalization.lift_mk'_spec]
    rw [ha, Algebra.smul_def]
  refine ⟨((IsLocalization.Away.lift (b : R) hφ).comp
    ((AlgEquiv.ofInjective g hinj).symm : g.range →ₐ[R] Localization.Away (b : R)).toRingHom).comp
    (Subalgebra.inclusion hle).toRingHom, ?_⟩
  ext r
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  exact IsLocalization.lift_eq _ r

end GenericLB

theorem lbIso_generic_spreads_out : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M N : LB B), QuasiCompact pB → QuasiSeparated pB → M.IsLB → N.IsLB → LBIso (M.pull (pullback.fst pB (spMap (algebraMap R K)))) (N.pull (pullback.fst pB (spMap (algebraMap R K)))) → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → LBIso (M.pull (pullback.fst pB (spMap φ))) (N.pull (pullback.fst pB (spMap φ))) := by
  intro R K _ _ _ _ _ _ B pB M N hqc hqs hM hN H
  have := hqc
  have := hqs
  obtain ⟨s, hs⟩ := GenericLB.exists_finset_lbIso pB hM hN H
  obtain ⟨f, hf0, hf⟩ := GenericLB.exists_denom (R := R) s
  refine ⟨f, hf0, fun R' _ φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := hf R' φ hφ
  have key : spMap φ = spMap ψ ≫ spMap (algebraMap R (Algebra.adjoin R (s : Set K))) := by
    rw [spMap_comp_ring, hψ]
  exact Spread.lbIso_pull_comp
    (pullback.lift (pullback.fst pB (spMap φ)) (pullback.snd _ _ ≫ spMap ψ)
      (by rw [pullback.condition, key, Category.assoc]))
    (pullback.lift_fst _ _ _).symm (pullback.lift_fst _ _ _).symm hs

end GlobalTheory
