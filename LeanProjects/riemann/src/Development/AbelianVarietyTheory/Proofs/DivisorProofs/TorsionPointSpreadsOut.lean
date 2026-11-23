import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPrechartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointSection
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.TorsLift

theorem torsMap_torsMap {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}
    {B C D : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (φ : B →ₐ[R] C) (ψ : C →ₐ[R] D) (z : Tors G N B) : torsMap ψ (torsMap φ z) = torsMap (ψ.comp φ) z := by
  apply Subtype.ext
  simp only [torsMap_val]
  rw [← Category.assoc]
  first | rw [spOver_comp] | rw [← spOver_comp]

def extendAway {R : Type} [CommRing R] (r : R) {A T : Type} [CommRing A] [Algebra R A]
    [Algebra (Localization.Away r) A] [IsScalarTower R (Localization.Away r) A] [CommRing T] [Algebra R T]
    [Algebra (Localization.Away r) T] [IsScalarTower R (Localization.Away r) T] (f : A →ₐ[R] T) :
    A →ₐ[Localization.Away r] T :=
  { f with
    commutes' := fun x => by
      haveI := IsLocalization.algHom_subsingleton (R := R) (M := Submonoid.powers r)
        (S := Localization.Away r) (P := T)
      have h := congrArg (fun g : Localization.Away r →ₐ[R] T => g x)
        (Subsingleton.elim (f.comp (IsScalarTower.toAlgHom R (Localization.Away r) A))
          (IsScalarTower.toAlgHom R (Localization.Away r) T))
      simpa using h }

@[simp] theorem extendAway_apply {R : Type} [CommRing R] (r : R) {A T : Type} [CommRing A] [Algebra R A]
    [Algebra (Localization.Away r) A] [IsScalarTower R (Localization.Away r) A] [CommRing T] [Algebra R T]
    [Algebra (Localization.Away r) T] [IsScalarTower R (Localization.Away r) T] (f : A →ₐ[R] T) (a : A) :
    extendAway r f a = f a := rfl

end GlobalTheory.GroupBplus.Aff.TorsLift

open GlobalTheory.GroupBplus.Aff.TorsLift in

theorem GlobalTheory.GroupBplus.Aff.exists_tors_lift_away : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (k : Type) [Field k] [Algebra R k] (z : Tors G N k), ∃ (r : R) (ψ : Localization.Away r →ₐ[R] k) (z' : Tors G N (Localization.Away r)), torsMap ψ z' = z := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN k _ _ z
  classical
  let q : PrimeSpectrum R := ⟨RingHom.ker (algebraMap R k), RingHom.ker_isPrime _⟩
  obtain ⟨c⟩ := GlobalTheory.T.exists_torsion_prechart R K G hG N hN q
  obtain ⟨hfin, hsep⟩ := GlobalTheory.T.torsion_prechart_points_separate R K G hG N hN q c
  obtain ⟨ψ, -, hψ⟩ := (c.bij k).surjOn (c.fibre k rfl z)
  have hr0 : c.r ≠ 0 := fun h => c.hr (h ▸ q.asIdeal.zero_mem)
  have hrk : IsUnit (algebraMap R k c.r) := isUnit_iff_ne_zero.mpr fun h => c.hr (RingHom.mem_ker.mpr h)
  have hrK : IsUnit (algebraMap R K c.r) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr0)
  letI : Algebra (Localization.Away c.r) k := (Localization.awayLift (algebraMap R k) c.r hrk).toAlgebra
  haveI : IsScalarTower R (Localization.Away c.r) k :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq c.r hrk x).symm
  letI : Algebra (Localization.Away c.r) K := (Localization.awayLift (algebraMap R K) c.r hrK).toAlgebra
  haveI : IsScalarTower R (Localization.Away c.r) K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq c.r hrK x).symm
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  haveI : IsDomain (Localization.Away c.r) := IsLocalization.isDomain_localization hle
  haveI : IsIntegrallyClosed (Localization.Away c.r) := isIntegrallyClosed_of_isLocalization _ _ hle
  haveI : IsFractionRing (Localization.Away c.r) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers c.r) (Localization.Away c.r) K
  haveI : Finite (c.C →ₐ[Localization.Away c.r] K) :=
    Finite.of_injective (fun f => f.restrictScalars R) (AlgHom.restrictScalars_injective R)
  have hsep' : ∀ a : c.C, (∀ f : c.C →ₐ[Localization.Away c.r] K, f a = 0) → a = 0 :=
    fun a ha => hsep a fun f => by simpa using ha (extendAway c.r f)
  obtain ⟨s, hs⟩ := GlobalTheory.finiteAlg_fieldPoint_factors_through_base (Localization.Away c.r) K c.C hsep' k
    (extendAway c.r ψ)
  refine ⟨c.r, (Algebra.ofId (Localization.Away c.r) k).restrictScalars R, torsMap (s.restrictScalars R) c.j, ?_⟩
  rw [torsMap_torsMap, ← hψ]
  congr 1
  ext a
  have h := congrArg (fun g : c.C →ₐ[Localization.Away c.r] k => g a) hs
  simp only [extendAway_apply] at h
  rw [h]
  rfl
