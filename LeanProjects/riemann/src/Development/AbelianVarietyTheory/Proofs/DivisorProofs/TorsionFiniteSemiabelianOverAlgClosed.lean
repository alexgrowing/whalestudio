import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTorsionPrechartCoverStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.TorsFin

theorem finite_algHom_of_away (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (r : R) (hr : r ≠ 0) (C : Type) [CommRing C] [Algebra R C] [Algebra (Localization.Away r) C]
    [IsScalarTower R (Localization.Away r) C] [Module.Finite (Localization.Away r) C]
    [Module.Free (Localization.Away r) C] : Finite (C →ₐ[R] K) := by
  have hu : IsUnit (algebraMap R K r) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hr).isUnit
  letI : Algebra (Localization.Away r) K := (IsLocalization.Away.lift r hu).toAlgebra
  haveI : Nontrivial (Localization.Away r) := (algebraMap (Localization.Away r) K).domain_nontrivial
  have key : ∀ ψ : C →ₐ[R] K, (ψ : C →+* K).comp (algebraMap (Localization.Away r) C) =
      algebraMap (Localization.Away r) K := by
    intro ψ
    refine IsLocalization.ringHom_ext (Submonoid.powers r) ?_
    ext x
    have h1 : algebraMap (Localization.Away r) K (algebraMap R (Localization.Away r) x) = algebraMap R K x :=
      IsLocalization.Away.lift_eq r hu x
    simp only [RingHom.comp_apply, h1, ← IsScalarTower.algebraMap_apply]
    exact ψ.commutes x
  let f : (C →ₐ[R] K) → (C →ₐ[Localization.Away r] K) := fun ψ =>
    { (ψ : C →+* K) with commutes' := fun x => congrArg (fun g : _ →+* K => g x) (key ψ) }
  refine Finite.of_injective f ?_
  intro ψ ψ' h
  ext x
  exact congrArg (fun g : C →ₐ[Localization.Away r] K => g x) h

theorem finite_tors : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → Finite (Tors G N K) := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN
  obtain ⟨Idx, _, q, c, hc⟩ := GlobalTheory.T.exists_finite_torsion_prechart_cover R K G hG N hN
  haveI : ∀ i, Finite ((c i).C →ₐ[R] K) := fun i =>
    finite_algHom_of_away R K (c i).r (fun h => (c i).hr (h ▸ (q i).asIdeal.zero_mem)) (c i).C
  refine Finite.of_surjective
    (fun x : Σ i, ((c i).C →ₐ[R] K) => torsMap x.2 (c x.1).j) ?_
  intro z
  obtain ⟨i, hi⟩ := hc K z
  obtain ⟨ψ, -, hψ⟩ := ((c i).bij K).surjOn hi
  exact ⟨⟨i, ψ⟩, hψ⟩

end GlobalTheory.GroupBplus.Aff.TorsFin
