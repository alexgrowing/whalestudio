import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem exists_algHom_away_comp {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] (r : R) (hr : r ≠ 0) (C : Type) [CommRing C] [Algebra R C] [Algebra (Localization.Away r) C]
    [IsScalarTower R (Localization.Away r) C] [Module.Finite (Localization.Away r) C] (ψ₀ : C →ₐ[R] K) :
    ∃ (e : C →ₐ[R] Localization.Away r) (w : Localization.Away r →ₐ[R] K), w.comp e = ψ₀ := by
  have hle : Submonoid.powers r ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr
  let L := Localization.Away r
  let w : L →ₐ[R] K := ψ₀.comp (IsScalarTower.toAlgHom R L C)
  letI : Algebra L K := (w : L →+* K).toAlgebra
  haveI : IsScalarTower R L K := IsScalarTower.of_algebraMap_eq fun x => (w.commutes x).symm
  haveI : IsDomain L := IsLocalization.isDomain_localization hle
  haveI : IsIntegrallyClosed L := isIntegrallyClosed_of_isLocalization L (Submonoid.powers r) hle
  haveI : IsFractionRing L K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r) L K
  let ψ₁ : C →ₐ[L] K := { (ψ₀ : C →+* K) with commutes' := fun x => rfl }
  have hmem : ∀ x : C, ψ₀ x ∈ w.range := fun x => by
    have h : IsIntegral L (ψ₁ x) := (Algebra.IsIntegral.isIntegral x).map ψ₁
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    exact ⟨y, hy⟩
  have hinj : Function.Injective w := IsFractionRing.injective L K
  refine ⟨((AlgEquiv.ofInjective w hinj).symm : w.range →ₐ[R] L).comp (ψ₀.codRestrict w.range hmem), w, ?_⟩
  ext x
  have := AlgEquiv.ofInjective_apply w hinj ((AlgEquiv.ofInjective w hinj).symm ⟨ψ₀ x, hmem x⟩)
  rw [AlgEquiv.apply_symm_apply] at this
  exact this.symm

theorem PreChart.exists_translation (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (N : ℕ) (q : PrimeSpectrum R) (c : PreChart G N q) (hc : c.IsGrp) (ψ₀ : c.C →ₐ[R] K) :
    ∃ T : c.C →ₐ[R] c.C, ∀ ψ : c.C →ₐ[R] K, torsMap (ψ.comp T) c.j = torsMap ψ₀ c.j * torsMap ψ c.j := by
  have hr : c.r ≠ 0 := fun h => c.hr (h ▸ q.asIdeal.zero_mem)
  obtain ⟨e, w, he⟩ := exists_algHom_away_comp c.r hr c.C ψ₀
  let u : Localization.Away c.r →ₐ[R] c.C := IsScalarTower.toAlgHom R _ c.C
  obtain ⟨T, hT⟩ := hc.2 c.C (u.comp e) (AlgHom.id R c.C)
  refine ⟨T, fun ψ => ?_⟩
  have hcomp : ∀ φ : c.C →ₐ[R] c.C, torsMap (ψ.comp φ) c.j = torsMap ψ (torsMap φ c.j) := fun φ => by
    apply Subtype.ext
    simp only [torsMap_val, ← spOver_comp, Category.assoc]
  have hmul : ∀ x y : Tors G N c.C, torsMap ψ (x * y) = torsMap ψ x * torsMap ψ y := fun x y => by
    apply Subtype.ext
    simp only [torsMap_val, tors_mul_val, MonObj.comp_mul]
  have hu : ψ.comp u = w := IsLocalization.algHom_ext (Submonoid.powers c.r) (Subsingleton.elim _ _)
  rw [hcomp, hT, hmul, ← hcomp, ← hcomp, ← AlgHom.comp_assoc, hu, he, AlgHom.comp_id]

end GlobalTheory.GroupBplus.Aff
