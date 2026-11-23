import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrechartTranslateOrderStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartLocAway

theorem chart_isLocalization_away : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] (io : A ≃ₐ[R] ord G N K) (θ : TorsPt G N A), (∀ (x : Tors G N K) (a : A), θ.pt K x a = (io a : Tors G N K → K) x) → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), c.IsGrp → ∃ e : A, @IsLocalization.Away A _ e c.C _ (θ.pt c.C c.j).toRingHom.toAlgebra := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN A _ _ io θ hθ q c hc
  have hsep := (GlobalTheory.T.torsion_prechart_points_separate R K G hG N hN q c).2
  have hext := GlobalTheory.T.prechart_translate_order R K G hG N hN q c hc 1
  set ρ : A →ₐ[R] c.C := θ.pt c.C c.j with hρ
  have key : ∀ (ψ : c.C →ₐ[R] K) (a : A), ψ (ρ a) = (io a : Tors G N K → K) (torsMap ψ c.j) := by
    intro ψ a
    rw [← hθ, θ.nat]
    rfl
  have lift : ∀ u : c.C, ∃ (k : ℕ) (a : A), ρ a = algebraMap R c.C c.r ^ k * u ∧
      ∀ x, (∀ ψ : c.C →ₐ[R] K, x ≠ torsMap ψ c.j) → (io a : Tors G N K → K) x = 0 := by
    intro u
    obtain ⟨k, g, hg, h1, h2⟩ := hext u
    refine ⟨k, io.symm ⟨g, hg⟩, ?_, ?_⟩
    · rw [← sub_eq_zero]
      apply hsep
      intro ψ
      have := h1 ψ
      rw [_root_.one_mul] at this
      rw [map_sub, key, AlgEquiv.apply_symm_apply, map_mul, map_pow, AlgHom.commutes]
      exact sub_eq_zero.2 this
    · intro x hx
      rw [AlgEquiv.apply_symm_apply]
      exact h2 x (fun ψ => by rw [_root_.one_mul]; exact hx ψ)
  obtain ⟨k, e₀, he₀, he₀z⟩ := lift 1
  rw [_root_.mul_one] at he₀
  have hr : IsUnit (algebraMap R c.C c.r) := by
    rw [IsScalarTower.algebraMap_apply R (Localization.Away c.r) c.C]
    exact (IsLocalization.Away.algebraMap_isUnit c.r).map _
  have he : ρ (algebraMap R A c.r * e₀) = algebraMap R c.C c.r ^ (k + 1) := by
    rw [map_mul, AlgHom.commutes, he₀, pow_succ']
  refine ⟨algebraMap R A c.r * e₀, ?_⟩
  letI : Algebra A c.C := ρ.toRingHom.toAlgebra
  have ham : ∀ a, algebraMap A c.C a = ρ a := fun _ => rfl
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [ham, he]
    exact hr.pow _
  · intro u
    obtain ⟨m, a, ha, -⟩ := lift u
    refine ⟨m, algebraMap R A c.r ^ (k * m) * a, ?_⟩
    rw [ham, ham, he, map_mul, map_pow, AlgHom.commutes, ha]
    ring
  · intro a b hab
    rw [ham, ham] at hab
    refine ⟨1, ?_⟩
    have : e₀ * a = e₀ * b := by
      apply io.injective
      apply Subtype.ext
      funext x
      rw [map_mul, map_mul]
      show (io e₀ : Tors G N K → K) x * (io a : Tors G N K → K) x
        = (io e₀ : Tors G N K → K) x * (io b : Tors G N K → K) x
      by_cases hx : ∃ ψ : c.C →ₐ[R] K, x = torsMap ψ c.j
      · obtain ⟨ψ, rfl⟩ := hx
        rw [← key ψ a, ← key ψ b, hab]
      · rw [he₀z x (fun ψ h => hx ⟨ψ, h⟩), zero_mul, zero_mul]
    rw [pow_one, _root_.mul_assoc, _root_.mul_assoc, this]

end GlobalTheory.ChartLocAway
