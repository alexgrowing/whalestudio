import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlockGLSupportedMemMirabolicSupported
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates

open scoped TensorProduct nonZeroDivisors

theorem exists_nat_eq_mul {E : Type} [Field E] [NumberField E] {a : 𝓞 E} (ha : a ≠ 0) :
    ∃ (k : ℕ) (b : 𝓞 E), k ≠ 0 ∧ (k : 𝓞 E) = b * a := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  refine ⟨Ideal.absNorm (Ideal.span {a}), b, ?_, hb.symm⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact ha

theorem exists_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ], ∃ N : ℕ, Module.finrank ℚ E * N = Module.finrank ℤ Λ ∧ ∃ e : Λ →+ (Fin N → E), Function.Injective e ∧ (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) ∧ ∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v := by
  intro E _ _ _ Λ _ _ _ _
  let f : Λ →ₗ[𝓞 E] E ⊗[𝓞 E] Λ := TensorProduct.mk (𝓞 E) E Λ 1
  have hb : IsBaseChange E f := TensorProduct.isBaseChange _ _ _
  haveI h1 : IsLocalizedModule (𝓞 E)⁰ f := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E f).2 hb
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) f :=
    (isLocalizedModule_iff_isBaseChange _ E f).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (f.restrictScalars ℤ) := IsLocalizedModule.restrictScalars _ f
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Λ
  have hrank : Module.finrank ℚ E * Module.finrank E (E ⊗[𝓞 E] Λ) = Module.finrank ℤ Λ := by
    rw [← IsLocalizedModule.finrank_eq ℤ⁰ (f.restrictScalars ℤ) le_rfl,
      ← IsLocalization.finrank_eq ℚ ℤ⁰ le_rfl, Module.finrank_mul_finrank]
  have htors : ∀ x : Λ, f x = 0 → x = 0 := by
    intro x hx
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (𝓞 E)⁰ f).1 hx
    obtain ⟨k, b, hk, hkb⟩ := exists_nat_eq_mul (nonZeroDivisors.coe_ne_zero c)
    have hkx : (k : ℤ) • x = 0 := by
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), hkb, mul_smul]
      have : (c : 𝓞 E) • x = 0 := hc
      rw [this, smul_zero]
    exact (smul_eq_zero.1 hkx).resolve_left (by exact_mod_cast hk)
  let g := (Module.finBasis E (E ⊗[𝓞 E] Λ)).equivFun
  refine ⟨Module.finrank E (E ⊗[𝓞 E] Λ), hrank,
    AddMonoidHom.mk' (fun x => g (f x)) (fun x y => by simp only [map_add]), ?_, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => htors x ?_
    exact g.map_eq_zero_iff.1 hx
  · intro a x
    change g (f (a • x)) = (a : E) • g (f x)
    rw [map_smul, ← map_smul g]
    congr 1
  · intro v
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (𝓞 E)⁰ f (g.symm v)
    obtain ⟨k, b, hk, hkb⟩ := exists_nat_eq_mul (nonZeroDivisors.coe_ne_zero s)
    refine ⟨k, b • x, hk, ?_⟩
    change g (f (b • x)) = k • v
    have hs' : (s : 𝓞 E) • g.symm v = f x := hs
    rw [map_smul, ← hs', ← mul_smul, ← hkb, Nat.cast_smul_eq_nsmul, map_nsmul, LinearEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates
