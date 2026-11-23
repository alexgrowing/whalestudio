import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocalOfFam
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlmostEverywhereSpherical
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem jι_eq' (t : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := by
  have e := UnimodularLocalization.algebraMap_smul_K (K := K) t (1 : K)
  rwa [Algebra.smul_def, mul_one, mul_one] at e

theorem inP_of_mem_pow {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {t : 𝓞 F} (ht : t ∈ 𝔭 ^ k) :
    InP 𝔭 k (algebraMap F K (t : F)) := by
  rw [← jι_eq']
  apply inP_jK
  rw [extP, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ht

theorem inP_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ≠ 0) :
    InP 𝔭 (vF 𝔭 t) (algebraMap F K (t : F)) := by
  have := h𝔭.isPrime
  exact inP_of_mem_pow ((G1.mem_pow_iff h𝔭 ht _).2 le_rfl)

theorem mem_SP_of_inP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {π s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π s₀) {k : ℕ}
    {x : K} (hx : InP 𝔭 k x) : (algebraMap F K (π : F))⁻¹ ^ k * x ∈ SP K 𝔭 := by
  obtain ⟨s, hs, rfl⟩ := (mem_noncompactPart_iff hu k x).1 hx
  have h0 : algebraMap F K (π : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  rw [jι_eq', ← mul_assoc, ← mul_pow, inv_mul_cancel₀ h0, one_pow, one_mul]
  exact hs

theorem star_fix (hF : IsFixF K F) (x : F) : star (algebraMap F K x) = algebraMap F K x :=
  (hF _).2 ⟨x, rfl⟩

theorem star_inv_pow (hF : IsFixF K F) (x : F) (k : ℕ) :
    star ((algebraMap F K x)⁻¹ ^ k) = (algebraMap F K x)⁻¹ ^ k := by
  rw [← map_inv₀, ← map_pow]; exact star_fix hF _

theorem form_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (r : K) (x y : V) :
    h (r • x) y = star r * h x y := by
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem form_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : K) (x y : V) :
    h x (r • y) = r * h x y := by
  rw [map_smul, smul_eq_mul]

theorem form_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (r r' : K) (x y : V) :
    h (r • x) (r' • y) = star r * r' * h x y := by
  rw [form_smul_left, form_smul_right]; ring

end Formalism.L2.SG.Pf.GluingBases
