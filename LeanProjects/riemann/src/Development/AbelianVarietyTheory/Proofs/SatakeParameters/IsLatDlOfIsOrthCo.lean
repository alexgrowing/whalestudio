import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.OrthDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem int_mem_range {t : E} (h : IsIntegral ℤ t) : t ∈ (algebraMap (𝓞 E) E).range :=
  ⟨⟨t, h⟩, rfl⟩

theorem ringHom_mem_range (τ : E →+* E) {t : E} (h : t ∈ (algebraMap (𝓞 E) E).range) :
    τ t ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨r, rfl⟩ := h
  exact int_mem_range (IsIntegral.map τ.toIntAlgHom r.isIntegral_coe)

theorem exists_int_smul_mem (M : Submodule (𝓞 E) (Fin N → E)) {v : Fin N → E}
    (hv : v ∈ Submodule.span E (M : Set (Fin N → E))) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, mul_ne_zero h₁ h₂, ?_⟩
    have e : ((n₁ * n₂ : ℤ) : E) • (x + y) = n₂ • ((n₁ : E) • x) + n₁ • ((n₂ : E) • y) := by
      rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, smul_add]
      push_cast
      rw [mul_comm (n₂ : E)]
    rw [e]
    exact add_mem (zsmul_mem hx _) (zsmul_mem hy _)
  | smul e x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨k, hk, hki⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hke := hki e (Finset.mem_singleton_self e)
    refine ⟨k * n, mul_ne_zero hk hn, ?_⟩
    have e1 : ((k * n : ℤ) : E) • (e • x) = (⟨k • e, hke⟩ : 𝓞 E) • ((n : E) • x) := by
      rw [← algebraMap_smul E (⟨k • e, hke⟩ : 𝓞 E), smul_smul, smul_smul]
      congr 1
      show ((k * n : ℤ) : E) * e = (k • e) * n
      push_cast
      rw [zsmul_eq_mul]
      ring
    rw [e1]
    exact M.smul_mem _ hx

theorem isLat_dl (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E))
    (hc : Formalism.L2.PairingIndexBounds.F.IsOrthCo (σ : E →+* E) J co) (M : Submodule (𝓞 E) (Fin N → E))
    (hM : Formalism.L2.GlobalTheoryTheory.Comp.IsLat M) : Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M) := by
  classical
  set v : Fin N → Fin N → E := fun a => co.symm (Pi.single a 1) with hv
  have key : ∀ x y, Formalism.UG.hform (σ : E →+* E) J x y = ∑ b, (σ : E →+* E) (co x b) * co y b :=
    fun x y => (hc x y).symm
  have hsingle : ∀ (a : Fin N) (c : E), Pi.single a c = c • (Pi.single a (1 : E) : Fin N → E) := by
    intro a c; ext j; simp [Pi.single_apply]
  have hexp : ∀ z : Fin N → E, z = ∑ a, co z a • v a := by
    intro z
    conv_lhs => rw [← co.symm_apply_apply z, ← Finset.univ_sum_single (co z)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsingle, map_smul]
  have hcv : ∀ (c : E) a b, co (c • v a) b = if b = a then c else 0 := by
    intro c a b; simp [v, Pi.single_apply]
  have hform_v : ∀ (c : E) a x, Formalism.UG.hform (σ : E →+* E) J x (c • v a) = (σ : E →+* E) (co x a) * c := by
    intro c a x; rw [key]; simp [hcv]

  have hex : ∀ a, ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v a ∈ M := fun a =>
    exists_int_smul_mem M (by rw [hM.2]; trivial)
  choose n hn0 hnM using hex
  have hle : Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M ≤
      Submodule.span (𝓞 E) (Set.range fun a => ((n a : E))⁻¹ • v a) := by
    intro y hy
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl] at hy
    have hr : ∀ a, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = (n a : E) * co y a := by
      intro a
      obtain ⟨r, hr⟩ := hy _ (hnM a)
      refine ⟨r, ?_⟩
      rw [hr, key, Finset.sum_eq_single a]
      · rw [hcv, if_pos rfl, map_intCast]
      · intro b _ hb
        rw [hcv, if_neg hb, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ a) h
    choose r hr using hr
    rw [hexp y]
    refine Submodule.sum_mem _ fun a _ => ?_
    have e3 : co y a • v a = r a • (((n a : E))⁻¹ • v a) := by
      rw [← algebraMap_smul E (r a), smul_smul, hr a, mul_comm (n a : E), mul_assoc,
        mul_inv_cancel₀ (Int.cast_ne_zero.2 (hn0 a)), mul_one]
    rw [e3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  haveI : Module.Finite (𝓞 E) (Submodule.span (𝓞 E) (Set.range fun a => ((n a : E))⁻¹ • v a)) :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  refine ⟨Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle), ?_⟩

  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hM.1
  obtain ⟨m, hm0, hmi⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (s.biUnion fun x => Finset.univ.image fun b => co x b)
  have hint : ∀ a, ∀ x ∈ M, (m : E) * co x a ∈ (algebraMap (𝓞 E) E).range := by
    intro a x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      apply int_mem_range
      have := hmi (co x a) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩)
      rwa [zsmul_eq_mul] at this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, Pi.add_apply, mul_add]; exact add_mem hx hy
    | smul t x _ hx =>
      rw [← algebraMap_smul E t x, map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact mul_mem ⟨t, rfl⟩ hx
  have hmem : ∀ a, (m : E) • v a ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M := by
    intro a
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl]
    intro x hx
    rw [hform_v]
    have e4 : (σ : E →+* E) (co x a) * (m : E) = (σ : E →+* E) ((m : E) * co x a) := by
      rw [map_mul, map_intCast, mul_comm]
    rw [e4]
    exact ringHom_mem_range _ (hint a x hx)
  rw [eq_top_iff]
  intro z _
  rw [hexp z]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  have e5 : v a = ((m : E))⁻¹ • ((m : E) • v a) := by
    rw [smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hm0), one_smul]
  rw [e5]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem a))

end GlobalTheory.OrthDual

theorem GlobalTheory.isLat_dl_of_isOrthCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), (∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) → ∀ M : Submodule (𝓞 E) (Fin N → E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat M → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M) := by
  rintro R F E _ _ _ _ _ _ sp N J ⟨co, hc⟩ M hM
  exact GlobalTheory.OrthDual.isLat_dl sp.cm.sig J co hc M hM

end
