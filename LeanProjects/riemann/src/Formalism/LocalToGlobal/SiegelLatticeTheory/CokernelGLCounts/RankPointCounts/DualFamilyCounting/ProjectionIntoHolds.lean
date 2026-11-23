import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BigLineBundleMoriwaki
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtAdjoinIff

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {v : V} :
    v ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem form_ozmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) (y v : V) : h y (c • v) = c • h y v := by
  rw [← algebraMap_smul K c v, LinearMap.map_smul, algebraMap_smul]

theorem form_ozmul_left_mem (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) {y v : V}
    (hy : h y v ∈ (1 : Submodule (𝓞 K) K)) : h (c • y) v ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← algebraMap_smul K c y, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨c0, hc0⟩ := Submodule.mem_one.mp (VecSplit.star_alg_mem_one c)
  obtain ⟨z0, hz0⟩ := Submodule.mem_one.mp hy
  exact Submodule.mem_one.mpr ⟨c0 * z0, by rw [map_mul, hc0, hz0]⟩

theorem mem_locF_dualIn {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V}
    (hL : L.FG) (𝔭 : Ideal (𝓞 F)) {v : V} (hv : v ∈ X)
    (H : ∀ y ∈ L, h y v ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) : v ∈ locF 𝔭 (dualIn h X L) := by
  classical
  obtain ⟨s, hs⟩ := hL
  have H' : ∀ y ∈ s, ∃ t ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
      t • h y v ∈ (1 : Submodule (𝓞 K) K) := by
    intro y hy
    exact H y (hs ▸ Submodule.subset_span hy)
  choose! t ht using H'
  refine ⟨∏ y ∈ s, t y, Submonoid.prod_mem _ fun y hy => (ht y hy).1, ?_⟩
  refine ⟨X.restrictScalars (𝓞 K) |>.smul_mem _ hv, ?_⟩
  show (∏ y ∈ s, t y) • v ∈ Formalism.HermitianLatticesTheory.dual h L
  rw [mem_dual_iff]
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [form_ozmul_right, ← Finset.prod_erase_mul s t hy, mul_smul]
    exact Submodule.smul_mem _ _ (ht y hy).2
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact form_ozmul_left_mem h c ha

theorem projection_into_holds : ProjInto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd X Y hc hXY L hL 𝔭 h𝔭 Λ hΛ0 hΛd hΛX x hx
  apply mem_locF_dualIn hL.1 𝔭 (Submodule.projection_apply_mem hc x)
  intro y hy
  have hyΛ : y ∈ Λ := by
    have : y ∈ locF 𝔭 L := LocalizedFibreSets.le_locF 𝔭 L hy
    rw [← hΛX] at this
    exact this.1
  have hyX : y ∈ X := le_of_isLatIn hL y hy
  have e := Submodule.projection_add_projection_eq_self hc x
  have h0 : h y (Y.projection X hc.symm x) = 0 := hXY y hyX _ (Submodule.projection_apply_mem _ x)
  have hx' : x ∈ dualF h 𝔭 Λ := by rw [hΛd]; exact hx
  have := hx' y hyΛ
  rw [← e, map_add, h0, add_zero] at this
  exact this

end Formalism.L2.SG.Pf.G6
