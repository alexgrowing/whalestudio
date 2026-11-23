import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CondZIff

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def crd (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (b : Fin m → V) (a : Fin m → 𝓞 F) (x : V) (j : Fin m) : K :=
  h (b j) x / jK (ι (a j))

def gmap (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (b : Fin m → V) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) : V →ₗ[𝓞 K] V where
  toFun x := ∑ i, (∑ j, jK (Y i j) * crd h b a x j) • b i
  map_add' x y := by
    simp only [crd, map_add, add_div, mul_add, Finset.sum_add_distrib, add_smul]
  map_smul' c x := by
    simp only [crd, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_jK c x, smul_eq_jK c, smul_smul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul]; ring

section

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

theorem crd_sub (x y : V) (j : Fin m) : crd h b a (x - y) j = crd h b a x j - crd h b a y j := by
  simp only [crd, map_sub, sub_div]

theorem crd_smul (c : 𝓞 K) (x : V) (j : Fin m) : crd h b a (c • x) j = jK c * crd h b a x j := by
  unfold crd
  rw [smul_eq_jK c x, LinearMap.map_smul, smul_eq_mul, mul_div_assoc]

variable (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
include horth hdiag ha

theorem crd_sum (c : Fin m → K) (k : Fin m) : crd h b a (∑ i, c i • b i) k = c k := by
  have e : ∀ j, jK (ι (a j)) = algebraMap F K ((a j : 𝓞 F) : F) := fun j =>
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K (a j)).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K (a j))
  unfold crd
  rw [map_sum, Finset.sum_eq_single k]
  · rw [LinearMap.map_smul, hdiag k, smul_eq_mul, ← e k, mul_div_assoc,
      div_self (jK_ι_ne_zero (K := K) (ha k)), mul_one]
  · intro i _ hik
    rw [LinearMap.map_smul, horth k i (Ne.symm hik), smul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem crd_gmap (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x : V) (k : Fin m) :
    crd h b a (gmap h b a Y x) k = ∑ j, jK (Y k j) * crd h b a x j := by
  rw [show gmap h b a Y x = ∑ i, (∑ j, jK (Y i j) * crd h b a x j) • b i from rfl]
  exact crd_sum horth hdiag ha _ k

theorem h_b (x : V) (k : Fin m) : h (b k) x = jK (ι (a k)) * crd h b a x k := by
  unfold crd
  rw [mul_div_assoc', eq_div_iff (jK_ι_ne_zero (K := K) (ha k)), mul_comm]

variable (hbX : ∀ i, b i ∈ (⊤ : Submodule K V))
  (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
include hbX hloc

theorem coordsT (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x : V) : x = ∑ i, crd h b a x i • b i := G2.coords (hbX := hbX) (hloc := hloc) (horth := horth) (hdiag := hdiag) (ha := ha)
  h𝔭 hL Submodule.mem_top

theorem h_expand (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x y : V) :
    h x y = ∑ i, star (crd h b a x i) * jK (ι (a i)) * crd h b a y i := by
  have e : ∀ j, jK (ι (a j)) = algebraMap F K ((a j : 𝓞 F) : F) := fun j =>
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K (a j)).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K (a j))
  have e1 : ∀ j, h x (b j) = star (crd h b a x j) * jK (ι (a j)) := by
    intro j
    have hx := coordsT horth hdiag ha hbX hloc h𝔭 hL x
    conv_lhs => rw [hx]
    rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
    · rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hdiag j, smul_eq_mul, starRingEnd_apply, ← e j]
    · intro i _ hij
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, horth i j hij, smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hy := coordsT horth hdiag ha hbX hloc h𝔭 hL y
  conv_lhs => rw [hy]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul, e1 j, smul_eq_mul]
  ring

theorem mem_B (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x : V) :
    x ∈ locF 𝔭 L ↔ ∀ i, crd h b a x i ∈ HU.SP K 𝔭 := by
  rw [G2.mem_B_iff (hbX := hbX) (hloc := hloc) (horth := horth) (hdiag := hdiag) (ha := ha)
    h𝔭 hL x]
  exact ⟨fun hx => hx.2, fun hx => ⟨Submodule.mem_top, hx⟩⟩

theorem mem_A (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) (hL : IsLatIn ⊤ L) (x : V) :
    x ∈ locF 𝔭 (dualIn h ⊤ L) ↔ ∀ i, jK (ι (a i)) * crd h b a x i ∈ HU.SP K 𝔭 := by
  rw [G2.mem_locF_dualIn_iff (hbX := hbX) (hloc := hloc) (horth := horth) (hdiag := hdiag) (ha := ha)
    hF h𝔭 hL x]
  refine ⟨fun hx i => ?_, fun hx => ⟨Submodule.mem_top, fun i => ?_⟩⟩
  · rw [← h_b horth hdiag ha x i]
    exact hx.2 i
  · rw [h_b horth hdiag ha x i]
    exact hx i

end

end Formalism.L2.SG.Pf.fibreCountingData
