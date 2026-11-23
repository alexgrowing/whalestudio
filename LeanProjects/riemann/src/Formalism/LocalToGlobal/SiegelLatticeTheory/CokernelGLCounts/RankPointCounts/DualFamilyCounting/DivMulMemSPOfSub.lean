import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscEquiv
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapes
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityEighth

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem jK_conjO (z : 𝓞 K) : jK (conjO K z) = star (jK z) := rfl

theorem jK_star (z : 𝓞 K) : jK (star z) = star (jK z) := rfl

theorem star_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (hF : IsFixF K F) {r : K}
    (hr : r ∈ HU.SP K 𝔭) : star r ∈ HU.SP K 𝔭 := by
  obtain ⟨t, ht, z, hz⟩ := HU.mem_SP.1 hr
  refine HU.mem_SP.2 ⟨t, ht, conjO K z, ?_⟩
  rw [jK_conjO, hz, star_mul', star_jK_ι hF, mul_comm]

theorem extP_pow (𝔭 : Ideal (𝓞 F)) (k : ℕ) : extP K 𝔭 ^ k = (𝔭 ^ k).map ι := by
  rw [extP, Ideal.map_pow]

theorem exists_sub_mul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} (hd : d ≠ 0) {z : 𝓞 K}
    (hz : haveI := h𝔭.isPrime; jK z / jK (ι d) ∈ HU.SP K 𝔭) (k : ℕ) :
    ∃ w : 𝓞 K, z - w * ι d ∈ extP K 𝔭 ^ k := by
  have := h𝔭.isPrime
  obtain ⟨t, ht, w, hw⟩ := HU.mem_SP.1 hz
  obtain ⟨u, hu⟩ := exists_inv_mod h𝔭 ht k
  refine ⟨ι u * w, ?_⟩
  have e : w * ι d = ι t * z := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [map_mul, map_mul, hw, mul_assoc, div_mul_cancel₀ _ (jK_ι_ne_zero hd)]
  have e2 : z - ι u * w * ι d = ι (1 - t * u) * z := by
    rw [mul_assoc, e, map_sub, map_one, map_mul]; ring
  rw [e2, extP_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hu)

theorem div_mem_SP_of_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} (hd : d ≠ 0) {x : 𝓞 K}
    {k : ℕ} (hk : vF 𝔭 d ≤ k) (hx : x ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK x / jK (ι d) ∈ HU.SP K 𝔭 :=
  (div_mem_SP_iff h𝔭 hd _).2 (Ideal.pow_le_pow_right hk hx)

theorem div_mul_mem_SP_of_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d d' : 𝓞 F} (hd : d ≠ 0)
    (hd' : d' ≠ 0) {x : 𝓞 K} {k : ℕ} (hk : vF 𝔭 d + vF 𝔭 d' ≤ k) (hx : x ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK x / (jK (ι d) * jK (ι d')) ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  have hx' : x ∈ extP K 𝔭 ^ vF 𝔭 d * extP K 𝔭 ^ vF 𝔭 d' := by
    rw [← pow_add]; exact Ideal.pow_le_pow_right hk hx
  refine Submodule.mul_induction_on hx' (fun y hy y' hy' => ?_) (fun u v hu hv => ?_)
  · rw [map_mul, mul_div_mul_comm]
    exact mul_mem ((div_mem_SP_iff h𝔭 hd _).2 hy) ((div_mem_SP_iff h𝔭 hd' _).2 hy')
  · rw [map_add, add_div]; exact add_mem hu hv

theorem div_mem_SP_of_sub {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} (hd : d ≠ 0) {z w : 𝓞 K}
    {k : ℕ} (hk : vF 𝔭 d ≤ k) (h : z - w * ι d ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK z / jK (ι d) ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  have e : jK z / jK (ι d) = jK (z - w * ι d) / jK (ι d) + jK w := by
    rw [map_sub, map_mul, sub_div, mul_div_cancel_right₀ _ (jK_ι_ne_zero hd)]; ring
  rw [e]
  exact add_mem (div_mem_SP_of_mem h𝔭 hd hk h) (HU.jK_mem_SP w)

theorem div_mul_mem_SP_of_sub {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d d' : 𝓞 F} (hd : d ≠ 0)
    (hd' : d' ≠ 0) {z w : 𝓞 K} {k : ℕ} (hk : vF 𝔭 d + vF 𝔭 d' ≤ k)
    (h : z - w * (ι d * ι d') ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK z / (jK (ι d) * jK (ι d')) ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  have e : jK z / (jK (ι d) * jK (ι d')) =
      jK (z - w * (ι d * ι d')) / (jK (ι d) * jK (ι d')) + jK w := by
    rw [map_sub, map_mul, map_mul, sub_div,
      mul_div_cancel_right₀ _ (mul_ne_zero (jK_ι_ne_zero hd) (jK_ι_ne_zero hd'))]; ring
  rw [e]
  exact add_mem (div_mul_mem_SP_of_mem h𝔭 hd hd' hk h) (HU.jK_mem_SP w)

end Formalism.L2.SG.Pf.fibreCountingData
