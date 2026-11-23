import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionOfCoordinateDivisibility

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.ZH GlobalTheory.ZH.RatModel

namespace PositivityTheory.UnitarySelfGeneration.UnitProductCombination

section Gen

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z}

theorem valF_compat (u : H.Sec) {i j : H.ι} (h : ((H.U i ⊓ H.U j : M.Z.Opens) : Set M.Z).Nonempty) :
    valF M.pt (H.U i) (u.f i) = valF M.pt (H.U i ⊓ H.U j) (H.g i j).val * valF M.pt (H.U j) (u.f j) := by
  have e := congrArg (M.res _ h) (u.compat i j)
  rw [map_mul, M.res_apply, M.res_apply, M.res_apply] at e
  exact (M.valF_resG inf_le_left h _).symm.trans (e.trans (congrArg _ (M.valF_resG inf_le_right h _)))

theorem valF_unit_ne_zero {U : M.Z.Opens} (h : (U : Set M.Z).Nonempty) (u : Γ(M.Z, U)ˣ) : valF M.pt U u.val ≠ 0 := by
  rw [← M.res_apply U h]
  exact (u.isUnit.map (M.res U h)).ne_zero

theorem exists_genTriv {W : Type} (s : W → H.Sec) (t : W → Ω)
    (hr : ∀ w w' i, (H.U i : Set M.Z).Nonempty →
      t w * valF M.pt (H.U i) ((s w').f i) = t w' * valF M.pt (H.U i) ((s w).f i))
    (hb : ⨆ w, nonzeroLocus (s w) = ⊤) (ht : ∃ w, t w ≠ 0) :
    ∃ e : H.ι → Ω, M.GenTriv H e ∧ ∀ w, M.HasVal e (s w) (t w) := by
  classical
  have hm : genericPoint M.Z ∈ ⨆ w, nonzeroLocus (s w) := by rw [hb]; trivial
  obtain ⟨w₀, hk⟩ := Opens.mem_iSup.1 hm
  obtain ⟨l, hl⟩ := Opens.mem_iSup.1 hk
  have hzl : genericPoint M.Z ∈ H.U l := M.Z.basicOpen_le _ hl
  have h0 : valF M.pt (H.U l) ((s w₀).f l) ≠ 0 := ((isUnit_O_iff _).1 ((isUnit_valF_iff hzl _).2 hl)).1
  have h1 : ∀ i, (H.U i : Set M.Z).Nonempty → valF M.pt (H.U i) ((s w₀).f i) ≠ 0 := fun i hi => by
    have h := M.nonempty_inf hi ⟨_, hzl⟩
    rw [valF_compat (s w₀) h]
    exact mul_ne_zero (valF_unit_ne_zero h _) h0
  have ht0 : t w₀ ≠ 0 := fun h => by
    obtain ⟨w, hw⟩ := ht
    have := hr w w₀ l ⟨_, hzl⟩
    rw [h, zero_mul] at this
    exact mul_ne_zero hw h0 this
  refine ⟨fun i => if (H.U i : Set M.Z).Nonempty then t w₀ / valF M.pt (H.U i) ((s w₀).f i) else 1,
    ⟨fun i => ?_, fun i j h => ?_⟩, fun w i hi => ?_⟩
  · split_ifs with hi
    · exact div_ne_zero ht0 (h1 i hi)
    · exact one_ne_zero
  · have hi : (H.U i : Set M.Z).Nonempty := h.mono fun _ hz => hz.1
    have hj : (H.U j : Set M.Z).Nonempty := h.mono fun _ hz => hz.2
    rw [if_pos hi, if_pos hj, valF_compat (s w₀) h]
    have := h1 j hj
    have := valF_unit_ne_zero h (H.g i j)
    field_simp
  · simp only [if_pos hi]
    have := h1 i hi
    have e := hr w w₀ i hi
    field_simp
    linear_combination -e

theorem exists_unit {e : H.ι → Ω} (he : M.GenTriv H e) {J : Type}
    {s : J → H.Sec} {t : J → Ω} (hv : ∀ k, M.HasVal e (s k) (t k)) (hs : ⨆ k, nonzeroLocus (s k) = ⊤)
    (i : H.ι) (z : M.Z) (hz : z ∈ H.U i) : ∃ k, t k ≠ 0 ∧ e i / t k ∈ M.O z := by
  have hm : z ∈ ⨆ k, nonzeroLocus (s k) := by rw [hs]; trivial
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hm
  obtain ⟨l, hl⟩ := Opens.mem_iSup.1 hk
  have hzl : z ∈ H.U l := M.Z.basicOpen_le _ hl
  obtain ⟨h0, h1⟩ := (isUnit_O_iff _).1 ((isUnit_valF_iff hzl _).2 hl)
  have e0 := hv k l ⟨z, hzl⟩
  dsimp only at h0 h1
  rw [e0] at h0 h1
  have hi : t k ≠ 0 := fun h => h0 (by rw [h, zero_div])
  refine ⟨k, hi, ?_⟩
  have h2 := valF_mem_O (show z ∈ H.U l ⊓ H.U i from ⟨hzl, hz⟩) (H.g l i).val
  rw [he.g_eq l i ⟨z, hzl, hz⟩] at h2
  have h3 := mul_mem h2 h1
  have := he.ne l
  have e' : e i / e l * (t k / e l)⁻¹ = e i / t k := by field_simp
  rwa [e'] at h3

theorem hasDiv (hH : H.IsLB) {e : H.ι → Ω} (he : M.GenTriv H e) {J : Type}
    {s : J → H.Sec} {t : J → Ω} (hv : ∀ k, M.HasVal e (s k) (t k)) (hs : ⨆ k, nonzeroLocus (s k) = ⊤) :
    M.HasDiv t := fun z => by
  have hm : z ∈ ⨆ k, nonzeroLocus (s k) := by rw [hs]; trivial
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hm
  exact ⟨k, (mem_nonzeroLocus_iff_div hH he hv (exists_unit he hv hs) k z).1 hk⟩

theorem nonzero_of_comb {e : H.ι → Ω} {J : Type} {s : J → H.Sec} {t : J → Ω} (hv : ∀ k, M.HasVal e (s k) (t k))
    (hs : ⨆ k, nonzeroLocus (s k) = ⊤) {n : ℕ} (γ : Fin n → J)
    (hc : ∀ j, ∃ a : Fin n → o, t j = ∑ k, algebraMap o Ω (a k) * t (γ k)) :
    ⨆ k, nonzeroLocus (s (γ k)) = ⊤ := top_unique fun z _ => by
  have hm : z ∈ ⨆ k, nonzeroLocus (s k) := by rw [hs]; trivial
  obtain ⟨j, hk⟩ := Opens.mem_iSup.1 hm
  obtain ⟨l, hl⟩ := Opens.mem_iSup.1 hk
  have hzl : z ∈ H.U l := M.Z.basicOpen_le _ hl
  have hu := (isUnit_valF_iff hzl _).2 hl
  obtain ⟨a, ha⟩ := hc j
  have e0 : (⟨valF M.pt (H.U l) ((s j).f l), valF_mem_O hzl _⟩ : M.O z) =
      ∑ k, algebraMap o (M.O z) (a k) * ⟨valF M.pt (H.U l) ((s (γ k)).f l), valF_mem_O hzl _⟩ := by
    refine Subtype.ext ?_
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [MulMemClass.coe_mul, SubalgebraClass.coe_algebraMap, hv _ l ⟨z, hzl⟩]
    rw [ha, Finset.sum_div]
    simp only [mul_div_assoc]
  rw [e0] at hu
  obtain ⟨k, -, hk⟩ := IsLocalRing.exists_of_isUnit_sum hu
  exact Opens.mem_iSup.2 ⟨k, Opens.mem_iSup.2 ⟨l, (isUnit_valF_iff hzl _).1 (isUnit_of_mul_isUnit_right hk)⟩⟩

end Gen

theorem gen_all {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (M : RatModel (𝓞 K) Ω) (H : LB M.Z) (hH : H.IsLB)
    (ev : V →ₗ[K] Ω) (W : Submodule (𝓞 K) V) (s : W → H.Sec)
    (hr : ∀ (w w' : W) i, (H.U i : Set M.Z).Nonempty →
      ev w * valF M.pt (H.U i) ((s w').f i) = ev w' * valF M.pt (H.U i) ((s w).f i))
    (hb : ⨆ w, nonzeroLocus (s w) = ⊤) (hev : ev ≠ 0) (hW : Submodule.span K (W : Set V) = ⊤)
    {n : ℕ} (gw : Fin n → W) (hg : Submodule.span (𝓞 K) (Set.range fun k => (gw k : V)) = W) :
    ∃ e : H.ι → Ω, M.GenTriv H e ∧ (∀ w : W, M.HasVal e (s w) (ev w)) ∧ ⨆ k, nonzeroLocus (s (gw k)) = ⊤ ∧
      M.HasDiv fun k => ev (gw k) := by
  have ht : ∃ w : W, ev w ≠ 0 := by
    by_contra h
    refine hev (LinearMap.ext_on hW fun v hv => ?_)
    by_contra h'
    exact h ⟨⟨v, hv⟩, h'⟩
  obtain ⟨e, he, hv⟩ := exists_genTriv s (fun w : W => ev w) hr hb ht
  have hs := nonzero_of_comb hv hb gw fun w => by
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hg.ge w.2)
    refine ⟨a, ?_⟩
    rw [← ha, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul K (a k), map_smul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  exact ⟨e, he, hv, hs, hasDiv hH he (fun k => hv (gw k)) hs⟩

end PositivityTheory.UnitarySelfGeneration.UnitProductCombination
