import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DivMemLocRingOfVFEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CongrPIffInI
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsFracOfFixed

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA Formalism.HermitianLattices.Ext.L3.WCA Formalism.HermitianLattices.Ext.L3.Cell

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

private theorem vF_spec_of_ne_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) :
    a ∈ 𝔭 ^ vF 𝔭 a ∧ a ∉ 𝔭 ^ (vF 𝔭 a + 1) := by
  have hbot : ∃ N, a ∉ 𝔭 ^ N := by
    by_contra hcon
    push_neg at hcon
    have hinf : a ∈ ⨅ i, 𝔭 ^ i := Submodule.mem_iInf _ |>.mpr hcon
    rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top, Ideal.mem_bot] at hinf
    exact ha hinf
  obtain ⟨N, hN⟩ := hbot
  have hbdd : BddAbove {e : ℕ | a ∈ 𝔭 ^ e} := ⟨N, fun e he => by
    by_contra hlt
    push_neg at hlt
    exact hN (Ideal.pow_le_pow_right hlt.le he)⟩
  have hmem : a ∈ 𝔭 ^ vF 𝔭 a := Nat.sSup_mem ⟨0, by simp⟩ hbdd
  refine ⟨hmem, fun h => ?_⟩
  have hle : vF 𝔭 a + 1 ≤ vF 𝔭 a := le_csSup hbdd h
  omega

private theorem jK_iota_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : κ (ι a) ≠ 0 := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]
  refine (map_ne_zero (algebraMap F K)).mpr ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha

theorem exists_mul_eq_of_mem_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a a' : 𝓞 F}
    (ha : a ≠ 0) (ha' : a' ∈ 𝔭 ^ vF 𝔭 a) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c : 𝓞 F, t * a' = c * a := by
  obtain ⟨hmem, hnot⟩ := vF_spec_of_ne_zero h𝔭 ha
  obtain ⟨J, hJ⟩ : 𝔭 ^ vF 𝔭 a ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  have hJp : ¬ J ≤ 𝔭 := fun hle => hnot (by
    have hs : Ideal.span {a} ≤ 𝔭 ^ (vF 𝔭 a + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).mp hs)
  obtain ⟨t, htJ, htp⟩ := SetLike.not_le_iff_exists.mp hJp
  have hat : a' * t ∈ Ideal.span {a} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ha' htJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hat
  exact ⟨t, htp, c, by rw [mul_comm, hc]⟩

variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
include hK hF

theorem div_mem_locRing_of_mem_pow {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {a a' : 𝓞 F}
    (ha : a ≠ 0) (ha' : a' ∈ (P.comap ι) ^ vF (P.comap ι) a) :
    κ (ι a') / κ (ι a) ∈ locRing P := by
  have hPm : (P.comap ι).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  obtain ⟨t, ht, c, hc⟩ := exists_mul_eq_of_mem_pow hPm ha ha'
  have hκa : κ (ι a) ≠ 0 := jK_iota_ne_zero ha
  have e : κ (ι t) * (κ (ι a') / κ (ι a)) = κ (ι c) := by
    rw [← mul_div_assoc, ← map_mul, ← map_mul, hc, map_mul, map_mul, mul_div_cancel_right₀ _ hκa]
  show κ (ι a') / κ (ι a) ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
  rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
  have hfix : star (κ (ι t)) = κ (ι t) := (hF _).mpr ⟨(t : F), by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]⟩
  have hmem : ι t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
    refine Submonoid.subset_closure (And.intro ht fun t' ht' => ?_)
    rw [hfix] at ht'
    have ht'' : t' = ι t := IsFractionRing.injective (𝓞 K) K ht'
    rw [ht'']
    exact ht
  refine ⟨ι t, hmem, ?_⟩
  rw [e]
  exact Submodule.mem_one.mpr ⟨_, rfl⟩

omit hK in

theorem mul_inv_pow_mem {P : Ideal (𝓞 K)} {π : K}
    (h1 : ∀ z ∈ extP K (P.comap ι), Dv (locRing P) π (κ z)) (j : ℕ) :
    ∀ z ∈ extP K (P.comap ι) ^ j, κ z * (π ^ j)⁻¹ ∈ locRing P := by
  have hz0 : ∀ z : 𝓞 K, κ z ∈ locRing P := by
    intro z
    show κ z ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, by rw [map_one, one_mul]; exact Submodule.mem_one.mpr ⟨z, rfl⟩⟩
  induction j with
  | zero =>
    intro z _
    rw [pow_zero, inv_one, mul_one]
    exact hz0 z
  | succ j ih =>
    intro z hz
    rw [pow_succ] at hz
    refine Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun u w hu hw => ?_)
    · have hxy := (locRing P).mul_mem (ih x hx) (h1 y hy)
      rw [map_mul, pow_succ, mul_inv]
      convert hxy using 1
      ring
    · rw [map_add, add_mul]
      exact (locRing P).add_mem hu hw

theorem unifVal_at {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ π : K, IsUnif (locRing P) π ∧ ∀ a : 𝓞 F, a ≠ 0 →
      IsUnitIn (locRing P) (algebraMap F K (a : F) * (π ^ vF (P.comap ι) a)⁻¹) := by
  obtain ⟨π, hπ, h1, h2⟩ := exists_isUnif hF hP
  have hPm : (P.comap ι).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hcoe : ∀ c : 𝓞 F, algebraMap F K (c : F) = κ (ι c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]
  have hstar : ∀ c : 𝓞 F, star (κ (ι c)) = κ (ι c) := fun c => (hF _).mpr ⟨(c : F), hcoe c⟩
  have hπ0 : π ≠ 0 := hπ.3
  have hex : ∃ p0 ∈ P.comap ι, IsUnitIn (locRing P) (κ (ι p0) * π⁻¹) := by
    by_contra hne
    push_neg at hne
    have hle : extP K (P.comap ι) ≤ extP K (P.comap ι) ^ 2 := by
      show Ideal.map ι (P.comap ι) ≤ _
      refine Ideal.map_le_iff_le_comap.mpr fun p0 hp0 => ?_
      show ι p0 ∈ extP K (P.comap ι) ^ 2
      have hmemR : κ (ι p0) * π⁻¹ ∈ locRing P := h1 _ (Ideal.mem_map_of_mem _ hp0)
      have hfix : star (κ (ι p0) * π⁻¹) = κ (ι p0) * π⁻¹ := by
        rw [star_mul', star_inv₀, hπ.2, hstar]
      exact h2 _ ((hπ.4 _ hmemR hfix).resolve_left (hne p0 hp0))
    have hI0 : extP K (P.comap ι) ≠ ⊥ := by
      intro h0
      have hp0 : P.comap ι ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hPm (NumberField.RingOfIntegers.not_isField F)
      apply hp0
      rw [eq_bot_iff]
      intro c hc
      have hc' : ι c ∈ extP K (P.comap ι) := Ideal.mem_map_of_mem _ hc
      rw [h0, Ideal.mem_bot] at hc'
      have hk : algebraMap F K (c : F) = 0 := by rw [hcoe, hc', map_zero]
      rw [Ideal.mem_bot]
      exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mp
        ((map_eq_zero (algebraMap F K)).mp hk)
    have hIT : extP K (P.comap ι) ≠ ⊤ := by
      intro htop
      have hle' : extP K (P.comap ι) ≤ P := Ideal.map_comap_le
      rw [htop] at hle'
      exact hP.ne_top (top_le_iff.mp hle')
    have hsq : extP K (P.comap ι) * extP K (P.comap ι) = extP K (P.comap ι) * ⊤ := by
      rw [Ideal.mul_top]
      refine le_antisymm Ideal.mul_le_right ?_
      rw [← sq]
      exact hle
    exact hIT (mul_left_cancel₀ hI0 hsq)
  obtain ⟨p0, hp0, hu⟩ := hex
  have hu' : κ (ι p0) * π⁻¹ ≠ 0 ∧ κ (ι p0) * π⁻¹ ∈ locRing P ∧
      (κ (ι p0) * π⁻¹)⁻¹ ∈ locRing P := hu
  have hy : κ (ι p0) ≠ 0 := fun h0 => hu'.1 (by rw [h0, zero_mul])
  refine ⟨π, hπ, fun a ha => ?_⟩
  obtain ⟨hav, -⟩ := vF_spec_of_ne_zero hPm ha
  have hκa : κ (ι a) ≠ 0 := jK_iota_ne_zero ha
  rw [hcoe a]
  have hιa : ι a ∈ extP K (P.comap ι) ^ vF (P.comap ι) a := by
    show ι a ∈ (Ideal.map ι (P.comap ι)) ^ _
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hav
  have hxR : κ (ι a) * (π ^ vF (P.comap ι) a)⁻¹ ∈ locRing P :=
    mul_inv_pow_mem hF h1 _ (ι a) hιa
  have hb : p0 ^ vF (P.comap ι) a ∈ P.comap ι ^ vF (P.comap ι) a := Ideal.pow_mem_pow hp0 _
  have hdiv := div_mem_locRing_of_mem_pow hK hF hP ha hb
  have hinvR : ((κ (ι p0) * π⁻¹)⁻¹) ^ vF (P.comap ι) a ∈ locRing P :=
    (locRing P).pow_mem hu'.2.2 _
  have e : (κ (ι a) * (π ^ vF (P.comap ι) a)⁻¹)⁻¹ =
      ((κ (ι p0) * π⁻¹)⁻¹) ^ vF (P.comap ι) a * (κ (ι (p0 ^ vF (P.comap ι) a)) / κ (ι a)) := by
    rw [map_pow, map_pow, mul_inv, inv_inv, mul_inv, inv_inv, mul_pow, inv_pow, div_eq_mul_inv,
      mul_comm ((κ (ι p0) ^ vF (P.comap ι) a)⁻¹) (π ^ vF (P.comap ι) a), mul_assoc,
      ← mul_assoc ((κ (ι p0) ^ vF (P.comap ι) a)⁻¹), inv_mul_cancel₀ (pow_ne_zero _ hy), one_mul,
      mul_comm]
  refine (⟨mul_ne_zero hκa (inv_ne_zero (pow_ne_zero _ hπ0)), hxR, ?_⟩ : _ ∧ _ ∧ _)
  rw [e]
  exact (locRing P).mul_mem hinvR hdiv

end Formalism.L2.SG.Pf.TemperedBoundGL3

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

theorem uniformizer_valuation_holds : G3.UnifVal := by
  intro K F _ _ _ _ _ _ hK hF P hP
  exact unifVal_at hK hF hP

end Formalism.L2.SG.Pf.TemperedBoundGL3
