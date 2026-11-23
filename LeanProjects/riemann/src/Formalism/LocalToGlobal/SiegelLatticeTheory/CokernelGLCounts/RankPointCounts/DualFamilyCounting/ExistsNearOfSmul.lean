import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DivMemLocRingOfVFEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNearRepresentation
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsFracOfFixed

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA Formalism.HermitianLattices.Ext.L3.WCA Formalism.HermitianLattices.Ext.L3.Cell

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem exists_F_mul_int (hF : IsFixF K F) (z : K) :
    ∃ s : 𝓞 F, s ≠ 0 ∧ ∃ r : 𝓞 K, κ (ι s) * z = κ r := by
  obtain ⟨a, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) z
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  have hκm : κ m ≠ 0 := fun h0 =>
    hm0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))
  obtain ⟨s, hs⟩ := (conjO_eq_iff_mem_range hF (conjO K m * m)).1
    (by rw [map_mul, WA.conjO_conjO, mul_comm])
  refine ⟨s, ?_, conjO K m * a, ?_⟩
  · rintro rfl
    rw [map_zero] at hs
    rcases mul_eq_zero.1 hs.symm with h0 | h0
    · exact hm0 (by rw [← WA.conjO_conjO m, h0, map_zero])
    · exact hm0 h0
  · rw [hs, map_mul, map_mul]
    field_simp

section Near

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem exists_near_of_smul (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {n : 𝓞 F} (hn : n ≠ 0) {b : V}
    (hb : h b b = κ (ι n)) {s : 𝓞 F} (hs0 : s ≠ 0) (hsb : ι s • b ∈ A) :
    ∃ v : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ x, InL 𝔭 A 0 x → InI 𝔭 (v + k) (h x x - κ (ι n)) →
      ∃ y, InL 𝔭 A 0 y ∧ h y y = κ (ι n) ∧ InL 𝔭 A k (y - x) := by
  have hp := h𝔭.isPrime
  have hN : 4 * (s * s * n) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero hs0 hs0) hn)
  refine ⟨vF 𝔭 (4 * (s * s * n)), fun k hk x hx hε => ?_⟩
  set v := vF 𝔭 (4 * (s * s * n)) with hv
  by_cases h1 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - b) (x - b))
  · by_cases h2 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - -b) (x - -b))
    · exfalso
      apply localValuationFiltration.notMem_pow_vF h𝔭 hN
      rw [← hv, ← inI_ι (K := K) h𝔭]
      have h3 : InI 𝔭 (v + 1) (κ (ι (2 * (s * s))) * (h x x - κ (ι n))) := by
        have := InI.mul hp (InI.int hp (ι (2 * (s * s)))) (hε.mono (by omega : v + 1 ≤ v + k))
        rwa [zero_add] at this
      have e : κ (ι (4 * (s * s * n))) = κ (ι (s * s)) * h (x - b) (x - b) +
          κ (ι (s * s)) * h (x - -b) (x - -b) - κ (ι (2 * (s * s))) * (h x x - κ (ι n)) := by
        simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, hb, map_mul, map_ofNat]
        ring
      rw [e]
      exact (h1.add hp h2).sub hp h3
    · exact exists_near_representation h𝔭 hF hs hA (b := -b) (by simpa using hb)
        (by rw [smul_neg]; exact A.neg_mem hsb) hx hε h2
  · exact exists_near_representation h𝔭 hF hs hA hb hsb hx hε h1

theorem isIntegral_span {J : Type} {h : V →ₗ⋆[K] V →ₗ[K] K} (c : J → V)
    (hc : ∀ i j, h (c i) (c j) ∈ (1 : Submodule (𝓞 K) K)) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (Submodule.span (𝓞 K) (Set.range c)) := by
  have hsm : ∀ (r : 𝓞 K) (v : V), r • v = κ r • v := fun r v => (algebraMap_smul K r v).symm
  have key : ∀ i, ∀ y ∈ Submodule.span (𝓞 K) (Set.range c),
      h (c i) y ∈ (1 : Submodule (𝓞 K) K) := by
    intro i y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact hc i j
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [hsm, LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r hy
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact key i y hy
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hz
  | smul r x _ hx =>
    rw [hsm, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
      ← WA.algebraMap_conjO, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hx

end Near

section Exact

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem notMem_zero {𝔭 : Ideal (𝓞 F)} {d : 𝓞 F} (hd : d ∉ 𝔭) : d ≠ 0 :=
  fun h0 => hd (h0 ▸ Ideal.zero_mem _)

theorem exactAt_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {π : K} (hπ : IsUnif (locRing P) π) :
    G3.ExactAt (locRing P) π h := by
  intro J _ _ b e i₀ ho hu hmin ξ hξ hξu
  have hPp := hP.isPrime
  set 𝔭 := P.comap ι with h𝔭def
  have h𝔭 : 𝔭.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  have hπS : ∀ m : ℕ, π ^ m ∈ locRing P := fun m => (locRing P).pow_mem hπ.mem m
  have hnormS : ∀ (v : V) (m : ℕ), IsUnitIn (locRing P) (h v v * (π ^ m)⁻¹) →
      h v v ∈ locRing P ∧ h v v ≠ 0 := by
    intro v m hv
    have hπm : π ^ m ≠ 0 := pow_ne_zero _ hπ.ne
    refine ⟨?_, ?_⟩
    · have e1 : h v v = h v v * (π ^ m)⁻¹ * π ^ m := by field_simp
      rw [e1]
      exact (locRing P).mul_mem hv.2.1 (hπS m)
    · intro h0
      apply hv.1
      rw [h0, zero_mul]
  have hfix : ∀ v : V, star (h v v) = h v v := fun v => hs.eq v v
  have hfrac : ∀ (v : V) (m : ℕ), IsUnitIn (locRing P) (h v v * (π ^ m)⁻¹) →
      ∃ f d : 𝓞 F, d ∉ 𝔭 ∧ h v v = κ (ι f) / κ (ι d) := by
    intro v m hv
    obtain ⟨t, s, hs', he⟩ := U0.exists_frac_of_fixed hF hPp (hnormS v m hv).1 (hfix v)
    exact ⟨t, s, hs', he⟩
  choose f d hd hfd using fun i => hfrac (b i) (e i) (hu i)
  obtain ⟨n₁, d₀, hd₀, hξn⟩ := hfrac ξ (e i₀) hξu
  have hB0 := (hnormS _ _ (hu i₀)).2
  have hr : IsUnitIn (locRing P) (h ξ ξ / h (b i₀) (b i₀)) := by
    have hπm : π ^ e i₀ ≠ 0 := pow_ne_zero _ hπ.ne
    have e1 : h ξ ξ / h (b i₀) (b i₀) =
        (h ξ ξ * (π ^ e i₀)⁻¹) * (h (b i₀) (b i₀) * (π ^ e i₀)⁻¹)⁻¹ := by
      field_simp
    rw [e1]
    exact unit_mul hξu (unit_inv (hu i₀))
  obtain ⟨c, s, hs₀, hcs⟩ := U0.exists_frac_of_fixed hF hPp hr.2.1
    (by rw [star_div₀, hfix, hfix])
  have hc₀ : c ∉ 𝔭 := by
    intro hc
    have hu' := hr
    rw [hcs] at hu'
    have h1 := (WA.isUnitIn_div_iff hPp (ι c) (U0.mem_hcompl_of_notMem hF hPp hs₀)).1 hu'
    exact ((WA.mem_hcompl_iff hPp _).1 h1).1 hc
  have hcs𝔭 : c * s ∉ 𝔭 := fun hm => (hp.mem_or_mem hm).elim hc₀ hs₀
  have hD0 : κ (ι d₀) ≠ 0 := κι_ne_zero (notMem_zero hd₀)
  have hS0 : κ (ι s) ≠ 0 := κι_ne_zero (notMem_zero hs₀)
  have hE0 : κ (ι (d i₀)) ≠ 0 := κι_ne_zero (notMem_zero (hd i₀))

  let bb : J → V := fun i => κ (ι (d i)) • b i
  let A : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range bb)
  have hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A := by
    refine isIntegral_span bb fun i j => ?_
    by_cases hij : i = j
    · subst hij
      refine Submodule.mem_one.2 ⟨ι (d i * f i), ?_⟩
      show κ (ι (d i * f i)) = h (κ (ι (d i)) • b i) (κ (ι (d i)) • b i)
      have hdi : κ (ι (d i)) ≠ 0 := κι_ne_zero (notMem_zero (hd i))
      rw [h_smul_smul, hfd i, localizedQuotients.star_ι hF]
      simp only [map_mul]
      field_simp
    · show h (κ (ι (d i)) • b i) (κ (ι (d j)) • b j) ∈ _
      rw [h_smul_smul, ho i j hij, mul_zero]
      exact Submodule.zero_mem _
  have hmemS : ∀ y, InL 𝔭 A 0 y → y ∈ G3.spanS (locRing P) b := by
    rintro y ⟨t, ht, hty⟩
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hty
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hty
    have ht0 : κ (ι t) ≠ 0 := κι_ne_zero (notMem_zero ht)
    refine ⟨fun i => κ (g i * ι (d i)) / κ (ι t),
      fun i => U0.div_mem_locRing hPp _ (U0.mem_hcompl_of_notMem hF hPp ht), ?_⟩
    have e1 : y = (κ (ι t))⁻¹ • (ι t • y) := by
      rw [← algebraMap_smul K (ι t) y, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [e1, ← hg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bb]
    rw [← algebraMap_smul K (g i), smul_smul, smul_smul, map_mul]
    congr 1
    ring

  obtain ⟨β, hβ⟩ : ∃ β : V, β = κ (ι d₀) • ξ := ⟨_, rfl⟩
  have hn₁ : n₁ ≠ 0 := by
    rintro rfl
    apply (hnormS ξ _ hξu).2
    rw [hξn]
    simp
  have hβn : h β β = κ (ι (d₀ * n₁)) := by
    rw [hβ, h_smul_smul, hξn, localizedQuotients.star_ι hF]
    simp only [map_mul]
    field_simp
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hξ
  choose sj hsj0 rj hrj using fun j => exists_F_mul_int (K := K) hF (κ (ι d₀) * γ j / κ (ι (d j)))
  have hs'0 : (∏ j, sj j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hsj0 j
  have hs'β : ι (∏ j, sj j) • β ∈ A := by
    have e : ι (∏ j, sj j) • β = ∑ j, (ι (∏ k ∈ Finset.univ.erase j, sj k) * rj j) • bb j := by
      rw [← algebraMap_smul K (ι (∏ j, sj j)) β, hβ, ← hγ, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul K (ι (∏ k ∈ Finset.univ.erase j, sj k) * rj j) (bb j)]
      simp only [bb, smul_smul]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ sj (Finset.mem_univ j)]
      have hdj : κ (ι (d j)) ≠ 0 := κι_ne_zero (notMem_zero (hd j))
      have h1 := hrj j
      simp only [map_mul] at h1 ⊢
      rw [← h1]
      field_simp
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨v, hv⟩ := exists_near_of_smul h𝔭 hF hs hA
    (mul_ne_zero (notMem_zero hd₀) hn₁) hβn hs'0 hs'β

  obtain ⟨α, hα⟩ := exists_norm_congr_pow hK hF h𝔭 hcs𝔭 (show 1 ≤ v + 1 by omega)
  obtain ⟨x, hx⟩ : ∃ x : V, x = (κ (ι d₀) * κ α / κ (ι s)) • b i₀ := ⟨_, rfl⟩
  have hxL : InL 𝔭 A 0 x := by
    refine ⟨s * d i₀, fun hm => (hp.mem_or_mem hm).elim hs₀ (hd i₀), ?_⟩
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    have e : ι (s * d i₀) • x = (ι d₀ * α) • bb i₀ := by
      rw [← algebraMap_smul K (ι (s * d i₀)) x, ← algebraMap_smul K (ι d₀ * α) (bb i₀), hx]
      simp only [bb, smul_smul, map_mul]
      congr 1
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i₀, rfl⟩)
  have hF0 : κ (ι (f i₀)) = h (b i₀) (b i₀) * κ (ι (d i₀)) := by
    rw [hfd i₀]
    field_simp
  have hN1 : κ (ι n₁) = κ (ι d₀) * (κ (ι c) / κ (ι s) * h (b i₀) (b i₀)) := by
    have e2 : h ξ ξ = κ (ι c) / κ (ι s) * h (b i₀) (b i₀) := by
      have e3 := hcs
      unfold toK at e3
      rw [← e3]
      field_simp
    rw [← e2, hξn]
    field_simp
  have hε : InI 𝔭 (v + 1) (h x x - κ (ι (d₀ * n₁))) := by
    refine ⟨s * s * d i₀, fun hm => (hp.mem_or_mem hm).elim
        (fun hm' => (hp.mem_or_mem hm').elim hs₀ hs₀) (hd i₀),
      ι (d₀ * d₀ * f i₀) * (conjO K α * α - ι (c * s)), Ideal.mul_mem_left _ _ hα, ?_⟩
    rw [hx, h_smul_smul]
    simp only [map_mul, map_sub, WA.algebraMap_conjO, star_mul', star_div₀, localizedQuotients.star_ι hF, hF0, hN1]
    field_simp
  obtain ⟨y, hyL, hyy, -⟩ := hv 1 le_rfl x hxL hε
  obtain ⟨g, hg, rfl⟩ := hmemS y hyL
  have hinv : (κ (ι d₀))⁻¹ ∈ locRing P := by
    have := U0.div_mem_locRing hPp 1 (U0.mem_hcompl_of_notMem hF hPp hd₀)
    rwa [map_one, one_div] at this
  refine ⟨(κ (ι d₀))⁻¹ • ∑ i, g i • b i, ⟨fun i => (κ (ι d₀))⁻¹ * g i,
    fun i => (locRing P).mul_mem hinv (hg i), by rw [Finset.smul_sum]; simp only [smul_smul]⟩, ?_⟩
  rw [h_smul_smul, hyy, hξn, star_inv₀, localizedQuotients.star_ι hF]
  simp only [map_mul]
  field_simp

end Exact

theorem exact_vector_holds : G3.ExactVec := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs _ P hP π hπ
  exact exactAt_locRing hK hF hs hP hπ

end Formalism.L2.SG.Pf.TemperedBoundGL3
