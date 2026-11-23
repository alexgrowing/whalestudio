import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CardQuotSmulTopCongr
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G2

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem mem_dual_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

private theorem coe_iota_eq_algebraMap_coe (a : 𝓞 F) : jK (ι a) = algebraMap F K (a : F) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]

private theorem jK_iota_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : jK (ι a) ≠ 0 := by
  rw [coe_iota_eq_algebraMap_coe]
  refine (map_ne_zero (algebraMap F K)).mpr ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha

private theorem jK_ne_zero_of_mem_closure_prime_compl {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    jK s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨t, ht, rfl⟩ := hy
    refine jK_iota_ne_zero ?_
    rintro rfl
    exact ht 𝔭.zero_mem
  | one => simp
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_ne_zero hy hz

private theorem star_jK_eq_of_mem_closure_prime_compl (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    star (jK s) = jK s := by
  induction hs using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨t, _, rfl⟩ := hy
    exact star_jK_ι hF t
  | one => simp
  | mul y z _ _ hy hz => rw [map_mul, star_mul', hy, hz]

private theorem star_mem_HU_SP (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K}
    (ha : a ∈ HU.SP K 𝔭) : star a ∈ HU.SP K 𝔭 :=
  HU.InP.conj hF ha

theorem smul_eq_jK (c : 𝓞 K) (v : V) : c • v = jK c • v := (algebraMap_smul K c v).symm

section

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
  {n : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F}

theorem h_sum (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0) (hdiag : ∀ i, h (b i) (b i) = jK (ι (a i)))
    (c : Fin n → K) (k : Fin n) : h (b k) (∑ i, c i • b i) = c k * jK (ι (a k)) := by
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · rw [hdiag]
  · intro i _ hik
    rw [horth k i (Ne.symm hik), mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem locF_le_spanK (h𝔭 : 𝔭.IsPrime) :
    locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) ≤
      (Submodule.span K (Set.range b)).restrictScalars (𝓞 K) := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hs0 : jK s ≠ 0 := jK_ne_zero_of_mem_closure_prime_compl hs
  have h1 : s • x ∈ Submodule.span K (Set.range b) :=
    Submodule.span_le_restrictScalars (𝓞 K) K _ hsx
  have h2 : (jK s)⁻¹ • (s • x) ∈ Submodule.span K (Set.range b) := Submodule.smul_mem _ _ h1
  rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul] at h2
  exact h2

variable (hbX : ∀ i, b i ∈ X) (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
  (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
include hbX hloc horth hdiag ha

theorem coords (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn X L) {x : V} (hx : x ∈ X) :
    x = ∑ i, (h (b i) x / jK (ι (a i))) • b i := by
  have hxs : x ∈ Submodule.span K (Set.range b) := by
    rw [← hL.2] at hx
    refine (Submodule.span_le.mpr ?_) hx
    intro y hy
    haveI := h𝔭
    have h1 : y ∈ locF 𝔭 L := Formalism.HermitianLattices.Ext.L3.localizedQuotients.le_locF 𝔭 L hy
    rw [← hloc] at h1
    exact locF_le_spanK h𝔭 h1
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxs
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h_sum horth (fun j => by rw [hdiag j]; exact (coe_iota_eq_algebraMap_coe (a j)).symm) c i,
    mul_div_cancel_right₀ _ (jK_iota_ne_zero (ha i))]

theorem mem_B_iff (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn X L) (x : V) :
    x ∈ locF 𝔭 L ↔ x ∈ X ∧ ∀ i, h (b i) x / jK (ι (a i)) ∈ HU.SP K 𝔭 := by
  haveI := h𝔭
  have hdiag' : ∀ i, h (b i) (b i) = jK (ι (a i)) := fun i => by
    rw [hdiag i]; exact (coe_iota_eq_algebraMap_coe (a i)).symm
  have key : ∀ w ∈ Submodule.span (𝓞 K) (Set.range b), ∀ i,
      h (b i) w / jK (ι (a i)) ∈ (1 : Submodule (𝓞 K) K) := by
    intro w hw i
    obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hw
    have e : (∑ j, z j • b j) = ∑ j, jK (z j) • b j :=
      Finset.sum_congr rfl fun j _ => smul_eq_jK _ _
    rw [e, h_sum horth hdiag' _ i, mul_div_cancel_right₀ _ (jK_iota_ne_zero (ha i))]
    exact Submodule.mem_one.mpr ⟨z i, rfl⟩
  rw [← hloc]
  constructor
  · intro hx
    have hxs := locF_le_spanK h𝔭 hx
    obtain ⟨s, hs, hsx⟩ := hx
    refine ⟨Submodule.span_le.mpr ?_ hxs, fun i => ?_⟩
    · rintro _ ⟨j, rfl⟩
      exact hbX j
    · rw [HU.mem_SP_iff_locF]
      refine Exists.intro s ⟨hs, ?_⟩
      have e : s • (h (b i) x / jK (ι (a i))) = h (b i) (s • x) / jK (ι (a i)) := by
        rw [smul_eq_jK s x, map_smul, smul_eq_mul, Algebra.smul_def, mul_div_assoc]
      rw [e]
      exact key _ hsx i
  · rintro ⟨hxX, hc⟩
    rw [coords hbX hloc horth hdiag ha h𝔭 hL hxX]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨s, hs, hsc⟩ := (HU.mem_SP_iff_locF).mp (hc i)
    obtain ⟨y, hy⟩ := Submodule.mem_one.mp hsc
    refine Exists.intro s ⟨hs, ?_⟩
    rw [← smul_assoc, ← hy, ← smul_eq_jK]
    exact Submodule.smul_mem _ y (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_locF_dualIn_iff (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) (hL : IsLatIn X L) (x : V) :
    x ∈ locF 𝔭 (dualIn h X L) ↔ x ∈ X ∧ ∀ i, h (b i) x ∈ HU.SP K 𝔭 := by
  haveI := h𝔭.isPrime
  constructor
  · intro hx
    obtain ⟨s, hs, hsx⟩ := hx
    have hs0 : jK s ≠ 0 := jK_ne_zero_of_mem_closure_prime_compl hs
    obtain ⟨hsX, hsD⟩ := Submodule.mem_inf.mp hsx
    rw [Submodule.restrictScalars_mem, smul_eq_jK] at hsX
    have hxX : x ∈ X := by
      have := X.smul_mem (jK s)⁻¹ hsX
      rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at this
    refine ⟨hxX, fun i => ?_⟩
    have hbi : b i ∈ locF 𝔭 L := by
      rw [← hloc]
      exact Formalism.HermitianLattices.Ext.L3.localizedQuotients.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨t, ht, htb⟩ := hbi
    have h1 := (mem_dual_iff h L (s • x)).mp hsD _ htb
    rw [smul_eq_jK t, smul_eq_jK s, LinearMap.map_smulₛₗ₂, map_smul, starRingEnd_apply,
      star_jK_eq_of_mem_closure_prime_compl hF ht, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← map_mul] at h1
    rw [HU.mem_SP_iff_locF]
    refine Exists.intro (t * s) ⟨Submonoid.mul_mem _ ht hs, ?_⟩
    rw [Algebra.smul_def]
    exact h1
  · rintro ⟨hxX, hq⟩
    have hgx : ∀ y ∈ L, h y x ∈ HU.SP K 𝔭 := by
      intro y hy
      have hyB : y ∈ locF 𝔭 L := Formalism.HermitianLattices.Ext.L3.localizedQuotients.le_locF 𝔭 L hy
      obtain ⟨hyX, hc⟩ := (mem_B_iff hbX hloc horth hdiag ha h𝔭.isPrime hL y).mp hyB
      rw [coords hbX hloc horth hdiag ha h𝔭.isPrime hL hyX, map_sum, LinearMap.sum_apply]
      refine Subring.sum_mem _ fun i _ => ?_
      rw [LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]
      exact Subring.mul_mem _ (star_mem_HU_SP hF (hc i)) (hq i)
    obtain ⟨S, hS⟩ := hL.1
    have hex : ∀ g : S, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z : 𝓞 K, jK z = jK (ι t) * h g x := fun g =>
      HU.mem_SP.mp (hgx g (hS ▸ Submodule.subset_span g.2))
    choose t ht z hz using hex
    have hT : (∏ g, t g) ∉ 𝔭 := by
      refine Finset.prod_induction t (fun c => c ∉ 𝔭) (fun c d hc hd hcd => ?_) ?_ fun g _ => ht g
      · exact (h𝔭.isPrime.mem_or_mem hcd).elim hc hd
      · exact (Ideal.ne_top_iff_one 𝔭).mp h𝔭.ne_top
    have hgen : ∀ g : S, h g (ι (∏ g', t g') • x) ∈ (1 : Submodule (𝓞 K) K) := by
      intro g
      classical
      rw [smul_eq_jK, map_smul, smul_eq_mul,
        ← Finset.prod_erase_mul Finset.univ t (Finset.mem_univ g), map_mul, map_mul, mul_assoc,
        ← hz g, ← map_mul]
      exact Submodule.mem_one.mpr ⟨_, rfl⟩
    have hdual : ∀ y ∈ L, h y (ι (∏ g', t g') • x) ∈ (1 : Submodule (𝓞 K) K) := by
      intro y hy
      rw [← hS] at hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hgen ⟨y, hy⟩
      | zero => simp
      | add y w _ _ hy hw =>
        rw [map_add, LinearMap.add_apply]
        exact Submodule.add_mem _ hy hw
      | smul r y _ hy =>
        obtain ⟨r', hr'⟩ := star_jK r
        rw [smul_eq_jK r, LinearMap.map_smulₛₗ₂, starRingEnd_apply, ← hr', smul_eq_mul, ← Algebra.smul_def]
        exact Submodule.smul_mem _ r' hy
    refine Exists.intro (ι (∏ g, t g)) ⟨Submonoid.subset_closure ⟨_, hT, rfl⟩, ?_⟩
    refine Submodule.mem_inf.mpr ⟨?_, (mem_dual_iff h L _).mpr hdual⟩
    rw [Submodule.restrictScalars_mem, smul_eq_jK]
    exact X.smul_mem _ hxX

end

end Formalism.L2.SG.Pf.G2
