import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.IsomFixIff

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3 GluedLatticeMass OrbitSumPf

namespace GluedLatticeMass

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

theorem vF_neg (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) : vF 𝔭 (-n) = vF 𝔭 n := by
  unfold vF
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq, neg_mem_iff]

theorem vF_eq_vT {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : ℕ} (ht : 0 < t) :
    vF 𝔭 ((t : ℕ) : 𝓞 F) = vT F t 𝔭 := by
  have ht0 : ((t : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast ht.ne'
  have hI : Ideal.span {((t : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ht0
  have hne : 𝔭 ≠ ⊥ := Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.ne_bot h𝔭
  have hp : Prime 𝔭 := Ideal.prime_of_isPrime hne h𝔭.isPrime
  rw [Formalism.L2.SG.Pf.G1.vF_eq_multiplicity h𝔭 ht0, vT,
    UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors hp.irreducible hI, normalize_eq]

theorem nondeg {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} {t : ℕ} (hH : GlueHyp K F h1 z t) :
    Formalism.L2.SG.Pf.Cnt.Nondeg h1 := by
  obtain ⟨_, _, hs, hzz, ht, hd⟩ := hH
  have hz0 : h1 z z ≠ 0 := by
    rw [hzz, neg_ne_zero]
    exact_mod_cast ht.ne'
  intro x hx
  obtain ⟨c, w, rfl⟩ := (split h1 z hz0).cover x
  have hwz : h1 w.1 z = 0 := by
    rw [← hs.eq z w.1]
    have : h1 z w.1 = 0 := w.2
    rw [this, map_zero]
  have e1 := hx z
  change h1 (c • z + w.1) z = 0 at e1
  rw [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hwz, add_zero,
    smul_eq_mul] at e1
  have hc : c = 0 := by
    have h2 : (starRingEnd K) c = 0 := (mul_eq_zero.1 e1).resolve_right hz0
    simpa using h2
  subst hc
  have e2 := hx w.1
  change h1 ((0 : K) • z + w.1) w.1 = 0 at e2
  rw [zero_smul, zero_add] at e2
  by_contra hx0
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hx0
    change (0 : K) • z + ((0 : wPerp h1 z) : V1) = 0
    simp
  have hpos := hd w hw0 (Classical.arbitrary (K →+* ℂ))
  have e3 : hPerp h1 z w w = 0 := e2
  rw [e3, map_zero] at hpos
  simp at hpos

theorem isCompl_span {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} (hz0 : h1 z z ≠ 0) :
    IsCompl (Submodule.span K {z}) (wPerp h1 z) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have : h1 z (c • z) = 0 := hxw
    rw [map_smul, smul_eq_mul] at this
    rw [(mul_eq_zero.1 this).resolve_right hz0, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨c, w, rfl⟩ := (split h1 z hz0).cover x
    exact Submodule.add_mem_sup (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self z)) w.2

theorem jordan_rank_one_line {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} {t : ℕ} (hzz : h1 z z = -((t : ℕ) : K))
    (ht : 0 < t) (hz : z ≠ 0) (𝔭 : Ideal (𝓞 F)) :
    Formalism.L2.SG.Pf.Cnt.IsJordanIn h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) 𝔭
      (fun _ => z) (fun _ => -((t : ℕ) : 𝓞 F)) := by
  have h1r : finrank K (Submodule.span K {z}) = 1 := finrank_span_singleton hz
  have hne : Nonempty (Fin (finrank K (Submodule.span K {z}))) := by
    rw [h1r]
    exact ⟨0⟩
  refine ⟨fun _ => Submodule.mem_span_singleton_self z, ?_, ?_, ?_, ?_⟩
  · rw [Set.range_const]
  · intro i j hij
    exfalso
    apply hij
    apply Fin.ext
    have hi : i.val < 1 := lt_of_lt_of_eq i.2 h1r
    have hj : j.val < 1 := lt_of_lt_of_eq j.2 h1r
    omega
  · intro i
    rw [hzz]
    simp
  · intro i
    simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
    exact ht.ne'

end GluedLatticeMass

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
