import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open NumberField IsDedekindDomain

noncomputable section
open scoped Classical

namespace GlobalTheory.WeilM

variable (F : Type) [Field F] [NumberField F]

theorem thetaSum_pureA_bound {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
    ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ‖thetaSum F (pureA F f g)‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hg.2.isCompact
  haveI := discreteTopology_denomLattice F κ hN
  have hw := ZLattice.summable_norm_pow_inv (denomLattice F κ N) (Module.finrank ℤ (denomLattice F κ N) + 1)
    (Nat.lt_succ_self _)
  set k := Module.finrank ℤ (denomLattice F κ N) + 1 with hkdef
  set W := ∑' z : denomLattice F κ N, ‖z‖⁻¹ ^ k with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => by positivity
  refine ⟨{(0, 0), (k, 0)}, max B 0 * (1 + W), mul_nonneg (le_max_right _ _) (by linarith), fun f => ?_⟩
  set M := (({(0, 0), (k, 0)} : Finset (ℕ × ℕ)).sup
    (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f with hMdef
  have h00 : ∀ x, ‖f x‖ ≤ M := fun x => (SchwartzMap.norm_le_seminorm ℂ f x).trans
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)
      (i := (0, 0)) (by simp))
  have hk0 : ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ M := fun x => by
    have := SchwartzMap.le_seminorm ℂ k 0 f x
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)
      (i := (k, 0)) (by simp))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (h00 0)
  have hpt : ∀ z : denomLattice F κ N, ‖f z‖ ≤ (if z = 0 then M else 0) + ‖z‖⁻¹ ^ k * M := fun z => by
    by_cases hz : z = 0
    · subst hz; simp only [if_true]
      have := h00 0
      have h2 : 0 ≤ ‖(0 : denomLattice F κ N)‖⁻¹ ^ k * M := by positivity
      simpa using (show ‖f 0‖ ≤ M + ‖(0 : denomLattice F κ N)‖⁻¹ ^ k * M by linarith)
    · rw [if_neg hz, zero_add]
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hz0 _), mul_comm]
      exact hk0 z
  have hs1 : HasSum (fun z : denomLattice F κ N => if z = 0 then M else 0) M := by
    convert hasSum_ite_eq (0 : denomLattice F κ N) M
  have hsumL : Summable fun z : denomLattice F κ N => (if z = 0 then M else 0) + ‖z‖⁻¹ ^ k * M :=
    hs1.summable.add (hw.mul_right M)
  have hfL : Summable fun z : denomLattice F κ N => ‖f z‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumL
  have hLbound : ∑' z : denomLattice F κ N, ‖f z‖ ≤ (1 + W) * M := by
    refine (hfL.tsum_le_tsum hpt hsumL).trans (le_of_eq ?_)
    rw [hs1.summable.tsum_add (hw.mul_right M), hs1.tsum_eq, tsum_mul_right]
    ring

  have hmem : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  have hsupp : Function.support (fun ξ : κ → F => ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖)
      ⊆ S := by
    intro ξ hξ
    rw [Function.mem_support, norm_ne_zero_iff, pureA_algebraMap] at hξ
    have h0 := right_ne_zero_of_mul hξ
    show ∀ i, _
    intro i
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0) i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
    mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
  have hterm : ∀ ξ : S, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))‖ ≤
      max B 0 * ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ := fun ξ => by
    rw [pureA_algebraMap, norm_mul, mul_comm, Function.comp_apply]
    exact mul_le_mul (le_max_of_le_left (hB _)) le_rfl (norm_nonneg _) (le_max_right _ _)
  have hsumS : Summable ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) := hfL.comp_injective hj
  calc ‖thetaSum F (pureA F f g)‖
      ≤ ∑' ξ : κ → F, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_of_mem_schA F hmem)
    _ = ∑' ξ : S, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))‖ :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ ≤ ∑' ξ : S, max B 0 * ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ :=
        ((summable_norm_of_mem_schA F hmem).subtype S).tsum_le_tsum hterm (hsumS.mul_left _)
    _ = max B 0 * ∑' ξ : S, ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ := tsum_mul_left
    _ ≤ max B 0 * ∑' z : denomLattice F κ N, ‖f z‖ :=
        mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hfL (fun _ => norm_nonneg _) hj) (le_max_right _ _)
    _ ≤ max B 0 * ((1 + W) * M) := mul_le_mul_of_nonneg_left hLbound (le_max_right _ _)
    _ = max B 0 * (1 + W) * M := by ring

theorem exists_adm_eq_thetaSum_of_locallyCompact (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)]
    (κ : Type) [Fintype κ] : ∃ l : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm κ ∧
      ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ := by
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (thetaLin F κ)
  have hl' : ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ := fun Φ h => by
    have := LinearMap.congr_fun hl ⟨Φ, h⟩
    simpa using this
  refine ⟨l, fun g hg => ?_, hl'⟩
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ :=
    fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hadd : ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      pureA F (f + f') g = pureA F f g + pureA F f' g := fun f f' => by
    funext x; simp [pureA, add_mul]
  have hsmul : ∀ (a : ℂ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      pureA F (a • f) g = a • pureA F f g := fun a f => by
    funext x; simp [pureA, mul_assoc]
  let T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => thetaSum F (pureA F f g))
      (fun f f' => by rw [hadd]; exact thetaSum_add F (hmem f) (hmem f'))
      (fun a f => by rw [hsmul, thetaSum_smul]; rfl) (thetaSum_pureA_bound F hg)
  exact ⟨T, fun f => hl' _ (hmem f)⟩

end GlobalTheory.WeilM
