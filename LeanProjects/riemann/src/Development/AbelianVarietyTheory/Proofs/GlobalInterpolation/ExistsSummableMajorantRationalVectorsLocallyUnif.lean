import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.SumMaj
open scoped Classical
variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem re_add (x y : Ainf F) (w : InfinitePlace F) : re (x + y) w = re x w + re y w := by
  show (InfinitePlace.Completion.extensionEmbedding w (x w + y w)).re = _
  rw [map_add, Complex.add_re]; rfl

theorem abs_re_algebraMap (hF : IsTotallyReal F) (x : F) (w : InfinitePlace F) :
    |re (algebraMap F (Ainf F) x) w| = w x := by
  unfold re
  have hw : w.IsReal := hF.isReal w
  rw [InfiniteAdeleRing.algebraMap_apply]
  rw [InfinitePlace.Completion.extensionEmbedding_coe]
  rw [← InfinitePlace.embedding_of_isReal_apply hw, Complex.ofReal_re]
  first
  | (rw [← Real.norm_eq_abs]; exact InfinitePlace.norm_embedding_of_isReal hw x)
  | simpa [Real.norm_eq_abs] using InfinitePlace.norm_embedding_of_isReal hw x

theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sz_sub_le (u y : Fin N → AF F) : sz u - sz y ≤ sz (u + y) := by
  unfold sz
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  have h : re (inf (u + y) l) w = re (inf u l) w + re (inf y l) w := by
    rw [← re_add]; congr 1
  rw [h]
  have := abs_sub_abs_le_abs_sub (re (inf u l) w) (-(re (inf y l) w))
  simpa [abs_neg, sub_neg_eq_add] using this

theorem continuous_sz : Continuous (sz : (Fin N → AF F) → ℝ) := by
  unfold sz
  refine continuous_finset_sum _ fun l _ => continuous_finset_sum _ fun w _ => ?_
  have h1 : Continuous fun u : Fin N → AF F => inf u l := by
    show Continuous fun u : Fin N → AF F => (u l).1
    exact continuous_fst.comp (continuous_apply l)
  have h2 : Continuous fun x : Ainf F => re x w :=
    Complex.continuous_re.comp ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      (continuous_apply w))
  exact continuous_abs.comp (h2.comp h1)

theorem continuous_fin : Continuous (fin : (Fin N → AF F) → Fin N → Af F) := by
  refine continuous_pi fun l => ?_
  show Continuous fun u : Fin N → AF F => (u l).2
  exact continuous_snd.comp (continuous_apply l)

theorem fin_add (u y : Fin N → AF F) : fin (u + y) = fin u + fin y := by
  funext l; simp [fin, map_add]

theorem inf_rat (ξ : Fin N → F) (l : Fin N) : inf (rat ξ) l = algebraMap F (Ainf F) (ξ l) := by
  simp [inf, rat]

theorem fin_rat (ξ : Fin N → F) (l : Fin N) : fin (rat ξ) l = algebraMap F (Af F) (ξ l) := by
  simp [fin, rat]

theorem norm_le_sz (hF : IsTotallyReal F) (ξ : Fin N → F) :
    ‖(fun l => mixedEmbedding F (ξ l))‖ ≤ sz (rat ξ) := by
  refine (pi_norm_le_iff_of_nonneg (sz_nonneg _)).2 fun l => ?_
  classical
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply]
  unfold sz
  calc w (ξ l) = |re (inf (rat ξ) l) w| := by rw [inf_rat, abs_re_algebraMap hF]
    _ ≤ ∑ w', |re (inf (rat ξ) l) w'| :=
        Finset.single_le_sum (f := fun w' => |re (inf (rat ξ) l) w'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ w)
    _ ≤ _ := Finset.single_le_sum (f := fun l' => ∑ w', |re (inf (rat ξ) l') w'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)

theorem finrank_le_of_discrete {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] : Module.finrank ℤ L ≤ Module.finrank ℝ E := by
  let E' := Submodule.span ℝ (L : Set E)
  let L' : Submodule ℤ E' := ZLattice.comap ℝ L E'.subtype
  haveI : DiscreteTopology L' :=
    ZLattice.comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
  haveI : IsZLattice ℝ L' :=
    ⟨Submodule.map_injective_of_injective E'.subtype_injective (by simp [E', L'])⟩
  let e : L' ≃ₗ[ℤ] L := Submodule.comapSubtypeEquivOfLe (p := L) (q := E'.restrictScalars ℤ)
    Submodule.subset_span
  rw [← e.finrank_eq, ZLattice.rank ℝ L']
  exact Submodule.finrank_le E'

end GlobalTheory.SumMaj

namespace GlobalTheory.SumMaj
open scoped Classical

theorem summable_majorant : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ K : Set (Fin N → Af F), IsCompact K → ∃ k : ℕ, ∀ ω : Set (Fin N → AF F), IsCompact ω →
      ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧
        ∀ ξ, ∀ y ∈ ω, fin (rat ξ + y) ∈ K → 1 ≤ c ξ * (1 + sz (rat ξ + y)) ^ k := by
  intro F _ _ N hF K hK
  refine ⟨Module.finrank ℝ (Fin N → mixedEmbedding.mixedSpace F) + 1, fun ω hω => ?_⟩
  set k := Module.finrank ℝ (Fin N → mixedEmbedding.mixedSpace F) + 1 with hk
  obtain ⟨B, hB⟩ := hω.bddAbove_image (continuous_sz (F := F) (N := N)).continuousOn
  set B0 := max B 0 with hB0
  have hB0n : 0 ≤ B0 := le_max_right _ _
  have hszB : ∀ y ∈ ω, sz y ≤ B0 := fun y hy => (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  set K' : Set (Fin N → Af F) := (fun p : (Fin N → Af F) × (Fin N → Af F) => p.1 - p.2) '' (K ×ˢ (fin '' ω))
    with hK'
  have hK'c : IsCompact K' :=
    (hK.prod (hω.image continuous_fin)).image (continuous_fst.sub continuous_snd)
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hK'c
  set S : Set (Fin N → F) := {ξ | fin (rat ξ) ∈ K'} with hS
  set c : (Fin N → F) → ℝ := S.indicator fun ξ => (1 + B0) ^ k / (1 + sz (rat ξ)) ^ k with hc
  have hc0 : ∀ ξ, 0 ≤ c ξ := fun ξ =>
    Set.indicator_nonneg (fun ξ _ => div_nonneg (pow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [sz_nonneg (rat ξ)]) _)) ξ
  refine ⟨c, ?_, hc0, fun ξ y hy hξ => ?_⟩
  · haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F (Fin N) hM0
    set L := GlobalTheory.WeilM.denomLattice F (Fin N) M with hL
    have memL : ∀ ξ ∈ S, (fun i => mixedEmbedding F (ξ i)) ∈ L := by
      intro ξ hξ i
      obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((M : F) * ξ i)
        fun v => by
          rw [map_mul, map_natCast]
          have := hM _ hξ i v
          rwa [fin_rat] at this
      refine ⟨y, ?_⟩
      have h2 := congrArg (mixedEmbedding F) hy
      rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
      exact h2.symm
    let j : S → L := fun ξ => ⟨_, memL ξ.1 ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    have hkL : Module.finrank ℤ L < k := Nat.lt_succ_of_le (finrank_le_of_discrete L)
    have hg : Summable fun z : L => ((1 + ‖z‖) ^ k)⁻¹ := by
      refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L k hkL) ?_
      refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
      by_contra h0
      apply hz
      show ‖((1 + ‖z‖) ^ k)⁻¹‖ ≤ ‖z‖⁻¹ ^ k
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
      rw [Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg (by positivity) _)), inv_pow]
      exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)
    refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
    · intro ξ hξ
      have : ξ ∉ S := fun h => hξ ⟨⟨ξ, h⟩, rfl⟩
      exact Set.indicator_of_notMem this _
    · refine Summable.of_nonneg_of_le (fun ξ => hc0 _) (fun ξ => ?_) ((hg.comp_injective hj).mul_left ((1 + B0) ^ k))
      show c ξ.1 ≤ (1 + B0) ^ k * ((1 + ‖j ξ‖) ^ k)⁻¹
      rw [hc, Set.indicator_of_mem ξ.2, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)
      have hn : ‖j ξ‖ ≤ sz (rat ξ.1) := norm_le_sz hF ξ.1
      exact inv_anti₀ (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) (by linarith) _)
  · have hS' : ξ ∈ S := by
      refine ⟨(fin (rat ξ + y), fin y), ⟨hξ, y, hy, rfl⟩, ?_⟩
      simp [fin_add]
    rw [hc, Set.indicator_of_mem hS']
    have hs0 := sz_nonneg (rat ξ)
    have ht0 := sz_nonneg (rat ξ + y)
    have hst := sz_sub_le (rat ξ) y
    have hy0 := hszB y hy
    have key : 1 + sz (rat ξ) ≤ (1 + B0) * (1 + sz (rat ξ + y)) := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos (by linarith) _), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) key _

end GlobalTheory.SumMaj
