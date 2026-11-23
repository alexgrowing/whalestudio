import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

theorem summable_lat_wt {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] {k : ℕ} (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def sz {κ : Type} [Fintype κ] (y : κ → AF F) : ℝ := 1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j))

theorem norm_le_sz {κ : Type} [Fintype κ] (y : κ → AF F) : 1 + ‖fun j => evI F (y j)‖ ≤ sz y := by
  have h0 : ∀ j, 0 ≤ ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j)) := fun j =>
    Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg _ _
  refine add_le_add_right ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => h0 j)).2 fun j => ?_) 1
  refine le_trans ?_ (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ j))
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.sup'_le _ _ fun w _ => Finset.single_le_sum (f := fun w => mixedEmbedding.normAtPlace w (evI F (y j)))
    (fun w _ => mixedEmbedding.normAtPlace_nonneg _ _) (Finset.mem_univ w)

theorem sz_pos {κ : Type} [Fintype κ] (y : κ → AF F) : 0 < sz y := lt_of_lt_of_le (by positivity) (norm_le_sz y)

theorem summable_wt {κ : Type} [Fintype κ] {C : Set (κ → Af F)} (hC : IsCompact C) : ∃ N : ℕ, Summable fun ξ : κ → F =>
    if (fun j => (algebraMap F (AF F) (ξ j)).2) ∈ C then (sz (fun j => algebraMap F (AF F) (ξ j)) ^ N)⁻¹ else 0 := by
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hC
  haveI := discreteTopology_denomLattice F κ hN
  refine ⟨Module.finrank ℤ (denomLattice F κ N) + 1, ?_⟩
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
  · intro ξ hξ
    refine if_neg fun h0 => hξ ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ h0 i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  · let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    refine Summable.of_nonneg_of_le (fun ξ => ?_) (fun ξ => ?_)
      ((summable_lat_wt (denomLattice F κ N) (Nat.lt_succ_self _)).comp_injective hj)
    · simp only [Function.comp_apply]
      split_ifs
      · exact inv_nonneg.2 (pow_pos (sz_pos _) _).le
      · exact le_rfl
    · simp only [Function.comp_apply]
      split_ifs
      · rw [inv_pow]
        refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ _)
        have h := norm_le_sz (fun i => algebraMap F (AF F) (ξ.1 i))
        have e : (fun i => evI F (algebraMap F (AF F) (ξ.1 i))) = fun i => mixedEmbedding F (ξ.1 i) :=
          funext fun i => (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
        rw [e] at h
        exact h
      · positivity

variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
  {I : Set (Ten F E n d)} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u z : Fin m → Matrix (Fin n) (Fin d) E}

theorem slice_bound (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {l} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Af F)) :
    ∃ (wt : (Fin m → F) → ℝ) (P : SInf F (Fin n × Fin d) → ℝ), Summable wt ∧ Continuous P ∧ P 0 = 0 ∧
      ∀ y (f : SInf F (Fin n × Fin d)),
        ‖l (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) (pureA F f φ)))‖ ≤ P f * wt y := by
  obtain ⟨r, φ₁, C, A, h1, hC, -, h2, h3, h4⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hD φ hφ
  obtain ⟨N, hN⟩ := summable_wt hC
  choose T hT using fun i => hl (φ₁ i) (h1 i)
  choose p hp hq using fun i => h4 ((normSeminorm ℂ ℂ).comp (T i).toLinearMap) N (T i).continuous.norm
  refine ⟨_, fun f => ∑ i, p i f, hN, continuous_finset_sum _ fun i _ => hp i, by simp, fun y f => ?_⟩
  rw [h2, map_sum]
  simp only [hT]
  split_ifs with hy
  · rw [Finset.sum_mul]
    refine norm_sum_le_of_le _ fun i _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (sz_pos _) _)]
    exact hq i i _ f
  · simp [h3 _ _ hy]

end PositivityTheory.ThKCT
