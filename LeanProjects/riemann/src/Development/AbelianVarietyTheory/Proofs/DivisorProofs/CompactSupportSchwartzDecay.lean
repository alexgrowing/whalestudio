import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.TateConvBasis

theorem norm_le_evI {F : Type} [Field F] [NumberField F] (c : AF F) (v : InfinitePlace F) :
    ‖evInf F v c‖ ≤ ‖evI F c‖ := by
  change ‖c.1 v‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F c.1‖
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.norm_def]
  rcases v.isReal_or_isComplex with hv | hv
  · refine le_trans ?_ (le_max_left _ _)
    refine le_trans (le_of_eq ?_) (norm_le_pi_norm (fun (w : {w : InfinitePlace F // w.IsReal}) =>
      InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (c.1 w)) ⟨v, hv⟩)
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) _).symm
  · refine le_trans ?_ (le_max_right _ _)
    refine le_trans (le_of_eq ?_) (norm_le_pi_norm (fun (w : {w : InfinitePlace F // w.IsComplex}) =>
      InfinitePlace.Completion.extensionEmbedding w.1 (c.1 w)) ⟨v, hv⟩)
    exact ((InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) _).symm

theorem crd_eq_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (b₀ : Module.Basis (Fin m) F E) (x : AE F E) (j : Fin (Module.finrank F E)) :
    GlobalTheory.XTermMaj.crd F E x j = ∑ i, algebraMap F (AF F) ((Module.finBasis F E).repr (b₀ i) j) *
      (Algebra.TensorProduct.basis (AF F) b₀).equivFun x i := by
  have hlin : ∀ y, GlobalTheory.XTermMaj.crd F E y =
      (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun y := fun _ => rfl
  have h1 : ∀ i, (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun ((1 : AF F) ⊗ₜ[F] b₀ i) j =
      algebraMap F (AF F) ((Module.finBasis F E).repr (b₀ i) j) := by
    intro i
    rw [Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul]
    simp
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) b₀).sum_equivFun x, hlin]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.basis_apply, h1, mul_comm]

end GlobalTheory.TateConvBasis

namespace GlobalTheory.TateConvBasis

theorem integrable_norm_mul_absE_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m : ℕ) (b₀ : Module.Basis (Fin m) F E) (g : AE F E → ℂ), Continuous g →
    (∃ K : Set (Fin m → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧ ∀ a, (fun i => ((Algebra.TensorProduct.basis (AF F) b₀).equivFun a i).2) ∉ K → g a = 0) →
    (∀ N : ℕ, ∃ C : ℝ, ∀ a, ‖g a‖ * (1 + ‖fun i => evI F ((Algebra.TensorProduct.basis (AF F) b₀).equivFun a i)‖) ^ N ≤ C) →
    ∀ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure → ∀ z : ℕ, 2 ≤ z → Integrable (fun l : (AE F E)ˣ => ‖g l.1‖ * (absE F E l : ℝ) ^ z) μ := by
  intro F E _ _ _ _ _ m b₀ g hg ⟨K, hK, hK0⟩ hdec μ hμ z hz
  haveI := hμ
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  have hs : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (show 1 < z by omega)

  set P : Fin (Module.finrank F E) → Fin m → F := fun j i => (Module.finBasis F E).repr (b₀ i) j with hP
  set U : Set (Fin (Module.finrank F E) → Af F) :=
    (fun c : Fin m → Af F => fun j => ∑ i, algebraMap F (Af F) (P j i) * c i) '' K with hUdef
  have hU : IsCompact U := hK.image (continuous_pi fun j =>
    continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i))
  have hfin : ∀ x : AE F E, (fun i => ((Algebra.TensorProduct.basis (AF F) b₀).equivFun x i).2) ∈ K →
      (fun j => (GlobalTheory.XTermMaj.crd F E x j).2) ∈ U := by
    intro x hx
    refine ⟨_, hx, funext fun j => ?_⟩
    change _ = sndA F (GlobalTheory.XTermMaj.crd F E x j)
    rw [crd_eq_sum b₀, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, AlgHom.commutes]
    rfl
  set A : ℝ := ∑ j, ∑ v : InfinitePlace F, ∑ i, ‖evInf F v (algebraMap F (AF F) (P j i))‖ with hA
  have hA0 : 0 ≤ A := by positivity
  have hB : ∀ x : AE F E, ∑ j, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E x j).1 v‖ ≤
      A * ‖fun i => evI F ((Algebra.TensorProduct.basis (AF F) b₀).equivFun x i)‖ := by
    intro x
    have hT : ∀ i v, ‖evInf F v ((Algebra.TensorProduct.basis (AF F) b₀).equivFun x i)‖ ≤
        ‖fun i => evI F ((Algebra.TensorProduct.basis (AF F) b₀).equivFun x i)‖ := fun i v =>
      (norm_le_evI _ v).trans (norm_le_pi_norm (fun i => evI F ((Algebra.TensorProduct.basis (AF F) b₀).equivFun x i)) i)
    have e : ∀ j v, ‖(GlobalTheory.XTermMaj.crd F E x j).1 v‖ ≤ ∑ i, ‖evInf F v (algebraMap F (AF F) (P j i))‖ *
        ‖fun i => evI F ((Algebra.TensorProduct.basis (AF F) b₀).equivFun x i)‖ := by
      intro j v
      change ‖evInf F v (GlobalTheory.XTermMaj.crd F E x j)‖ ≤ _
      rw [crd_eq_sum b₀, map_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [map_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hT i v) (norm_nonneg _)
    calc _ ≤ ∑ j, ∑ v : InfinitePlace F, ∑ i, ‖evInf F v (algebraMap F (AF F) (P j i))‖ *
          ‖fun i => evI F ((Algebra.TensorProduct.basis (AF F) b₀).equivFun x i)‖ :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun v _ => e j v
      _ = _ := by simp only [hA, Finset.sum_mul]

  obtain ⟨N, k, L, C₀, hk, hb⟩ := GlobalTheory.TateConv.bound F E hs hU
  obtain ⟨C, hC⟩ := hdec N
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hpt : ∀ l : (AE F E)ˣ, ENNReal.ofReal (‖g l.1‖ * (absE F E l : ℝ) ^ z) ≤
      ENNReal.ofReal (C * (1 + A) ^ N) *
        (GlobalTheory.XTermMaj.maj F E N U (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ (z : ℝ))) := by
    intro l
    rw [Real.rpow_natCast]
    by_cases hx : (fun i => ((Algebra.TensorProduct.basis (AF F) b₀).equivFun (l : AE F E) i).2) ∈ K
    · rw [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem (hfin _ hx), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      set S := ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖
      set T := ‖fun i => evI F ((Algebra.TensorProduct.basis (AF F) b₀).equivFun (l : AE F E) i)‖
      have hS0 : 0 ≤ S := by positivity
      have hT0 : 0 ≤ T := norm_nonneg _
      have hST : 1 + S ≤ (1 + A) * (1 + T) := by nlinarith [hB (l : AE F E)]
      have hg1 : ‖g (l : AE F E)‖ * (1 + S) ^ N ≤ C * (1 + A) ^ N := by
        calc ‖g (l : AE F E)‖ * (1 + S) ^ N ≤ ‖g (l : AE F E)‖ * ((1 + A) ^ N * (1 + T) ^ N) := by
              rw [← mul_pow]; gcongr
          _ = (‖g (l : AE F E)‖ * (1 + T) ^ N) * (1 + A) ^ N := by ring
          _ ≤ C * (1 + A) ^ N := by gcongr; exact hC _
      have hg2 : ‖g (l : AE F E)‖ ≤ C * (1 + A) ^ N * (1 + S) ^ (-(N : ℝ)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        exact hg1
      calc ‖g (l : AE F E)‖ * (absE F E l : ℝ) ^ z ≤ C * (1 + A) ^ N * (1 + S) ^ (-(N : ℝ)) * (absE F E l : ℝ) ^ z := by
            gcongr
        _ = _ := by ring
    · rw [hK0 _ hx, norm_zero, zero_mul, ENNReal.ofReal_zero]
      exact zero_le
  have h2 : ∫⁻ l, GlobalTheory.XTermMaj.maj F E N U (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ (z : ℝ)) ∂μ < ⊤ :=
    (lintegral_mono hb).trans_lt (GlobalTheory.TateConv.lintegral_bound_lt_top F E μ hs hk L C₀)
  have hlt : ∫⁻ l, ENNReal.ofReal (‖g l.1‖ * (absE F E l : ℝ) ^ z) ∂μ < ⊤ := by
    refine (lintegral_mono hpt).trans_lt ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2
  have hcont : Continuous (fun l : (AE F E)ˣ => ‖g l.1‖ * (absE F E l : ℝ) ^ z) :=
    (continuous_norm.comp (hg.comp Units.continuous_val)).mul
      ((NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).pow z)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun l => by positivity)]
  exact hlt

end GlobalTheory.TateConvBasis

end
