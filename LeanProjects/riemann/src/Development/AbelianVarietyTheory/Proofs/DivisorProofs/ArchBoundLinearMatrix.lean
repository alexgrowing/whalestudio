import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.ThetaDecay

theorem piInf_algebraMap (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = archAt F w a := by
  change infEmb τ (compInf F E w (a ⊗ₜ[F] 1)) = _
  unfold compInf
  simp [archAt]

theorem linMap_archBound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ]
    (f : (κ → AF F) × (κ → AF F) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E)), ∃ K : ℝ, 0 ≤ K ∧
    ∀ (v : (κ → AF F) × (κ → AF F)) (B : ℝ), 0 ≤ B → (∀ w i, ‖archAt F w (v.1 i)‖ ≤ B ∧ ‖archAt F w (v.2 i)‖ ≤ B) →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (f v k l)‖ ≤ K * B := by
  intro F E _ _ _ _ _ n d κ _ f
  classical
  let e1 : κ → (κ → AF F) × (κ → AF F) := fun i => (Pi.single i 1, 0)
  let e2 : κ → (κ → AF F) × (κ → AF F) := fun i => (0, Pi.single i 1)
  let S : ∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin d → ℝ := fun w τ k l =>
    ∑ i, (‖piInf τ (f (e1 i) k l)‖ + ‖piInf τ (f (e2 i) k l)‖)
  have hS : ∀ w τ k l, 0 ≤ S w τ k l := fun w τ k l =>
    Finset.sum_nonneg fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨∑ w, ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l,
    Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun l _ => hS w τ k l, ?_⟩
  intro v B hB hv w τ k l
  have hvdec : v = ∑ i, (v.1 i • e1 i + v.2 i • e2 i) := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      simp [e1, e2, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hfv : f v k l = ∑ i, (algebraMap (AF F) (AE F E) (v.1 i) * f (e1 i) k l +
      algebraMap (AF F) (AE F E) (v.2 i) * f (e2 i) k l) := by
    conv_lhs => rw [hvdec]
    simp only [map_sum, map_add, LinearMap.map_smul, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]
    simp only [Algebra.smul_def]
  have h1 : ‖piInf τ (f v k l)‖ ≤ B * S w τ k l := by
    rw [hfv, map_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_add, map_mul, map_mul, piInf_algebraMap, piInf_algebraMap, mul_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
    · exact mul_le_mul_of_nonneg_right (hv w i).1 (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_right (hv w i).2 (norm_nonneg _)
  have h2 : S w τ k l ≤ ∑ w, ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l)
      (fun w _ => Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hS w τ k l)
      (Finset.mem_univ w))
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ k, ∑ l, S w τ k l)
      (fun τ _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hS w τ k l) (Finset.mem_univ τ))
    refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ l, S w τ k l)
      (fun k _ => Finset.sum_nonneg fun l _ => hS w τ k l) (Finset.mem_univ k))
    exact Finset.single_le_sum (f := fun l => S w τ k l) (fun l _ => hS w τ k l) (Finset.mem_univ l)
  calc ‖piInf τ (f v k l)‖ ≤ B * S w τ k l := h1
    _ ≤ B * ∑ w, ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l := mul_le_mul_of_nonneg_left h2 hB
    _ = _ := mul_comm _ _

end GlobalTheory.ThetaDecay
end
