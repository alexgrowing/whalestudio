import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleCompareStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ConeMaj

open GroundTheory.Global GroundTheory.Global.IdeleGroup

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def archSize (x : AE F E) : ℝ := ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E x i).1 v‖

def finCrd (x : AE F E) : Fin (Module.finrank F E) → Af F := fun i => (GlobalTheory.XTermMaj.crd F E x i).2

theorem continuous_crd : Continuous (GlobalTheory.XTermMaj.crd F E) := by
  unfold GlobalTheory.XTermMaj.crd
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun.toLinearMap

theorem continuous_archSize : Continuous (archSize F E) := by
  unfold archSize
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun v _ => ?_
  exact ((continuous_apply v).comp (continuous_fst.comp ((continuous_apply i).comp (continuous_crd F E)))).norm

theorem continuous_finCrd : Continuous (finCrd F E) :=
  continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_crd F E))

theorem archSize_nonneg (x : AE F E) : 0 ≤ archSize F E x := by unfold archSize; positivity

theorem maj_toReal (N : ℕ) (U : Set (Fin (Module.finrank F E) → Af F)) (x : AE F E) :
    (GlobalTheory.XTermMaj.maj F E N U x).toReal = {y | finCrd F E y ∈ U}.indicator (fun y => (1 + archSize F E y) ^ (-(N : ℝ))) x := by
  unfold GlobalTheory.XTermMaj.maj
  by_cases h : finCrd F E x ∈ U
  · rw [Set.indicator_of_mem (by exact h), Set.indicator_of_mem (show x ∈ {y | finCrd F E y ∈ U} from h),
      ENNReal.toReal_ofReal]
    · rfl
    · apply Real.rpow_nonneg
      have := archSize_nonneg F E x
      exact le_trans zero_le_one (le_add_of_nonneg_right this)
  · rw [Set.indicator_of_notMem (by exact h), Set.indicator_of_notMem (show x ∉ {y | finCrd F E y ∈ U} from h)]
    rfl

theorem measurable_maj (N : ℕ) {U : Set (Fin (Module.finrank F E) → Af F)} (hU : IsCompact U) :
    Measurable fun l : (AE F E)ˣ => (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal := by
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  simp_rw [maj_toReal]
  have hc : Continuous fun l : (AE F E)ˣ => (l : AE F E) := Units.continuous_val
  have hS : MeasurableSet {l : (AE F E)ˣ | finCrd F E (l : AE F E) ∈ U} :=
    (hU.isClosed.preimage ((continuous_finCrd F E).comp hc)).measurableSet
  have hne : ∀ l : (AE F E)ˣ, 1 + archSize F E (l : AE F E) ≠ 0 ∨ 0 ≤ -(N : ℝ) := fun l =>
    Or.inl (ne_of_gt (by have := archSize_nonneg F E (l : AE F E); linarith))
  have hf : Measurable fun l : (AE F E)ˣ => (1 + archSize F E (l : AE F E)) ^ (-(N : ℝ)) :=
    ((continuous_const.add ((continuous_archSize F E).comp hc)).rpow_const hne).measurable
  have heq : (fun l : (AE F E)ˣ => {y | finCrd F E y ∈ U}.indicator (fun y => (1 + archSize F E y) ^ (-(N : ℝ))) (l : AE F E)) =
      {l : (AE F E)ˣ | finCrd F E (l : AE F E) ∈ U}.indicator (fun l => (1 + archSize F E (l : AE F E)) ^ (-(N : ℝ))) := by
    rfl
  rw [heq]
  exact hf.indicator hS

theorem integrable_of_le_maj (μ : Measure (AE F E)ˣ) [μ.IsHaarMeasure] {U : Set (Fin (Module.finrank F E) → Af F)}
    (hU : IsCompact U) (g : (AE F E)ˣ → ℝ) (hgm : Measurable g) (hg0 : ∀ l, 0 ≤ g l) (C : ℕ → ℝ)
    (hC : ∀ N l, g l ≤ C N * (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal) {s : ℝ} (hs : 1 < s) :
    Integrable (fun l => g l * (absE F E l : ℝ) ^ s) μ := by
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨N, k, L, C', hk, hb⟩ := GlobalTheory.TateConv.bound F E hs hU
  have hpow : Continuous fun l : (AE F E)ˣ => (absE F E l : ℝ) ^ s :=
    (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).rpow_const fun _ => Or.inr (by linarith)
  refine ⟨(hgm.mul hpow.measurable).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  set c := max (C N) 0
  have hle : ∀ l : (AE F E)ˣ, ‖g l * (absE F E l : ℝ) ^ s‖ₑ ≤ ENNReal.ofReal c *
      ENNReal.ofReal (C' * (infiniteZetaBound s k (IdeleGroup.toInfinite E (GlobalTheory.TateConv.idl F E l)) *
        finiteZetaBound L s (IdeleGroup.toFinite E (GlobalTheory.TateConv.idl F E l)))) := by
    intro l
    have ha : 0 ≤ (absE F E l : ℝ) ^ s := Real.rpow_nonneg (NNReal.coe_nonneg _) _
    have hm0 : 0 ≤ (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal := ENNReal.toReal_nonneg
    rw [Real.enorm_of_nonneg (mul_nonneg (hg0 l) ha)]
    calc ENNReal.ofReal (g l * (absE F E l : ℝ) ^ s)
        ≤ ENNReal.ofReal (c * (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal * (absE F E l : ℝ) ^ s) := by
          apply ENNReal.ofReal_le_ofReal
          refine mul_le_mul_of_nonneg_right ((hC N l).trans ?_) ha
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
      _ = ENNReal.ofReal c * (ENNReal.ofReal (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal *
            ENNReal.ofReal ((absE F E l : ℝ) ^ s)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (le_max_right _ _), mul_assoc]
      _ ≤ ENNReal.ofReal c * (GlobalTheory.XTermMaj.maj F E N U (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ s)) := by
          gcongr
          exact ENNReal.ofReal_toReal_le
      _ ≤ _ := by gcongr; exact hb l
  calc ∫⁻ l, ‖g l * (absE F E l : ℝ) ^ s‖ₑ ∂μ ≤ ∫⁻ l, _ ∂μ := lintegral_mono hle
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (GlobalTheory.TateConv.lintegral_bound_lt_top F E μ hs hk L C')

end GlobalTheory.ConeMaj

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.ConeMaj.cone_integrand_majorant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, ∃ g : (AE F E)ˣ → ℝ, (∀ s : ℝ, 1 < s → Integrable (fun l => g l * (absE F E l : ℝ) ^ s) μ) ∧
      ∀ (k : K) (l : (AE F E)ˣ), ‖G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1‖ ≤ g l := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hcfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  obtain ⟨U, hU, hsupp⟩ := GlobalTheory.T.config_B_triple_stabilizer hKP F E σ B a b G G₁ H H' hcfg e' he' K hK X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  choose C hC using GlobalTheory.T.config_B_triple_compare hKP F E σ B a b G G₁ H H' hcfg e' he' K hK X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  have hbd : ∀ N (k : K) (l : (AE F E)ˣ), ‖G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1‖ ≤ C N * (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal := by
    intro N k l
    rw [GlobalTheory.ConeMaj.maj_toReal]
    by_cases hl : GlobalTheory.ConeMaj.finCrd F E (l : AE F E) ∈ U
    · rw [Set.indicator_of_mem (show (l : AE F E) ∈ {y | GlobalTheory.ConeMaj.finCrd F E y ∈ U} from hl)]
      exact hC N k l
    · rw [Set.indicator_of_notMem (show (l : AE F E) ∉ {y | GlobalTheory.ConeMaj.finCrd F E y ∈ U} from hl), mul_zero]
      rw [hsupp k l hl, norm_zero]
  obtain ⟨g, hg⟩ : ∃ g : (AE F E)ˣ → ℝ, g = fun l : (AE F E)ˣ => ⨅ N : ℕ, C N * (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal := ⟨_, rfl⟩
  have hbb : ∀ l : (AE F E)ˣ, BddBelow (Set.range fun N : ℕ => C N * (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal) :=
    fun l => ⟨0, by rintro _ ⟨N, rfl⟩; exact (norm_nonneg _).trans (hbd N 1 l)⟩
  have hfg : ∀ (k : K) (l : (AE F E)ˣ), ‖G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1‖ ≤ g l :=
    fun k l => by rw [hg]; exact le_ciInf fun N => hbd N k l
  have hgC : ∀ N (l : (AE F E)ˣ), g l ≤ C N * (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal := fun N l => by
    rw [hg]; exact ciInf_le (hbb l) N
  have hg0 : ∀ l, 0 ≤ g l := fun l => (norm_nonneg _).trans (hfg 1 l)
  have hgm : Measurable g := by
    rw [hg]
    exact Measurable.iInf fun N => measurable_const.mul (GlobalTheory.ConeMaj.measurable_maj F E N hU)
  refine ⟨g, fun s hs => GlobalTheory.ConeMaj.integrable_of_le_maj F E μ hU g hgm hg0 C hgC hs, fun k l => hfg k l⟩
