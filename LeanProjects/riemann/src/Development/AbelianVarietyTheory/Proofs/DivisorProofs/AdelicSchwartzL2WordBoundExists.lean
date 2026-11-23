import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedSpaceDualVectorTraceFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivApplyEqFoldrDirectionalFderivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMultilinearMapNormLeSumBasisValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPowLeConstMulOneAddSumAbsBasisCoordPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceMultiplicationDerivativeWordIteratedFDerivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSqLeSumLintegralEnormSqOfPointwiseStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.WeilL2Words

theorem adelic_schwartz_slice_l2_word_bound : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ i j : ℕ,
    ∃ (L : List (List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))) (C : ℝ), ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : (κ → FiniteAdeleRing (𝓞 F) F),
      ENNReal.ofReal (∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2) ≤
        ENNReal.ofReal C * (L.map fun w => ∫⁻ x, ‖GlobalTheory.WeilL2Words.word F ψ w Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum := by
  intro F _ _ _ κ _ ψ hψ i j
  obtain ⟨ℓ, hnd, hℓ⟩ := hψ
  obtain ⟨n, ⟨b⟩⟩ : ∃ n, Nonempty (Module.Basis (Fin n) ℝ (κ → mixedEmbedding.mixedSpace F)) :=
    ⟨_, ⟨Module.finBasis ℝ _⟩⟩
  obtain ⟨K4, hK4, hb4⟩ := GlobalTheory.T.continuousMultilinearMap_norm_le_sum_basis_values (κ → mixedEmbedding.mixedSpace F) _ b j
  obtain ⟨K5, hK5, hb5⟩ := GlobalTheory.T.norm_pow_le_const_mul_one_add_sum_abs_basisCoord_pow (κ → mixedEmbedding.mixedSpace F) _ b i
  choose u hu using fun c => GlobalTheory.T.exists_mixedSpace_dual_vector_traceForm F κ ℓ hnd (b.coord c)
  let ia : Option (Fin n) → ℕ := fun a => a.elim 0 (fun _ => i)
  let ua : Option (Fin n) → (κ → mixedEmbedding.mixedSpace F) := fun a => a.elim 0 u
  let wd : Option (Fin n) × (Fin j → Fin n) →
      List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :=
    fun p => List.replicate (ia p.1) (0, ua p.1) ++ (List.ofFn fun r => b (p.2 r)).map fun v => (v, 0)
  refine ⟨Finset.univ.toList.map wd, (K5 * K4) ^ 2 * (Fintype.card (Option (Fin n) × (Fin j → Fin n)) : ℝ),
    fun Φ hΦ y => ?_⟩
  obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F hΦ y
  have hsf : (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) = s := funext fun x => (hs x).symm
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := hsf ▸ s.smooth ⊤
  have hℓc : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  have key : ∀ p x, GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
      (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * ua p.1 k) : ℂ)) ^ (ia p.1) *
        iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r)) := by
    intro p x
    rw [GlobalTheory.T.slice_multiplicationDerivativeWord_iteratedFDeriv F κ ψ ℓ hℓ Φ y hsm, GlobalTheory.T.iteratedFDeriv_apply_eq_foldr_directional_fderiv _ _ hsm]
  have hcont : ∀ p, Continuous fun x => GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
    intro p
    simp_rw [key]
    have h1 : Continuous fun x : κ → mixedEmbedding.mixedSpace F => ∑ k, x k * ua p.1 k := by fun_prop
    have h2 : Continuous fun x => iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x :=
      hsm.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    exact ((continuous_const.mul (Complex.continuous_ofReal.comp (hℓc.comp h1))).pow _).mul
      ((ContinuousMultilinearMap.apply ℝ _ ℂ (fun r => b (p.2 r))).continuous.comp h2)
  rw [List.map_map, Finset.sum_map_toList]
  refine GlobalTheory.T.integral_sq_le_sum_lintegral_enorm_sq_of_pointwise _ MeasureTheory.volume _ _ _ _ hcont fun x => ?_
  have hterm : ∀ p : Option (Fin n) × (Fin j → Fin n),
      p.1.elim 1 (fun c => |b.coord c x| ^ i) *
          ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r))‖ ≤
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ := by
    intro p
    rw [key, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rcases p with ⟨_ | c, cs⟩
    · simp [ia]
    · simp only [Option.elim, ia, ua, hu, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_I, Real.norm_eq_abs, mul_one]
      rw [mul_pow]
      refine le_mul_of_one_le_left (by positivity) (one_le_pow₀ ?_)
      rw [abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
  have h1 : ‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ ≤
      K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ := by
    calc _ ≤ (K5 * (1 + ∑ c, |b.coord c x| ^ i)) *
          (K4 * ∑ cs : Fin j → Fin n, ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x
            (fun r => b (cs r))‖) :=
          mul_le_mul (hb5 x) (hb4 _) (norm_nonneg _) (by positivity)
      _ = K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n), p.1.elim 1 (fun c => |b.coord c x| ^ i) *
          ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r))‖ := by
          rw [Fintype.sum_prod_type, Fintype.sum_option]
          simp only [Option.elim, one_mul, ← Finset.mul_sum, ← Finset.sum_mul]
          ring
      _ ≤ _ := by
          gcongr with p
          exact hterm p
  have h0 : 0 ≤ ‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ := by positivity
  calc _ ≤ (K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (K5 * K4) ^ 2 * (∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖) ^ 2 := by ring
    _ ≤ (K5 * K4) ^ 2 * ((Fintype.card (Option (Fin n) × (Fin j → Fin n)) : ℝ) * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ ^ 2) := by
          gcongr
          exact sq_sum_le_card_mul_sum_sq
    _ = _ := by ring

end GlobalTheory.WeilL2Words
