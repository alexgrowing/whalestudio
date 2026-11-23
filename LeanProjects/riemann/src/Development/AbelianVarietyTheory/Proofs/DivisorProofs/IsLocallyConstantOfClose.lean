import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable local instance measFvStd {F : Type} [Field F] [NumberField F] (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFvStd {F : Type} [Field F] [NumberField F] (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

noncomputable section

namespace GlobalTheory.StdPairCone

section SBProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unif_pow_facts {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (c : ℕ) :
    valuation k ((ϖ ^ (c + 1) : kˣ) : k) < 1 ∧
      valuation k ((ϖ ^ (c + 1) : kˣ) : k) ≤ valuation k ((ϖ ^ c : kˣ) : k) ∧
      valuation k ((ϖ ^ c : kˣ) : k) ≤ 1 := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hc : valuation k ((ϖ ^ c : kˣ) : k) ≤ 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]; exact pow_le_one' hlt.le c
  have he : valuation k ((ϖ ^ (c + 1) : kˣ) : k) = valuation k ((ϖ ^ c : kˣ) : k) * valuation k (ϖ : k) := by
    rw [pow_succ, Units.val_mul, map_mul]
  refine ⟨?_, ?_, hc⟩
  · rw [he]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hlt
  · rw [he]; exact mul_le_of_le_one_right' hlt.le

theorem cball_stable {c : ℕ} {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {x y : k}
    (hxy : valuation k (y - x) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k)) (hx : x ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) :
    y ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
  obtain ⟨-, hec, -⟩ := unif_pow_facts hϖ c
  simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx ⊢
  have : y = (y - x) + x := by ring
  rw [this]
  exact Valuation.map_add_le _ (hxy.trans hec) hx

theorem isLocallyConstant_of_close {m n : ℕ} (s : kˣ) (f : Matrix (Fin m) (Fin n) k → ℂ)
    (hf : ∀ X Y : Matrix (Fin m) (Fin n) k, (∀ i j, valuation k (Y i j - X i j) ≤ valuation k (s : k)) → f Y = f X) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro X
  have : ∀ᶠ Y in 𝓝 X, ∀ i j, valuation k (Y i j - X i j) ≤ valuation k (s : k) := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    have hc : Continuous fun Y : Matrix (Fin m) (Fin n) k => Y i j - X i j :=
      (continuous_id.matrix_elem i j).sub continuous_const
    have ht := hc.tendsto X
    simp only [sub_self] at ht
    exact ht (GlobalTheory.SplitWeil.cball_mem_nhds s)
  exact this.mono fun Y hY => hf X Y hY

theorem hasCompactSupport_of_int {m n : ℕ} (f : Matrix (Fin m) (Fin n) k → ℂ)
    (hf : ∀ X, f X ≠ 0 → ∀ i j, X i j ∈ 𝒪[k]) : HasCompactSupport f := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hK := isCompact_univ_pi fun _ : Fin m => isCompact_univ_pi fun _ : Fin n => GlobalTheory.SplitWeil.isCompact_int k
  refine HasCompactSupport.intro (f := f) hK fun X hX => ?_
  by_contra h
  exact hX (Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => hf X h i j)

end SBProof

end GlobalTheory.StdPairCone
