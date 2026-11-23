import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZRYRCover
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

open MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm GlobalTheory.Harm.HighestUnique

namespace GlobalTheory.CompactHarm

theorem fst_eq_of_mixedWeight {k l p q : ℕ} (N : ℕ) (a : Fin k → ℕ) (b : Fin l → ℕ)
    (hpq : p + q ≤ N) (ha : ∀ c, 0 < a c ↔ (c : ℕ) < p) (hb : ∀ d, 0 < b d ↔ (d : ℕ) < q)
    (c : Fin k) :
    a c = if h : (c : ℕ) < N then (mixedWeight N a b ⟨c, h⟩).toNat else 0 := by
  have hac := ha c
  split_ifs with h
  · rw [mixedWeight_apply]
    simp only [c.2, dif_pos, Fin.eta]
    split_ifs with h2
    · have hb' : (0 : ℤ) ≤ (b ⟨N - 1 - c, h2⟩ : ℤ) := by positivity
      have h4 : (c : ℕ) < N := h
      by_cases hcp : (c : ℕ) < p
      · have hbc := hb ⟨N - 1 - c, h2⟩
        have : b ⟨N - 1 - c, h2⟩ = 0 := by simp only at hbc; omega
        rw [this]; omega
      · have : a c = 0 := by omega
        rw [this]; omega
    · omega
  · omega

theorem snd_eq_of_mixedWeight {k l p q : ℕ} (N : ℕ) (a : Fin k → ℕ) (b : Fin l → ℕ)
    (hpq : p + q ≤ N) (ha : ∀ c, 0 < a c ↔ (c : ℕ) < p) (hb : ∀ d, 0 < b d ↔ (d : ℕ) < q)
    (d : Fin l) :
    b d = if h : (d : ℕ) < N then (-mixedWeight N a b ⟨N - 1 - d, by omega⟩).toNat else 0 := by
  have hbd := hb d
  split_ifs with h
  · rw [mixedWeight_apply]
    have e : N - 1 - (N - 1 - (d : ℕ)) = d := by omega
    have hd : N - 1 - (N - 1 - (d : ℕ)) < l := by omega
    rw [dif_pos hd]
    have hbe : b ⟨N - 1 - (N - 1 - (d : ℕ)), hd⟩ = b d := congrArg b (Fin.ext e)
    simp only [hbe]
    split_ifs with h1
    · have ha' : (0 : ℤ) ≤ (a ⟨N - 1 - d, h1⟩ : ℤ) := by positivity
      have hac := ha ⟨N - 1 - d, h1⟩
      by_cases hdq : (d : ℕ) < q
      · have : a ⟨N - 1 - d, h1⟩ = 0 := by simp only at hac; omega
        rw [this]; omega
      · have : b d = 0 := by omega
        rw [this]; omega
    · omega
  · omega

theorem jointTop_line : ∀ {σ : Type} {k l N : ℕ} (z : Fin k × Fin N → σ) (y : Fin l × Fin N → σ),
    Function.Injective z → Function.Injective y → (∀ u w, z u ≠ y w) →
    (∀ s, (∃ u, z u = s) ∨ ∃ w, y w = s) → ∀ κ : Fin N → ℂ, ∃ Q₀ : MvPolynomial σ ℂ,
    ∀ (α : Fin k → ℂ) (β : Fin l → ℂ) (f : MvPolynomial σ ℂ),
      GlobalTheory.CompactHarm.JointTop z y κ α β f → ∃ r : ℂ, f = r • Q₀ := by
  intro σ k l N z y hz hy hzy hs κ
  classical
  by_cases hex : ∃ α β f, f ≠ 0 ∧ JointTop z y κ α β f
  · obtain ⟨α₀, β₀, f₀, hf0, hJ0⟩ := hex
    obtain ⟨a, b, p, q, hpq, hp, hq, hpa, hqb, hκ, rfl, rfl, hhom⟩ :=
      weights_of_jointTop z hz y hy hzy hs κ α₀ β₀ hf0 hJ0
    have hbij : Function.Bijective (Sum.elim z y) := by
      refine ⟨hz.sumElim hy hzy, fun s => ?_⟩
      rcases hs s with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact ⟨.inl u, rfl⟩
      · exact ⟨.inr u, rfl⟩
    have : Finite σ := Finite.of_surjective _ hbij.2
    have := finite_homog (σ := σ) (∑ c, a c + ∑ d, b d)
    have ha : Antitone a := fun i j hij => by
      have := highest_weight_antitone (rowOp ℂ z) (rowOp_lie z hz) (homogeneousSubmodule σ ℂ _)
        (fun i j w hw => by rw [rowOp_eq_colOp]; exact colOp_homog _ _ _ hw) f₀ hhom hf0
        (fun c => a c) hJ0.2.2.1 (fun c => by simpa using hJ0.2.2.2.1 c) hij
      exact Int.ofNat_le.1 this
    have hb : Antitone b := fun i j hij => by
      have := highest_weight_antitone (rowOp ℂ y) (rowOp_lie y hy) (homogeneousSubmodule σ ℂ _)
        (fun i j w hw => by rw [rowOp_eq_colOp]; exact colOp_homog _ _ _ hw) f₀ hhom hf0
        (fun c => b c) hJ0.2.2.2.2.1 (fun c => by simpa using hJ0.2.2.2.2.2.1 c) hij
      exact Int.ofNat_le.1 this
    obtain ⟨P₀, -, -, hu⟩ := exists_unique_jointTop z hz y hy hzy hs hpq hp hq a b ha hb
      (fun c hc => by have := hpa c; omega) (fun d hd => by have := hqb d; omega)
    subst hκ
    refine ⟨P₀, fun α β f hJ => ?_⟩
    by_cases hf : f = 0
    · exact ⟨0, by simp [hf]⟩
    obtain ⟨a', b', p', q', hpq', -, -, hpa', hqb', hκ', rfl, rfl, -⟩ :=
      weights_of_jointTop z hz y hy hzy hs _ α β hf hJ
    have hw : mixedWeight N a b = mixedWeight N a' b' :=
      funext fun i => by exact_mod_cast congrFun hκ' i
    have e1 : a' = a := funext fun c => by
      rw [fst_eq_of_mixedWeight N a' b' hpq' hpa' hqb' c, fst_eq_of_mixedWeight N a b hpq hpa hqb c,
        hw]
    have e2 : b' = b := funext fun d => by
      rw [snd_eq_of_mixedWeight N a' b' hpq' hpa' hqb' d, snd_eq_of_mixedWeight N a b hpq hpa hqb d,
        hw]
    subst e1 e2
    exact hu f hJ
  · refine ⟨0, fun α β f hJ => ⟨0, ?_⟩⟩
    by_contra hf
    exact hex ⟨α, β, f, by simpa using hf, hJ⟩

end GlobalTheory.CompactHarm
