import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosetsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta.AbsZeta

theorem trivial_isUnitarisable (G : Type) [Group G] : IsUnitarisable (Representation.trivial ℂ G ℂ) := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a b => a * starRingEnd ℂ b)
    (fun a a' b => add_mul a a' _) (fun c a b => by simp [smul_eq_mul, mul_assoc])
    (fun a b b' => by simp [mul_add]) (fun c a b => by simp [smul_eq_mul]; ring), ?_, ?_, ?_⟩
  · intro a b
    simp [mul_comm]
  · intro a ha
    simpa [Complex.mul_conj, Complex.normSq_pos] using ha
  · intro g a b
    simp

theorem kerGL_norm {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r N : ℕ} {z : ℂˣ}
    {φ : GL (Fin r) (w.adicCompletion E) → ℂ} (hz : ‖(z : ℂ)‖ = 1) (hφ : KerGL w N z φ) :
    KerGL w N 1 (fun g => ((‖φ g‖ : ℝ) : ℂ)) := by
  intro ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  have hq : ∀ m : ℤ, (qV E w : ℂ) ^ (-((N : ℂ) / 2) * (m : ℂ)) =
      (((qV E w : ℝ) ^ (-((N : ℝ) / 2) * (m : ℝ)) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have hpos : 0 ≤ (qV E w : ℝ) ^ (-((N : ℝ) / 2) * ((∑ i, |d i| : ℤ) : ℝ)) := by positivity
  beta_reduce
  rw [hφ ϖ hϖ d t ht k₁ hk₁ k₂ hk₂, hq]
  simp [norm_zpow, hz, Complex.norm_real, Real.norm_of_nonneg hpos]
  positivity

end GlobalTheory.FinZeta.AbsZeta

open GlobalTheory.FinZeta.AbsZeta in

theorem GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∃ B : Multiset ℂˣ, B.card = r ∧ (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac B (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => β⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) := by
  intro H E _ _ w r t hrt z φ hz hφ
  obtain ⟨B, hB, hbd⟩ := GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL E w r ℂ (Representation.trivial ℂ _ ℂ) (trivial_isUnitarisable _) 1 one_ne_zero
    (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) (fun h _ => ⟨_, (mul_one _).symm⟩)
  have hs := GlobalTheory.T.unramified_zeta_sum_GL_cosets H E w r t hrt 1 (fun g => ((‖φ g‖ : ℝ) : ℂ)) (by simp) (kerGL_norm hz hφ) ℂ
    (Representation.trivial ℂ _ ℂ) 1 B hB hbd LinearMap.id ⟨1, fun g => by simp⟩
  refine ⟨B, ?_, hbd, ?_⟩
  · have hB' := hB
    unfold IsSatVecGL at hB'
    exact hB'.2.2.1
  · simpa using hs
