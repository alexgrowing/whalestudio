import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanPoly

open Polynomial

theorem coeff_heckePolyOf_le (n q : ℕ) (a : ℕ → ℂ) {i : ℕ} (hi : i ≤ n) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff i = (-1) ^ i * (q : ℂ) ^ (i * (i - 1) / 2) * a i := by
  unfold Formalism.L2.Col.heckePolyOf
  rw [finset_sum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b _ hb
    rw [coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem heckePolyOf_eq_zero (n q : ℕ) (a : ℕ → ℂ) (h : ∀ k ≤ n, a k = 0) :
    Formalism.L2.Col.heckePolyOf n q a = 0 := by
  unfold Formalism.L2.Col.heckePolyOf
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [h k (by simpa [Nat.lt_succ_iff] using hk)]
  simp

theorem single_mem_span (nX nY q : ℕ) (hq : q ≠ 0) (c : ℂ) (hc : c ≠ 0) (B : Polynomial ℂ) (hB : B ≠ 0)
    (z : ℕ → ℕ → ℂ)
    (h : ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf nX q (fun k => ∑ j ∈ Finset.range (nY + 1), z k j * a j) =
      (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) * B)
    (j : Fin (nY + 1)) :
    Pi.single j (1 : ℂ) ∈ Submodule.span ℂ (Set.range fun k : Fin (nX + 1) => fun i : Fin (nY + 1) => z k i) := by
  by_contra hj
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hj inferInstance
  set a : ℕ → ℂ := fun i => if hi : i < nY + 1 then f (Pi.single ⟨i, hi⟩ 1) else 0 with ha
  have hfv : ∀ k : ℕ, f (fun i : Fin (nY + 1) => z k i) = ∑ i ∈ Finset.range (nY + 1), z k i * a i := by
    intro k
    rw [← Fin.sum_univ_eq_sum_range (fun i => z k i * a i)]
    conv_lhs => rw [show (fun i : Fin (nY + 1) => z k i) = ∑ i : Fin (nY + 1), z k i • Pi.single i (1 : ℂ) by
      ext m; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := Fin.is_le i
    simp [ha, hi]
  have hzero : ∀ k ≤ nX, ∑ i ∈ Finset.range (nY + 1), z k i * a i = 0 := by
    intro k hk
    rw [← hfv k]
    have hm : f (fun i : Fin (nY + 1) => z k i) ∈ Submodule.map f (Submodule.span ℂ (Set.range fun k : Fin (nX + 1) => fun i : Fin (nY + 1) => z k i)) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩)
    rw [hmap] at hm
    simpa using hm
  have h0 := h a
  rw [heckePolyOf_eq_zero _ _ _ hzero] at h0
  have hcomp : (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) = 0 := by
    rcases mul_eq_zero.1 h0.symm with h1 | h1
    · exact h1
    · exact absurd h1 hB
  have hco := congrArg (fun p => Polynomial.coeff p j) hcomp
  simp only [comp_C_mul_X_coeff, coeff_zero] at hco
  rw [coeff_heckePolyOf_le _ _ _ (Nat.lt_succ_iff.1 j.isLt)] at hco
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have haj : a j = 0 := by
    simpa [hc, hqc] using hco
  apply hf
  have hjle := Fin.is_le j
  simpa [ha, hjle] using haj

end GlobalTheory.SpanPoly

namespace GlobalTheory.SpanPoly

theorem single_splitLab_mem_span : ∀ (nX nY q : ℕ), q ≠ 0 → ∀ (c : ℂ), c ≠ 0 → ∀ (B : Polynomial ℂ), B ≠ 0 → ∀ (z : ℕ → ℕ → ℂ), (∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf nX q (fun k => ∑ j ∈ Finset.range (nY + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) * B) → ∀ j ≤ nY, Finsupp.single (splitLab nY j) (1 : ℂ) ∈ Submodule.span ℂ ((fun k => GlobalTheory.Hk3.splitC nY (z k)) '' Set.Iic nX) := by
  intro nX nY q hq c hc B hB z h j hj
  let φ : (Fin (nY + 1) → ℂ) →ₗ[ℂ] (List ℤ →₀ ℂ) :=
    ∑ i : Fin (nY + 1), (Finsupp.lsingle (splitLab nY i)).comp (LinearMap.proj i)
  have hφz : ∀ k, φ (fun i : Fin (nY + 1) => z k i) = GlobalTheory.Hk3.splitC nY (z k) := by
    intro k
    unfold GlobalTheory.Hk3.splitC
    rw [← Fin.sum_univ_eq_sum_range (fun i => Finsupp.single (splitLab nY i) (z k i))]
    simp [φ]
  have hφe : φ (Pi.single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nY + 1)) 1) = Finsupp.single (splitLab nY j) (1 : ℂ) := by
    simp only [φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Finsupp.lsingle_apply]
    rw [Finset.sum_eq_single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nY + 1))]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  rw [← hφe]
  have hm := Submodule.mem_map_of_mem (f := φ) (single_mem_span nX nY q hq c hc B hB z h ⟨j, Nat.lt_succ_of_le hj⟩)
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact ⟨k, Set.mem_Iic.2 (Nat.lt_succ_iff.1 k.isLt), (hφz k).symm⟩

end GlobalTheory.SpanPoly
