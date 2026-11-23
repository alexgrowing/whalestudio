import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnitOfIsUniUp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicClassFunBlockDiagonalEqSumDerivatives
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerTail
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsMirabolicConjInvariantTwistedTailMeanFun
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GgOneAndIsClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionRestrictionIsClassFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GelfandGraevCharacterGLnNormAndReciprocityStatement

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.ExactMult

variable {g : ℕ} [Fact g.Prime]

theorem wh_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Gn g n → ℂ) :
    wh ψ (fun h => ∑ i ∈ s, f i h) = ∑ i ∈ s, wh ψ (f i) := by
  unfold wh tr
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun h => c * f h) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem wh_gg_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (gg ψ 0) = 1 := by
  have hU : ∀ M : Mt g 0, IsUniUp M := fun M a => a.elim0
  have hgg : ∀ x : Gn g 0, gg ψ 0 x = 1 := by
    intro x
    unfold gg
    simp [hU]
  unfold wh eU
  rw [GlobalTheory.GLm.TraceTail.tr_eDat]
  simp [hU, hgg]

theorem isClass_der (ψ : AddChar (ZMod g) ℂ) {N : ℕ} (i : ℕ) (hi : i ≤ N) (χ : Gn g N → ℂ)
    (hχ : IsClass χ) : IsClass (der ψ i χ) := by
  intro x y
  have h := ((GlobalTheory.GLq.HcClass.hc_class g i (N - i) N (by omega)).2 χ hχ).2
  unfold der
  congr 1
  funext z
  exact h z x y

theorem wh_hc (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ)
    (hα : IsClass α) (hβ : IsClass β) : wh ψ (hc a b α β (a + b)) = wh ψ α * wh ψ β := by
  unfold hc
  rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ a b (a + b) rfl _ (fun y x z => by simp only [hα x z])
    (fun x y z => by simp only [hβ y z])]
  simp only [wh_const_mul]
  rw [show (fun x => α x * wh ψ β) = (fun x => wh ψ β * α x) from funext fun _ => mul_comm _ _,
    wh_const_mul, mul_comm]

end GlobalTheory.GLq.ExactMult

namespace GlobalTheory.GLq.ExactMult

open GlobalTheory.GLm

theorem tr_eJ'_eq_sum_wh_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k : ℕ), 1 ≤ k →
    k < N → ∀ χ : Gn g N → ℂ, IsClass χ → tr (eJ' g N k ψ) χ =
      (∑ i ∈ Finset.range k, wh ψ (der ψ i χ) * ((g : ℂ) ^ (k - i) - (g : ℂ) ^ (k - i - 1))) +
        wh ψ (der ψ k χ) := by
  intro g _ ψ hψ N k _ hk χ hχ
  rw [tr_eJ'_eq_wh_tail g ψ N k χ hk]
  have hM : IsMirClass χ := fun p x _ _ => hχ x p
  have hF := GlobalTheory.GLm.TailClass.isMirClass_tail g ψ (k + 1) N χ (by omega) (by omega) hM
  rw [show (fun h => tail ψ (k + 1) χ (diag1 h (k + 1))) = fun h =>
      ∑ i ∈ Finset.range (k + 1), hc i (k - i) (der ψ i (tail ψ (k + 1) χ)) (gg ψ (k - i)) k h from
    funext (mirClass_diag1_eq_sum g ψ hψ k _ hF)]
  rw [wh_sum, Finset.sum_range_succ]
  have key : ∀ i, i < k + 1 → wh ψ (hc i (k - i) (der ψ i (tail ψ (k + 1) χ)) (gg ψ (k - i)) k) =
      wh ψ (der ψ i χ) * wh ψ (gg ψ (k - i)) := by
    intro i hi
    rw [GlobalTheory.GLm.DerTail.der_tail g ψ i (k + 1) N χ hi (by omega)]
    have := wh_hc ψ hψ i (k - i) (der ψ i χ) (gg ψ (k - i)) (isClass_der ψ i (by omega) χ hχ)
      (GlobalTheory.GLq.GGDeg.gg_one_and_isClass g ψ (k - i)).2
    rwa [show i + (k - i) = k by omega] at this
  rw [key k (by omega), Nat.sub_self, wh_gg_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [key i (by omega), (GlobalTheory.T.gelfandGraevCharacterGLn_norm_and_reciprocity g ψ hψ (k - i) (by omega)).1]

end GlobalTheory.GLq.ExactMult
