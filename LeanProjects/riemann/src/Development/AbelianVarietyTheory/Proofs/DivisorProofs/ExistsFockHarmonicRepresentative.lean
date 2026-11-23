import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLineMatrixKroneckerRightFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable

noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg MvPolynomial GlobalTheory.FockDeg

namespace GlobalTheory.FockAlg.HarmLift

variable {p q r s : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem plusPart_eq_sub {Z : Mat p q} (hZ : IsPC Z) (Q : Pol p q r s) :
    plusPart (fockAct1 p q r s Z) Q = fockAct1 p q r s Z Q - minusPart (fockAct1 p q r s Z) Q := by
  rw [fockAct1_eq, omAct_eq_parts (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ) Q, add_sub_cancel_right]

theorem minusPart_mem {Z : Mat p q} (hZ : IsPC Z) {d : ℕ} {Q : Pol p q r s}
    (hQ : Q ∈ homog (Ix p q × Ix r s) d) :
    minusPart (fockAct1 p q r s Z) Q ∈ homog (Ix p q × Ix r s) (d - 2) := by
  rw [fockAct1_eq, minusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ)]
  exact downOp_mem _ d Q hQ

theorem minusPart_low {Z : Mat p q} (hZ : IsPC Z) {d : ℕ} (hd : d < 2) {Q : Pol p q r s}
    (hQ : Q ∈ homog (Ix p q × Ix r s) d) : minusPart (fockAct1 p q r s Z) Q = 0 := by
  rw [fockAct1_eq, minusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ)]
  exact downOp_low _ d Q hd hQ

theorem span_harm2 : Submodule.span ℂ (harm2 p q r s) = HarmStable.sub2 p q r s := by
  rw [← HarmStable.coe_fockHarmonicsSecondMemberSubmodule, Submodule.span_eq]

theorem homog_le (pr : Pol p q r s →ₗ[ℂ] W)
    (hpr : ∀ Z : Mat p q, IsPC Z → ∀ f, pr (fockAct1 p q r s Z f) = 0) (d : ℕ) :
    homog (Ix p q × Ix r s) d ≤ HarmStable.sub2 p q r s ⊔ LinearMap.ker pr := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases Nat.lt_or_ge d 2 with hd | hd
    · intro f hf
      refine Submodule.mem_sup_left ?_
      rw [← SetLike.mem_coe, HarmStable.coe_fockHarmonicsSecondMemberSubmodule]
      exact fun Z hZ => minusPart_low hZ hd hf
    · obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
      rw [(GlobalTheory.FischerParts.fischer_parts p q r s n).1, span_harm2]
      refine sup_le (inf_le_right.trans le_sup_left) (Submodule.span_le.2 ?_)
      rintro _ ⟨Q, hQ, Z, hZ, rfl⟩
      rw [SetLike.mem_coe, plusPart_eq_sub hZ]
      refine Submodule.sub_mem _ (Submodule.mem_sup_right (hpr Z hZ Q)) ?_
      exact ih (n - 2) (by omega) (minusPart_mem hZ hQ)

theorem exists_harm2_rep : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (pr : Pol P Q R S →ₗ[ℂ] W), (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) →
    ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := by
  intro P Q R S W _ _ pr hpr f
  have hf : f ∈ HarmStable.sub2 P Q R S ⊔ LinearMap.ker pr := by
    rw [← sum_homogeneousComponent f]
    exact Submodule.sum_mem _ fun i _ => homog_le pr hpr i (homogeneousComponent_mem i f)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
  refine ⟨y, ?_, ?_⟩
  · rw [← HarmStable.coe_fockHarmonicsSecondMemberSubmodule]; exact hy
  · rw [map_add, LinearMap.mem_ker.1 hz, add_zero]

end GlobalTheory.FockAlg.HarmLift
