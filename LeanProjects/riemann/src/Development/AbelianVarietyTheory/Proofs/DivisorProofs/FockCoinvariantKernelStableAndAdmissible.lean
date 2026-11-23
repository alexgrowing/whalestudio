import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweHighestWeightSupStableLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsSupCoinvariantsEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionsLieRationalWeightsCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial

namespace GlobalTheory.HoweR

theorem coinv_stab_snd (P Q R S : ℕ) (x : ℂ) : Stab (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro Z y hy
  have hcomm := (GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S).2.2.2.2
  induction hy using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨X, f, rfl⟩ := hg
    refine Submodule.subset_span ⟨X, fockAct2 P Q R S Z f, ?_⟩
    rw [map_sub, map_smul, hcomm]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem degW_le_of_abs_le {p q : ℕ} (c : ℚ) (μ : Ix p q → ℚ) (B : ℚ) (hμ : ∀ a, |μ a| ≤ B) :
    degW c μ ≤ ((p + q : ℕ) : ℚ) * (B + |c|) := by
  unfold degW
  have h : ∀ a, |shiftNu c μ a| ≤ B + |c| := by
    intro a
    rcases a with i | j
    · simp only [shiftNu]; exact (abs_sub _ _).trans (add_le_add (hμ _) le_rfl)
    · simp only [shiftNu]; exact (abs_add_le _ _).trans (add_le_add (hμ _) le_rfl)
  calc ∑ a, |shiftNu c μ a| ≤ ∑ _a : Ix p q, (B + |c|) := Finset.sum_le_sum fun a _ => h a
    _ = _ := by simp [Finset.card_univ, Fintype.card_sum]; ring

theorem fockCoinvariantKernel_highestWeight_admissible (P Q R S : ℕ) (x : ℂ) : AdmMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro B
  refine ⟨restrictTotalDegree (Ln P Q R S) ℂ ⌊((R + S : ℕ) : ℚ) * (B + |cPair P Q|)⌋₊, inferInstance, ?_⟩
  intro μ hμ v hv
  obtain ⟨-, hL2, -, hw2, -⟩ := GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S
  have hgood : Good (fockAct2 P Q R S) := ⟨hL2, hw2, GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩
  obtain ⟨hspan, -, hK2, -⟩ := GlobalTheory.FockAlg.harm_graded_stable P Q R S _ (Or.inr (Or.inl rfl))
  have hKc : KStable (fockAct2 P Q R S) (coinv P Q R S x) := fun X _ w hw => coinv_stab_snd P Q R S x X w hw
  have hv' : v ∈ (Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x) ⊓ hwSub (fockAct2 P Q R S) μ :=
    ⟨by rw [GlobalTheory.T.fockHarmonics_sup_coinvariants_eq_top]; exact Submodule.mem_top, hv⟩
  have hsplit := GlobalTheory.T.howeHighestWeight_sup_stable_le R S _ (fockAct2 P Q R S) hgood _ _ hK2 hKc μ hv'
  obtain ⟨h, hh, c, hc, rfl⟩ := Submodule.mem_sup.1 hsplit
  refine Submodule.add_mem_sup ?_ hc.1
  rw [mem_restrictTotalDegree]
  have hh2 : h ∈ harm2 P Q R S := by rw [← hspan]; exact hh.1
  exact (GlobalTheory.DegKeep.deg_le_of_harm hh2 hh.2).trans (Nat.floor_mono (degW_le_of_abs_le _ μ B hμ))

theorem coinv_stab_adm : ∀ (P Q R S : ℕ) (x : ℂ),
    Stab (fockAct2 P Q R S) (coinv P Q R S x) ∧ AdmMod (fockAct2 P Q R S) (coinv P Q R S x) :=
  fun P Q R S x => ⟨coinv_stab_snd P Q R S x, fockCoinvariantKernel_highestWeight_admissible P Q R S x⟩

end GlobalTheory.HoweR

end
