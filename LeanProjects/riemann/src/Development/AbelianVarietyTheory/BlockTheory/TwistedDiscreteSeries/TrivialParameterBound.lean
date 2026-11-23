import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound

open Formalism.UG GlobalTheory.PRep GlobalTheory.LGrp GlobalTheory.LFun

def TrivialBound (q n : ℕ) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∀ i, ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) ≤ ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ ≤ ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)

def SatakeBoundInert : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
      IsIrrSmooth π → IsUnitarisable π → HasSatU ϖ q π α → TrivialBound q n α

def SatakeBoundInertPS : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (hU : IsUnramInv ϖ σ q) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GU σ n) V)
    (α : Fin (n / 2) → ℂˣ),
      (haveI := locallyCompact_GU_of_unram hU n; HasSatakeU π α) → IsUnitarisable π → TrivialBound q n α

theorem bound_eq (q n : ℕ) : ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) = (q : ℝ) ^ ((n : ℝ) - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1
  push_cast
  ring

def trivParam (q n : ℕ) (hq : q ≠ 0) : Fin (n / 2) → ℂˣ :=
  fun i => Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))

theorem trivial_hyp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (hq : q ≠ 0) (n : ℕ) :
    IsIrrSmooth (charRep (1 : GU σ n →* ℂˣ)) ∧ IsUnitarisable (charRep (1 : GU σ n →* ℂˣ)) ∧
      HasSatU ϖ q (charRep (1 : GU σ n →* ℂˣ)) (trivParam q n hq) := by
  have hc : ∀ b : GU σ n, chiDeltaU q (fun i => (trivParam q n hq i : ℂ)) b = 1 := fun b => by
    refine Finset.prod_eq_one fun i _ => ?_
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    split_ifs with h
    · simp only [trivParam, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← zpow_mul, ← zpow_add₀ hq']
      convert zpow_zero (q : ℂ) using 2
      ring
    · rfl
  refine ⟨⟨fun z => by simp, charRep_irreducible _⟩, charRep_unitarisable _ (by simp), ?_, fun x _ h0 => ?_⟩
  · exact (Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 (by simp), one_ne_zero⟩
  · refine IsSatVecU.of_map hU (ρ' := rightReg ℂ _ ℂ) (LinearMap.pi fun _ => LinearMap.id)
      (fun g y => by funext z; simp [rightReg, LinearMap.funLeft]) (fun a b e => congrFun e 1)
      (isSatVecU_of_isSphericalU hU (fun b g k _ _ => by simp [hc]) fun e => h0 (congrFun e 1))

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound

end
