import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RhoSum

theorem rho_one_eq {b : ℕ} (n : ℕ) (l : Fin b) :
    rho n (fun _ => 1) l = (n : ℂ) - 2 * (l : ℕ) - 1 := by
  simp [rho, Fin.card_Iio]

theorem sum_range_aff (n P j : ℕ) :
    ∑ m ∈ range j, ((n : ℂ) - 2 * ((P + m : ℕ) : ℂ) - 1) = (j : ℂ) * ((n : ℂ) - 2 * P - j) := by
  induction j with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

theorem filter_lt_eq_Iio {a : ℕ} (i : Fin a) :
    univ.filter (fun l : Fin a => (l : ℕ) < (i.castSucc : ℕ)) = Iio i := by
  ext l
  rw [mem_filter, mem_Iio, Fin.coe_castSucc, Fin.lt_iff_val_lt_val]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

theorem filter_lt_succ {a : ℕ} (i : Fin a) :
    univ.filter (fun l : Fin a => (l : ℕ) < (i.succ : ℕ)) = insert i (Iio i) := by
  ext l
  rw [mem_filter, mem_insert, mem_Iio, Fin.val_succ, Fin.lt_iff_val_lt_val, Fin.ext_iff]
  constructor
  · rintro ⟨-, h⟩; omega
  · intro h; exact ⟨mem_univ _, by omega⟩

theorem card_and_rho_sum : ∀ {a b : ℕ} (n : ℕ) (j : Fin a → ℕ) {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → (∀ i, (p i : ℕ) = ∑ l ∈ univ.filter (fun l : Fin a => (l : ℕ) < (i : ℕ)), j l) → ∀ i, #{l | β l = i} = j i ∧ ∑ l with β l = i, rho n (fun _ => 1) l = (j i : ℂ) * rho n j i := by
  intro a b n j β p hβ hp i
  set P : ℕ := (p i.castSucc : ℕ) with hP
  set Q : ℕ := (p i.succ : ℕ) with hQ
  have hPsum : (P : ℂ) = ∑ l ∈ Iio i, (j l : ℂ) := by
    rw [hP, hp, filter_lt_eq_Iio]; push_cast; rfl
  have hQP : Q = P + j i := by
    rw [hQ, hP, hp, hp, filter_lt_succ, filter_lt_eq_Iio, sum_insert (by simp), add_comm]
  have hQb : Q ≤ b := Nat.lt_succ_iff.mp (p i.succ).isLt
  have hmap : (univ.filter (fun l => β l = i)).map Fin.valEmbedding = Ico P (P + j i) := by
    ext x
    rw [mem_map, mem_Ico]
    constructor
    · rintro ⟨l, hl, rfl⟩
      rw [mem_filter, hβ, Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.coe_castSucc] at hl
      simp only [Fin.valEmbedding_apply]
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, by omega⟩, ?_, rfl⟩
      rw [mem_filter, hβ, Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
      exact ⟨mem_univ _, by simp only; omega, by simp only; omega⟩
  constructor
  · rw [← card_map Fin.valEmbedding, hmap, Nat.card_Ico]; omega
  · have : ∑ l with β l = i, rho n (fun _ => 1) l
        = ∑ x ∈ (univ.filter (fun l => β l = i)).map Fin.valEmbedding, ((n : ℂ) - 2 * (x : ℂ) - 1) := by
      rw [sum_map]; exact sum_congr rfl fun l _ => rho_one_eq n l
    rw [this, hmap, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, sum_range_aff, rho, hPsum]
end GlobalTheory.RhoSum
