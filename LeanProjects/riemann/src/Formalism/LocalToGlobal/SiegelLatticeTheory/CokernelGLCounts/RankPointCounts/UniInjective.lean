import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolOneCOf

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.NGCut.SplitEmbedding

namespace Formalism.L2.SG.NGCut.StabilizerCovolume

section Uni

variable {P : Type} [Fintype P] (ht : P → ℕ)

def IsUni (A : (P → ℂ) →ₗ[ℂ] (P → ℂ)) : Prop :=
  ∀ (x x' : P → ℂ) p, (∀ q, ht q < ht p → x q = x' q) → A x p - x p = A x' p - x' p

theorem uni_low {A : (P → ℂ) →ₗ[ℂ] (P → ℂ)} (hA : IsUni ht A) :
    ∀ n (x x' : P → ℂ), (∀ q, ht q < n → x q = x' q) → ∀ q, ht q < n → A x q = A x' q := by
  intro n x x' h q hq
  have h1 := hA x x' q (fun r hr => h r (lt_trans hr hq))
  rw [h q hq] at h1
  exact sub_left_injective h1

theorem uni_injective {A : (P → ℂ) →ₗ[ℂ] (P → ℂ)} (hA : IsUni ht A) : Function.Injective A := by
  intro x x' hxx
  have key : ∀ n, ∀ q, ht q < n → x q = x' q := by
    intro n
    induction n with
    | zero => intro q hq; exact absurd hq (Nat.not_lt_zero _)
    | succ n ih =>
      intro q hq
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | h
      · exact ih q h
      · have h1 := hA x x' q (fun r hr => ih r (h ▸ hr))
        rw [hxx] at h1
        exact sub_right_injective h1
  funext q
  exact key (ht q + 1) q (Nat.lt_succ_self _)

theorem uni_inv {A : (P → ℂ) →ₗ[ℂ] (P → ℂ)} (hA : IsUni ht A) :
    ∃ B : (P → ℂ) →ₗ[ℂ] (P → ℂ), (∀ x, A (B x) = x) ∧ (∀ x, B (A x) = x) ∧ IsUni ht B := by
  have hinj := uni_injective ht hA
  let e := LinearEquiv.ofInjectiveEndo A hinj
  refine ⟨e.symm.toLinearMap, fun x => e.apply_symm_apply x, fun x => e.symm_apply_apply x, ?_⟩
  have low : ∀ (x x' : P → ℂ) n, (∀ q, ht q < n → A x q = A x' q) → ∀ q, ht q < n → x q = x' q := by
    intro x x' n
    induction n with
    | zero => intro _ q hq; exact absurd hq (Nat.not_lt_zero _)
    | succ n ih =>
      intro hAx q hq
      have ih' := ih (fun r hr => hAx r (Nat.lt_succ_of_lt hr))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | h
      · exact ih' q h
      · have h1 := hA x x' q (fun r hr => ih' r (h ▸ hr))
        rw [hAx q hq] at h1
        exact sub_right_injective h1
  intro y y' p hy
  have e1 : A (e.symm y) = y := e.apply_symm_apply y
  have e2 : A (e.symm y') = y' := e.apply_symm_apply y'
  have hx : ∀ q, ht q < ht p → e.symm y q = e.symm y' q :=
    low _ _ (ht p) (fun q hq => by rw [e1, e2]; exact hy q hq)
  have h1 := hA (e.symm y) (e.symm y') p hx
  rw [e1, e2] at h1
  show e.symm y p - y p = e.symm y' p - y' p
  linear_combination -h1

end Uni

end Formalism.L2.SG.NGCut.StabilizerCovolume
