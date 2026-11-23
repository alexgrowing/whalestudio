import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LmatMemR

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG2

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem lmat_low {l ρ : Formalism.L2.SG.LsDatumB.MatP D p} (hl0 : ∀ a b, a < b → l a b = 0) (hl1 : ∀ a, l a a = 1)
    (hρ0 : ∀ a b, b < a → ρ a b = 0) (hρ1 : ∀ a, ρ a a = 1) :
    (∀ a b, a < b → lmat Z p g l ρ a b = 0) ∧ ∀ a, lmat Z p g l ρ a a = 1 := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · simp only [lmat, Matrix.of_apply, hl0 a b h, hρ0 b a h, map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [show ((0 : (D.s.atP p).Fp), (0 : (D.s.atP p).Fp)) = 0 from rfl, map_zero]
  · simp only [lmat, Matrix.of_apply, hl1 a, hρ1 a, map_one, Prod.fst_one, Prod.snd_one]
    rw [show ((1 : (D.s.atP p).Fp), (1 : (D.s.atP p).Fp)) = 1 from rfl, map_one]

theorem corner_fix {L R C : Formalism.L2.SG.LsDatumB.MatP D p} (hL0 : ∀ a b, a < b → L a b = 0) (hL1 : ∀ a, L a a = 1)
    (hR0 : ∀ a b, b < a → R a b = 0) (hR1 : ∀ a, R a a = 1)
    (hC : ∀ a b, ¬ (a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS) → C a b = 0) : L * C * R = C := by
  have hLl : ∀ a, L a (Fin.last D.R.rS) = if a = Fin.last D.R.rS then 1 else 0 := by
    intro a
    split_ifs with h
    · subst h; exact hL1 _
    · exact hL0 a _ (lt_of_le_of_ne (Fin.le_last a) h)
  have hRl : ∀ b, R (Fin.last D.R.rS) b = if b = Fin.last D.R.rS then 1 else 0 := by
    intro b
    split_ifs with h
    · subst h; exact hR1 _
    · exact hR0 _ b (lt_of_le_of_ne (Fin.le_last b) h)
  ext a b
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last D.R.rS) (fun d _ hd => by
      rw [Finset.sum_eq_zero (fun c _ => by rw [hC c d (fun h => hd h.2), mul_zero]), zero_mul]) (by simp),
    Finset.sum_eq_single (Fin.last D.R.rS) (fun c _ hc => by rw [hC c _ (fun h => hc h.1), mul_zero]) (by simp),
    hLl a, hRl b]
  by_cases ha : a = Fin.last D.R.rS <;> by_cases hb : b = Fin.last D.R.rS
  · subst ha; subst hb; simp
  · rw [if_neg hb, mul_zero, hC a b (fun h => hb h.2)]
  · rw [if_neg ha, zero_mul, zero_mul, hC a b (fun h => ha h.1)]
  · rw [if_neg ha, zero_mul, zero_mul, hC a b (fun h => ha h.1)]

end ModeG2

end Formalism.L2.SG.Pf.FibQ
