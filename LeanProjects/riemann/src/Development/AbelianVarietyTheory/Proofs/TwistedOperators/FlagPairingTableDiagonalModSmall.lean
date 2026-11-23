import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjRead

theorem flagV_pair_table : ∀ {M A : Type} [Zero M] [Ring A] (p : M → M → A) (sm : A → Prop) (ρ k n : ℕ), n = 2 * ρ + k + 1 → ∀ (e f : Fin ρ → M) (b b' : Fin k → M) (z : M), PairTable p sm e f b b' z → ∀ a c : Fin n, sm (p (flagV ρ k n f e b' z a) (flagV ρ k n e f b z c) - if a = c then sgnD ρ k a else 0) := by
  intro M A _ _ p sm ρ k n hn e f b b' z hT a c
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16⟩ := hT
  subst hn
  have ha := a.isLt
  have hc := c.isLt
  have d1 : ∀ (x y : Fin ρ), x.1 = y.1 → sm (p (f x) (e y) - 1) := by
    intro x y h; have := t1 x y; rwa [if_pos (Fin.ext h)] at this
  have o1 : ∀ (x y : Fin ρ), x.1 ≠ y.1 → sm (p (f x) (e y) - 0) := by
    intro x y h; have := t1 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d6 : ∀ (x y : Fin k), x.1 = y.1 → sm (p (b' x) (b y) - 1) := by
    intro x y h; have := t6 x y; rwa [if_pos (Fin.ext h)] at this
  have o6 : ∀ (x y : Fin k), x.1 ≠ y.1 → sm (p (b' x) (b y) - 0) := by
    intro x y h; have := t6 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d16 : ∀ (x y : Fin ρ), x.1 = y.1 → sm (p (e x) (f y) - 1) := by
    intro x y h; have := t16 x y; rwa [if_pos (Fin.ext h)] at this
  have o16 : ∀ (x y : Fin ρ), x.1 ≠ y.1 → sm (p (e x) (f y) - 0) := by
    intro x y h; have := t16 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d11 : sm (p z z - -1) := by rw [sub_neg_eq_add]; exact t11
  by_cases hac : a.1 = c.1
  · rw [if_pos (Fin.ext hac)]
    unfold flagV sgnD
    split_ifs <;> first
      | omega
      | exact d11
      | exact d1 _ _ (by dsimp only; omega)
      | exact d6 _ _ (by dsimp only; omega)
      | exact d16 _ _ (by dsimp only; omega)
  · rw [if_neg (fun hh => hac (congrArg Fin.val hh))]
    unfold flagV
    split_ifs <;> first
      | omega
      | exact o1 _ _ (by dsimp only; omega)
      | exact o6 _ _ (by dsimp only; omega)
      | exact o16 _ _ (by dsimp only; omega)
      | (rw [sub_zero]; first
          | exact t2 _ _ | exact t3 _ | exact t4 _ _ | exact t5 _ _ | exact t7 _ | exact t8 _ _
          | exact t9 _ | exact t10 _ | exact t12 _ | exact t13 _ _ | exact t14 _ _ | exact t15 _)

end GlobalTheory.SeeConjRead
