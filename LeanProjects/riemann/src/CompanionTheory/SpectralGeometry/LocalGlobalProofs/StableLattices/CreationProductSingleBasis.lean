import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Chains

theorem cre_single {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (f : Pos n) (S : Finset (Pos n)) (w : V)
    (h : f ∉ S) :
    (cre f : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V) =
      CompanionTheory.D.LK.sg f (insert f S) • (Pi.single (insert f S) w : Cn n V) := by
  funext A
  show (if f ∈ A then CompanionTheory.D.LK.sg f A • (Pi.single S w : Cn n V) (A.erase f) else 0) = _
  by_cases hA : A = insert f S
  · subst hA
    rw [if_pos (Finset.mem_insert_self f S), Finset.erase_insert h]
    simp [Pi.single_apply]
  · have hr : (CompanionTheory.D.LK.sg f (insert f S) • (Pi.single (insert f S) w : Cn n V)) A = 0 := by
      simp [Pi.single_apply, hA]
    rw [hr]
    split_ifs with hf
    · have hne : A.erase f ≠ S := fun he => hA (by rw [← he, Finset.insert_erase hf])
      simp [Pi.single_apply, hne]
    · rfl

theorem sg_ne_zero {n : ℕ} (f : Pos n) (A : Finset (Pos n)) : CompanionTheory.D.LK.sg f A ≠ 0 := by
  delta CompanionTheory.D.LK.sg
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

theorem prod_cre_single : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (l : List (Pos n)) (S : Finset (Pos n)) (w : V),
    l.Nodup → (∀ i ∈ l, i ∉ S) → ∃ c : ℂ, c ≠ 0 ∧
      ((l.map cre).prod : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V) = c • (Pi.single (S ∪ l.toFinset) w : Cn n V) := by
  intro n V _ _ l S w
  induction l with
  | nil =>
    intro _ _
    refine ⟨1, one_ne_zero, ?_⟩
    simp
  | cons a l ih =>
    intro hnd hS
    obtain ⟨c, hc, hcl⟩ := ih hnd.of_cons (fun i hi => hS i (by simp [hi]))
    have ha : a ∉ S ∪ l.toFinset := by
      rw [Finset.mem_union, not_or, List.mem_toFinset]
      exact ⟨hS a (by simp), (List.nodup_cons.1 hnd).1⟩
    refine ⟨c * CompanionTheory.D.LK.sg a (insert a (S ∪ l.toFinset)), mul_ne_zero hc (sg_ne_zero _ _), ?_⟩
    rw [List.map_cons, List.prod_cons]
    show cre a (((l.map cre).prod : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V)) = _
    rw [hcl, map_smul, cre_single a _ w ha, smul_smul, List.toFinset_cons, Finset.union_insert]

end GlobalTheory.CompanionTheory.Chains
