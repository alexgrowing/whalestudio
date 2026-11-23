import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioParts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRootOfSUnitRatioUpToRootOfUnityClosureLawsStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

private theorem list_prod_map_pow_eq {α : Type} (l : List α) (f g : α → ℂ) (n : ℕ) (h : ∀ a, f a ^ n = g a ^ n) :
    (l.map f).prod ^ n = (l.map g).prod ^ n := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, mul_pow, ih, h]

private theorem list_prod_map_ne_zero {α : Type} (l : List α) (f : α → ℂ) (h : ∀ a, f a ≠ 0) :
    (l.map f).prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons]; exact mul_ne_zero (h a) ih

theorem mono_pow_eq {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ)
    (χ χ' : (AE D)ˣ →* Circle) (n : ℕ) (hn : χ ^ n = χ' ^ n) :
    o.mono r e χ ^ n = o.mono r e χ' ^ n := by
  unfold TDat.mono
  apply list_prod_map_pow_eq
  intro i
  simp only [mul_pow, chrPow]
  congr 1
  have key : ∀ μ : (AE D)ˣ →* Circle, ((μ ((o.p i).idele o.q.unit) ^ e i : Circle) : ℂ) ^ n
      = ((((μ ^ n) ((o.p i).idele o.q.unit)) ^ e i : Circle) : ℂ) := by
    intro μ
    rw [MonoidHom.pow_apply, ← Circle.coe_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  rw [key χ, key χ', hn]

theorem mono_ne_zero {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ)
    (χ : (AE D)ˣ →* Circle) (hr : ∀ i, 0 < r i) : o.mono r e χ ≠ 0 := by
  unfold TDat.mono
  apply list_prod_map_ne_zero
  intro i
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast (hr i).ne'
  · exact Circle.coe_ne_zero _

theorem mono_unitRatio : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ) (χ χ' : (AE D)ˣ →* Circle)
    (S : ℕ → Prop), (∀ i, 0 < r i) → (∃ n : ℕ, 0 < n ∧ χ ^ n = χ' ^ n) → UnitRatio S (o.mono r e χ) (o.mono r e χ') := by
  intro D c k _ _ _ _ ι o r e χ χ' S hr ⟨n, hn, hχ⟩
  exact (GlobalTheory.T.isRootOfSUnitRatioUpToRootOfUnity_closure_laws S).2.2.1 _ _ n (mono_ne_zero o r e χ' hr) hn (mono_pow_eq o r e χ χ' n hχ)

end GlobalTheory.SeeSaw
