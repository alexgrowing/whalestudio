import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.MainTerm

theorem toW_same {C : Type} [Field C] {I : Fin 2 → Type} (g : Fin 2) (u : I g → C) (x : I g) :
    toW g u ⟨g, x⟩ = u x := by
  simp [toW]

theorem toW_other {C : Type} [Field C] {I : Fin 2 → Type} {g g' : Fin 2} (h : g' ≠ g) (u : I g → C)
    (x : I g') : toW g u ⟨g', x⟩ = 0 := by
  simp [toW, h]

theorem hPullW_upG {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (g : Fin 2) (F : MvPowerSeries (I g) C) (a : ι → WV I → C)
    (b : ι' → WV I → C) :
    hPullW (upG g F) a b = MvPowerSeries.subst (fun x : I g =>
      (∑ c, a c ⟨g, x⟩ • MvPowerSeries.X (Sum.inl c) + ∑ c, b c ⟨g, x⟩ • MvPowerSeries.X (Sum.inr c) :
        MvPowerSeries (ι ⊕ ι') C)) F := by
  have hb : MvPowerSeries.HasSubst (fun w : WV I =>
      (∑ c, a c w • MvPowerSeries.X (Sum.inl c) + ∑ c, b c w • MvPowerSeries.X (Sum.inr c) :
        MvPowerSeries (ι ⊕ ι') C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  have ha : MvPowerSeries.HasSubst (fun x : I g => (MvPowerSeries.X ⟨g, x⟩ : MvPowerSeries (WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold hPullW upG
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext x
  rw [MvPowerSeries.subst_X hb]

theorem rename_linPull {C : Type} [Field C] {σ ι τ : Type} [Fintype σ] [Fintype ι] (f : ι → τ)
    (e : ι → σ → C) (F : MvPowerSeries σ C) :
    MvPowerSeries.rename f (linPull e F) = MvPowerSeries.subst (fun x : σ =>
      (∑ c, e c x • MvPowerSeries.X (f c) : MvPowerSeries τ C)) F := by
  have ha : MvPowerSeries.HasSubst (fun x : σ =>
      (∑ c : ι, e c x • MvPowerSeries.X c : MvPowerSeries ι C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold linPull
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply ha (MvPowerSeries.HasSubst.X_comp f)]
  congr 1
  funext x
  rw [← MvPowerSeries.rename_eq_subst]
  simp

theorem hPullW_upG_toW : ∀ (C : Type) [Field C] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (g : Fin 2) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ F : MvPowerSeries (I g) C, hPullW (upG g F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inl (linPull e F)) ∧ ∀ F : MvPowerSeries (I (1 - g)) C, hPullW (upG (1 - g) F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inr (linPull v' F) := by
  intro C _ I _ g ι ι' _ _ e v'
  have h : g ≠ 1 - g := by fin_cases g <;> decide
  refine ⟨fun F => ?_, fun F => ?_⟩
  · rw [hPullW_upG, rename_linPull]
    simp [toW_same, toW_other h]
  · rw [hPullW_upG, rename_linPull]
    simp [toW_same, toW_other h.symm]

end GlobalTheory.MainTerm
