import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRankR

theorem exists_lift_of_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (κ' : GA D (Wc D i)), κ' ∈ levG (Wc D i) (R.βW i) (R.datWp i P) → ∃ g0 : P.H, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0.1 κ' ∧ levChi (Wc D i) (R.βW i) (R.datWp i P) κ' = ((P.chi g0 : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i P κ' hκ
  have hp : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ') ∈ P.H := hκ.2.2
  refine ⟨⟨_, hp⟩, ⟨hκ.1, hκ.2.1, rfl⟩, ?_⟩
  have h2 : ext1 (R.datWp i P).P.H (R.datWp i P).P.chi
      (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ')) = P.chi ⟨_, hp⟩ := extendOne_of_mem _ hp
  unfold levChi levFn
  rw [h2]
  have hs : (R.datWp i P).s = 0 := rfl
  have hQ : (R.datWp i P).Q = ∅ := rfl
  rw [hs, hQ]
  simp

end GlobalTheory.LevelRankR

end
