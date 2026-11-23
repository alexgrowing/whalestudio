import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterTrivialOnSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_character_trivial_on_subgroup : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (i : Fin D.R.m) (Kf : Subgroup (GA D (Wc D i))), IsLevelK (Wc D i) (D.host.g 0 * D.host.g 1) Kf → ∀ k ∈ Kf, k ∈ levS (Wc D i) (L.βW i) (L.datWp i L.triv) ∧ Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  first | exact @GlobalTheory.HolRead.PrincLevelSub.mem_levS_and_levChi | exact GlobalTheory.HolRead.PrincLevelSub.mem_levS_and_levChi | (intros; apply GlobalTheory.HolRead.PrincLevelSub.mem_levS_and_levChi <;> assumption)
