import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFiniteOfHcFinite

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevelSmooth

theorem level_open_compact_smooth (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsOpen (((lev D.sp.cm V.gram β L).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
    IsCompact ((levA V (lev D.sp.cm V.gram β L) : Subgroup (GA D V)) : Set (GA D V)) ∧
    levS V β L ⊆ (GfC V : Set (GA D V)) ∧
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ levS V β L ∧ levChi V β L k = 1 :=
  ⟨GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L, GlobalTheory.ParahoricCompact.isCompact_levG V β L, fun _ hk => hk.1,
    GlobalTheory.GoodFiniteDim.exists_open_subgroup V β L⟩

end GlobalTheory.Mem.LevelSmooth
