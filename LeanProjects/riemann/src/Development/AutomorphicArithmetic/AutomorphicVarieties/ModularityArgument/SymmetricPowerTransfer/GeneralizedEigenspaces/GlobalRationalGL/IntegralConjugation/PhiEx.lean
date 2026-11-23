import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.phiEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], ∃ φ : ∀ (v : Pl (Lp L)) (w : Plc L), un w = v → Kv v →+* Kw w, (∀ v w h, Continuous (φ v w h)) ∧ ∀ v w h (a : Lp L), φ v w h (cv v a) = algebraMap L (Kw w) (algebraMap (Lp L) L a) := by
  intro L _ _ _
  have hlo : ∀ (v : Pl (Lp L)) (w : Plc L), un w = v → w.asIdeal.LiesOver v.asIdeal := by
    intro v w h
    subst h
    exact ⟨rfl⟩
  refine ⟨fun v w h => @GroundTheory.Global.SemiLocal.completionMap _ _ _ _ _ _ _ v w (hlo v w h), ?_, ?_⟩
  · intro v w h
    exact @GroundTheory.Global.SemiLocal.continuous_completionMap _ _ _ _ _ _ _ v w (hlo v w h)
  · intro v w h a
    have e := @GroundTheory.Global.SemiLocal.completionMap_algebraMap _ _ _ _ _ _ _ v w (hlo v w h) a
    simp only [cv]
    rw [e]
    exact IsScalarTower.algebraMap_apply (Lp L) L _ a
