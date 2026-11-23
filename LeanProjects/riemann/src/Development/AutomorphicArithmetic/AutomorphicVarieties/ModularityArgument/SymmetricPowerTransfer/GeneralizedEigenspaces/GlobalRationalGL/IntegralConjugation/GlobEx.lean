import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsAnti

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.globEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], ∃ (Δ : Lp L) (e : Lsq (Lp L) Δ ≃+* L), (∀ x, e (star x) = IsCMField.complexConj L (e x)) ∧ (∀ a : Lp L, e (algebraMap _ _ a) = algebraMap (Lp L) L a) ∧ ∀ σ : Lp L →+* ℝ, σ Δ < 0 :=
  _root_.UpperTheory.Reformulated.B.Qh37.globEx
