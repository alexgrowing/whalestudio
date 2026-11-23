import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.locBase :
    ∀ (F : Type) [Field F] [NumberField F] (v : Pl F), IsFractionRing (Ov v) (Kv v) ∧ IsAdicComplete (IsLocalRing.maximalIdeal (Ov v)) (Ov v) ∧ Finite (IsLocalRing.ResidueField (Ov v)) ∧ ((2 : 𝓞 F) ∉ v.asIdeal → IsUnit (2 : Ov v)) := by
  intro F _ _ v
  refine ⟨inferInstance, GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v,
    GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v, fun h => ?_⟩
  have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h
  rwa [map_ofNat] at this
