import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormsBasisInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalZeroIffRationalSubspace
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem iC_principal_injective : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → (R.toCx3 F).zs.InBlock → ∀ t, Function.Injective ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F _hOk hC _hIB t
  have hj : GlobalTheory.QPosCompare.IsForm ((R.toCx3 F).jR t) :=
    GlobalTheory.TwistPlacesObj.isForm_tw _ R.toRealDat.emb0 (GlobalTheory.QPosCompare.isForm_jX hC.base.models t)
  exact GlobalTheory.TwistPlacesObj.lin_injective ((R.toCx3 F).Θ t) hj
    ((A3.A.fam.R t).toF (A3.A.fam.lvl ⊥ 1) ((R.toCx3 F).zs.Z t))
    (BlockDat.toF_injective _ _ _) (fun y => GlobalTheory.TwistPlacesObj.toF_mem _ _ _ y)

end GlobalTheory.PrimIn
