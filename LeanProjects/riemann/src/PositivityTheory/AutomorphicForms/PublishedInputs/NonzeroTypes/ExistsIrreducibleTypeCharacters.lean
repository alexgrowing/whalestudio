import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NzOfSteps
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NeedCProps
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GMain
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GEmb
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TypeExNZ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ArtinTransferDecompositionHolds
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.LocalArtinBlockProduct
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TranslationCoordinates
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TwistedSphericalEquivalence
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.DistinctCharacterUnits
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SmoothStabiliserSubgroup
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PArtinIne
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductorBound
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CuspidalSupport2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.DeterminantVector
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PDMul
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PDUnit
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndDetK
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndExt
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Isotypic₂
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacquetFiniteLength2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacquetImage
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.P_Jmul
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PJone
import Mathlib.RepresentationTheory.Maschke
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.MaschkeCompactGroup
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SubrepresentationTransport
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SchurKernelSubmodule
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.InPowAlgebraMap
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PKill
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamBasic
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamLevi
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamUnip
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ParabolicMaximalCompact
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.InPowMono
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ProductIrreducible2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PProdRc
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarInertia
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SphericalOfUnramified
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SphericalUnramified
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Subquotient2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSumList
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorVector
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PTwistRc
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Uniformizer₂
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.UnramifiedTwist
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PUntwistRc
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.MemKCOfRedEq
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.StepV0Stable
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductor
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PTpow
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Iwahori₂
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamMul
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Tensor2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PExGrp
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.LeviEigenvectorMembership
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PJinv
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PNonint
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.IsClosedUnipRad
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacquetKernel
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PTzInj
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SupportProduct

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel UpperTheory.TNZ

namespace UpperTheory.NonzeroTypeTheory

theorem cSteps_all
     :
    CSteps := by
  intro k _ _ _ _
  exact ⟨Grp.step_ccBasic (k := k), Grp.step_unif (k := k), Grp.step_exGrp (k := k), fun n G => ⟨Grp.step_ccBound (G := G), Grp.step_Jone (G := G), Grp.step_Jmul (G := G), Grp.step_Jinv (G := G), Grp.step_KC (G := G), Grp.step_DUnit (G := G), Grp.step_DMul (G := G), Grp.step_lamMul (G := G), Grp.step_lamBasic (G := G), Grp.step_lamUnip (G := G), Grp.step_iwahori (G := G), Grp.step_V0stable (G := G), Grp.step_V0fin (G := G), Grp.leviEigenvector_holds (G := G), Grp.step_PJ (G := G), Grp.step_kill (G := G), Grp.step_nonint (G := G), Grp.step_TzE (G := G), Grp.step_Tpow (G := G), Grp.step_jacKer (G := G), Grp.step_TzInj (G := G), Grp.step_jacImage (G := G), Grp.step_jacFin (G := G), Grp.step_subq (G := G), Grp.step_tensor (G := G), Grp.step_suppProd (G := G)⟩⟩

theorem types_nonzero_level_holds (P : GlobalTheory.Mem.LiteralAutomorphy.LitN)
     : NZ :=
  nz_of_steps P invariantComplement_holds minimalSubrepresentation_holds schurInjective_holds artinTransferDecomposition_holds localArtinCharacterProduct_holds finiteDimensionalTranslation_holds twistedSphericalRepresentative_holds distinctOnInertia_holds smoothVectorsFixed_holds
    (gMain step_detVec step_unrTwist step_sumList step_isotypic step_scalarInertia step_sphOfUnr step_sphUnr step_twistRc
      step_untwistRc step_prodRc step_cuspSupp step_prodIrr step_artinIne)
    (gEmb step_tensorVec step_lamLevi step_parabKO step_indDetK step_indExt) step_artinIne
    (fun L => need_CMain (cSteps_all ) step_lamLevi L) (need_CProps (cSteps_all ))
    (need_Grp (cSteps_all ))

end UpperTheory.NonzeroTypeTheory

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.NonzeroTypeTheory.exists_type_for_residual_rep :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∃ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ :=
  fun P => UpperTheory.NonzeroTypeTheory.typeEx P (UpperTheory.NonzeroTypeTheory.types_nonzero_level_holds P )

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end
