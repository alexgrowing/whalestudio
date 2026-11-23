import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.SplitOfDecAlt
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

open GroundTheory.Global.SemiLocal in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.splitOfDec :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.SplitOfDec := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ v h w
  haveI : Module.Finite K M := Module.Finite.of_restrictScalars_finite ℚ K M
  haveI : Algebra.IsAlgebraic M Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w.1
  have hv : IsPlaceOver A v := fun x => by
    rw [IsScalarTower.algebraMap_apply K M Ω, w.2.over]
    exact hA (algebraMap (𝓞 K) (𝓞 M) x)
  obtain ⟨he, hf⟩ := GlobalTheory.PlaceIsoDec.ramificationIdx_eq_one_and_inertiaDeg_eq_one (F := K) (K := M) (L := M) hv hA hA
    (fun s hs => ⟨{ s.toRingEquiv with commutes' := h A hv s hs }, AlgEquiv.ext fun _ => rfl⟩)
  have hr := finrank_eq_ramificationIdx_mul_inertiaDeg M v w.1
  rw [he, hf] at hr
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hr).2
