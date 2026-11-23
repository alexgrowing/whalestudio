import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsDehomogenisationTwistedChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsTwistedSectionsCubeBijective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CstSmoothAndFlat
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecOnFinitePresentationProjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DehomogenisingCompOfSaturating
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexOfNoetherianModel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.Cohom

theorem exists_finite_projective_complex_cechLB : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → Smooth f → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cechLB f M (fun i => nonzeroLocus (s i))), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ) := by
  intro R _ Y f H m s M hH hM hs hf
  have hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V)
      fun i t => SecOnR.mulSec f M t (s i) V := fun V i j t x =>
    SecOn.mulSec_comm (s i) (s j) x
  obtain ⟨R₀, hR₀, C₀, θ, hflat, hfin, hθ⟩ :=
    exists_noetherian_model_grCube (Fin (m + 1)) R (GrSum (hx ⊤)) (GrSum.grading (hx ⊤)) fun i => by
      obtain ⟨haff, r, hr, hsurj⟩ := hs.2 i
      obtain ⟨hri, ε, hε, hker, -⟩ := GlobalTheory.AbLaw.exists_dehom_chart R Y f H m s M hH hM hs hx i r hr
      letI := cstAlgebra f (nonzeroLocus (s i))
      obtain ⟨hfp, hproj⟩ := secOn_finitePresentation_projective Y (tw M H 0) (nonzeroLocus (s i))
        (isLB_tw hM hH 0) haff
      exact ⟨Γ(Y, nonzeroLocus (s i)), inferInstance, cstAlgebra f _, MvPolynomial.aeval r,
        SecOn (tw M H 0) (nonzeroLocus (s i)), inferInstance, inferInstance, ε,
        (cst_smooth_and_flat R Y f _ haff).1 hf, hfp, hproj, hsurj,
        (MvPolynomial.aeval_X r i).trans hri, hε, hker⟩
  obtain ⟨γ, hγ⟩ := GlobalTheory.exists_grCube_twistedSections_hom_secCube_bijective R Y f H m s M hH hM hs hx 0
  let e := secCubeIso f (fun i => nonzeroLocus (s i)) (SecOn.twZeroEquiv hM hH)
    (SecOn.twZeroEquiv_restrict hM hH)
  obtain ⟨K, φ, -, hK, hφ⟩ := exists_finite_projective_complex_of_noetherian_model (Fin (m + 1)) R₀ R
    C₀ (secCube f M fun i => nonzeroLocus (s i)) (θ ≫ γ ≫ e.inv) hflat hfin fun I hI => by
      rw [NatTrans.comp_app, NatTrans.comp_app, ModuleCat.hom_comp, ModuleCat.hom_comp,
        LinearMap.coe_comp, LinearMap.coe_comp]
      exact ((ConcreteCategory.bijective_of_isIso (e.inv.app I)).comp (hγ I)).comp (hθ I hI)
  exact ⟨K, φ, hK, hφ⟩

end GlobalTheory.Cohom
