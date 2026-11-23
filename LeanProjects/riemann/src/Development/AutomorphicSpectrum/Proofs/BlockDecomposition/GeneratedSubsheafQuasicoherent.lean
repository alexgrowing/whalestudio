import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem isQuasicoherent_imageSubobject {X : Scheme.{0}} {A B : X.Modules}
    (hA : A.IsQuasicoherent) (hB : B.IsQuasicoherent) (f : A ⟶ B) :
    (imageSubobject f : X.Modules).IsQuasicoherent := by
  haveI := hA
  haveI := hB
  have hK : (kernel (cokernel.π f)).IsQuasicoherent := inferInstance
  exact GlobalTheory.QCoh.isQuasicoherent_of_iso
    (Abelian.imageIsoImage f ≪≫ (imageSubobjectIso f).symm)

theorem isQuasicoherent_genSub : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)),
    (genSub hH n b : X.Modules).IsQuasicoherent := by
  intro X H hH P hP n b
  have hO : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent := inferInstance
  have hS : (GlobalTheory.twistZ (SheafOfModules.unit X.ringCatSheaf) H (-n)).IsQuasicoherent :=
    GlobalTheory.Twist.isQuasicoherent_twist (F := SheafOfModules.unit X.ringCatSheaf)
      (GlobalTheory.Twist.isLB_lbZPow hH (-n))
  exact isQuasicoherent_imageSubobject hS hP _

end GlobalTheory.CompanionTheory.GE.TwGen
