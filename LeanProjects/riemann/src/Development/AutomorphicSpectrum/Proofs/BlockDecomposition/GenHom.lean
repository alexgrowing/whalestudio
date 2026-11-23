import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.TwGen

variable {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X}

def genHom (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    GlobalTheory.twistZ (SheafOfModules.unit X.ringCatSheaf) H (-n) ⟶ P :=
  GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom b) ≫
    (GlobalTheory.Twist.twistZAddIso P hH (add_neg_cancel n)).hom ≫ (GlobalTheory.Twist.twistZZeroIso P hH).inv

def genSub (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)) : Subobject P :=
  imageSubobject (genHom hH n b)

end GlobalTheory.CompanionTheory.GE.TwGen
