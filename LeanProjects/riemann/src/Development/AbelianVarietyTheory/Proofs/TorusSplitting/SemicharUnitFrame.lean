import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Semichar
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AhFrameFactorEqNegOnePowRiemannForm

set_option autoImplicit false

namespace GlobalTheory

theorem semichar_unit_frame : ReciprocityTheory.ChartRestriction.G.PullbackSections.PPSemicharSt := by
  intro E _ _ _ H Dw l Xo c σ r U _ k x W Wu _ a
  have hF : GlobalTheory.EtaAn.AHFrame W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr :=
    ⟨Wu.herm, Wu.pos, Wu.c1, Wu.c2, Wu.c3, Wu.c4, fun j hj => by
      rw [← W.pt]; exact Wu.c5 j hj, Wu.c6⟩
  have h : Wu.χl (W.Pm a) =
      ((Int.negOnePow ((W.F.Di (W.ik k)).EF a (H.w0 • a)) : ℤˣ) : ℤ) :=
    GlobalTheory.ahFrame_factor_eq_negOnePow E H Dw l Xo _ _ _ W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr W.per hF a
  rw [h, Int.cast_negOnePow]

end GlobalTheory
