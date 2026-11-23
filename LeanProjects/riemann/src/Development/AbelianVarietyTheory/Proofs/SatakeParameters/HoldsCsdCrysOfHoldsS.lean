import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfUnr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatake
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem holds_csd_crys_of_holdsS (hC : SphericalLevelCondition .csd .crys) : Holds .csd .crys := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw
  intro P AI hT A hAw O _ _ _ Bw hj σ hσ hsph
  have hc := GlobalTheory.Cong.satake_locComp E a π w σ hσ
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred (hc.2.1 hsph)
  exact hC E Ω l ι a ha π χ hs r hr w hw B ((hc.1 B).2 hB) P AI hT A hAw O Bw hj σ hσ hsph

theorem holdsS_good_crys : Inputs → SphericalLevelCondition .csd .crys → SphericalLevelCondition .good .crys := by
  intro hI hC
  have hG := GlobalTheory.CrysTwistBack.holds_good_crys GlobalTheory.automorphicFormsFiniteGL hI.hk (holds_csd_crys_of_holdsS hC)
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw B _
  exact hG E Ω l ι a ha π χ hs r hr w hw

end GlobalTheory.RoadU

end
