import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.WedgeSplitTan
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftedColumnMultidegree
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LatticeCountingFormula

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

theorem canonical_translate_jet_identity (D : Formalism.BasicNotions.D7) : CanonicalTranslateJetIdentity D := by
  intro p f _ O _ _ _ _ S hp5 hf hsq N r K _ _ _ LL B z hK hmono hz P g hg c hpos J
  have H : ColOK LL P.mu c := colOK_of_path LL B hK P c
  refine ⟨column_kernel_components_integral p f LL g hg z P.mu c J, fun m hm i hi => lifted_column_multidegree p f LL g z P.mu c hmono hz J m hm i hi,
    fun g' hg' => lifted_column_order p f (frobCong p f hf) S hsq LL g g' hg hg' z P.mu c H hmono hz hpos J, ?_,
    column_order_le_two_power p (by omega) LL.pos z hmono hz P.mu c hpos⟩
  exact lifted_column_congruence p f S LL g hg z P.mu c hmono hz hpos (SgVanish_of LL P.mu c H)
    (fun J => plTanCol_eq_SgW O LL P.mu c H P.dom J) J

end Formalism.MainNotions.LemmaBAlt
