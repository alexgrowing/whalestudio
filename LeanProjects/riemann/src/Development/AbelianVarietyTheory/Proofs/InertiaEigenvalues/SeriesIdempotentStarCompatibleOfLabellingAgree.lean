import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootsMinpolyPhi
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.GoodTypes

theorem seriesConj_of_labTie : Green → ∀ (D : D7) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L →
    GlobalTheory.GoodTypes.SeriesConj D :=
  fun hG D L hL k f hf =>
    GlobalTheory.GLq.GalSer.eSer_galois hG D ((eSerTie_iff D).2 ⟨L, hL⟩) starRingAut k f hf

end GlobalTheory.GoodTypes
