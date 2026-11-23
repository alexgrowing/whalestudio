import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsGeometricPoint
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.TopAmpSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasisOnAny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsUnimodularSolTwoTorsion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models.FamInh

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Model

theorem isProjOver_powObj {R : Type} [CommRing R] (A : Over (Sp R)) (h : IsProjOver A.hom) :
    ∀ n, IsProjOver (Out.powObj A n).hom
  | 0 => Inhab.isProjOver_id R
  | n + 1 => ProjSpace.isProjOver_pullback h (isProjOver_powObj A h n)

end Model

section Zero

variable {D : Datum H} {n N : ℕ}

open RankZero

end Zero

theorem topAmpExists_iff_topAmpSt : TopAmpExists ↔ GlobalTheory.LN.TopAmpSt := Iff.rfl

theorem topAmpExists_iff_topExists : TopAmpExists ↔ TopExists :=
  ⟨fun h E _ _ _ H D hD Xo n hn => let ⟨J, k, T, hJ, a⟩ := h E H D hD Xo n hn; ⟨J, hJ, T, k, a⟩,
    fun h E _ _ _ H D hD Xo n hn => let ⟨J, hJ, T, k, a⟩ := h E H D hD Xo n hn; ⟨J, k, T, hJ, a⟩⟩

end GlobalTheory.Models.FamInh

end
