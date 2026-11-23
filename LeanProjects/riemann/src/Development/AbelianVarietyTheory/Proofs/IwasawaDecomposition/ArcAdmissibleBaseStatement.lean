import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcAdmissibleBase
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_admissible_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O']
    (b : 𝓞 c.F →+* O') (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f →
    ∀ χ χ' : Sp R ⟶ Z.X, Set.range (Out.jK R ≫ χ) ⊆ Set.range Z.j → Set.range (Out.jK R ≫ χ') ⊆ Set.range Z.j →
      χ ≫ Z.s = spMap f ≫ spMap b → χ' ≫ Z.s = spMap f ≫ spMap b → Z.HasArcData a I f u χ → Z.HasArcData a I f u χ' →
      χ = χ' := by
  first | exact @GlobalTheory.ArcUniqueGlobal.eq_of_hasArcData_global | exact GlobalTheory.ArcUniqueGlobal.eq_of_hasArcData_global | (intros; apply GlobalTheory.ArcUniqueGlobal.eq_of_hasArcData_global <;> assumption)
