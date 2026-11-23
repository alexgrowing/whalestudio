import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SstCpOfNoIwahori
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.PureDegreeZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrow7
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TaylorYoshidaSquareIntegrable
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open GlobalTheory.GalCut7
open GlobalTheory GlobalTheory.IwaPkg GlobalTheory.TheRec GlobalTheory.Cong GlobalTheory.UnitaryBC

namespace GlobalTheory.CrysNoMono

theorem crystalline_decompositionGroup_no_monodromy : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω)
    (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) (ρ : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)),
    IsCrysAt P Bw ρ → (wdAt P ι Bw h hj ρ).mono0 := by
  intro E Ω _ _ _ _ _ l _ ι a P w A h O _ _ _ Bw hj ρ hc
  by_cases hr : IsPstAt P Bw ρ
  · exact (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj P ι ρ hr).2 hc.isPotCrysAt
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, trivWD]
    exact WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))

end GlobalTheory.CrysNoMono
