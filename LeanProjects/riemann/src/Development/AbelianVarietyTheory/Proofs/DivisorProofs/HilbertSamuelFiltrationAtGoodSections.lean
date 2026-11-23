import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubPtsIffOfToBaseEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefBigBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilMonoOfKerRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedSectionChartCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefBigSecondBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesSpecialisedFormProdLinearFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelSectionShiftCommSingleMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelSectionBaseChangePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelDegreeZeroResiduesRangeEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotFilTotSymKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelFiltrationSymbolMonomialProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelVanishingFiltrationDeepestStepSpanStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem flatAt_of_simpleAt : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ →
    ∀ (δ : ℕ) (f : MvPolynomial (Fin (X.D + 1) × Fin X.N) F) (Q : MvPolynomial (Fin X.D × Fin X.N) F),
      (∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E),
        aeval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → SimpleAt X.toTuple δ f E s) →
      ∀ s : Fin X.D → Fin X.N → F, eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → (sysOf X Λ₀).FlatAt δ f s := by
  intro hQ F _ _ X Λ₀ hX δ f Q hS s hs
  have hF : SimpleAt X.toTuple δ f F s := hS F s (by simpa [MvPolynomial.coe_aeval_eq_eval] using hs)
  obtain ⟨E, iE, nE, iFE, iEE, htow, hsp⟩ := GlobalTheory.HSCore.exists_split F X.toTuple F s hF.good
  have heq : (fun i k => @algebraMap F E _ _ iEE (s i k)) = fun i k => @algebraMap F E _ _ iFE (s i k) := by
    funext i k
    rw [@IsScalarTower.algebraMap_apply F F E _ _ _ _ iEE iFE htow (s i k)]
    rfl
  rw [heq] at hsp
  clear heq htow iEE
  have hval : aeval (fun p : Fin X.D × Fin X.N => algebraMap F E (s p.1 p.2)) Q =
      algebraMap F E (eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q) := by
    exact (MvPolynomial.eval₂_comp_left (algebraMap F E) (RingHom.id F) _ Q).symm
  have hSE : SimpleAt X.toTuple δ f E (fun i k => algebraMap F E (s i k)) :=
    hS E _ (by rw [hval]; exact (map_ne_zero _).2 hs)
  have hgood : (X.baseChange E).IsGood (fun i k => algebraMap F E (s i k)) := Geo.isGood_baseChange_iff.2 hSE.good
  obtain ⟨Co, c, hc, hspec⟩ := GlobalTheory.T.exists_coordinates_specialisedForm_prod_linearForms F X.toGeo E _ hgood δ f hsp hSE
  have hnef₂ := nef_big_second_baseChange F X E hX.nef₂ hX.big₂
  have hnefA := GlobalTheory.HSCore.nef_big_baseChange F X E hX.nef hX.big
  have hms : (X.baseChange E).MulStable :=
    (GlobalTheory.HilbertSamuel.Data.complexify_statement F X (fun _ => X.beta) hX.totallyComplex
      (fun _ => one_pos.trans_le X.one_le_beta) hX.mulStable hX.mulBound).2 E
  have hFM : FilMono := GlobalTheory.HSCore.filMono_of_kerRes (GlobalTheory.HSKerRes.kerRes hQ)
  obtain ⟨hind, hmul, hspan⟩ := GlobalTheory.T.hilbertSamuelSectionBaseChange_properties F X Λ₀ E
  obtain ⟨hcomm, -, -⟩ := GlobalTheory.T.hilbertSamuelSectionShift_comm_single_monomial E (X.toGeo.baseChange E)
  have honto := GlobalTheory.T.hilbertSamuelDegreeZeroResidues_range_eq_top hQ E (X.baseChange E) _ hgood δ Co hnef₂.1 hnef₂.2
  have hker := totFil_totSym_ker E (X.baseChange E) _ hgood δ Co
  have hmono := GlobalTheory.T.hilbertSamuelFiltrationSymbol_monomial_product E (X.baseChange E) _ hgood δ Co hms
  have hdiv := GlobalTheory.T.hilbertSamuelVanishingFiltration_deepest_step_span hFM E (X.baseChange E) _ hgood hnefA.1 hnefA.2 hms
  let Φ : (sysOf X Λ₀).Flat E (Tot (X.toGeo.baseChange E)) (fun i k => algebraMap F E (s i k)) δ :=
    { ι := totExt X.toGeo E
      indep := hind
      mul := shift (X.toGeo.baseChange E)
      comm := hcomm
      mul_ι := hmul
      y := Co.y
      y_ne := Co.y_ne
      res := totRes (X := X.baseChange E) Co
      onto := by rw [hspan 0]; exact honto
      U := totFil (X.baseChange E) (fun i k => algebraMap F E (s i k))
      sym := totSym (X := X.baseChange E) Co
      le := fun a ha => (hker a ha).1
      ker := fun a ha => (hker a ha).2
      mono := fun a ha α l m hm => hmono a ha α l m (by rw [hspan 0] at hm; exact hm)
      div := by rw [hspan]; exact hdiv }
  exact ⟨E, Tot (X.toGeo.baseChange E), inferInstance, inferInstance, inferInstance, inferInstance, Φ, c, hc, hspec⟩

end GlobalTheory.HSShort
