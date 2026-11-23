import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHubData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepsCuspidal

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem exists_canonical_hubData_with_bounds : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK), _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → ∀ (e' : FamilyRepresentationConstants.RFam D → FamilyRepresentationConstants.RhoFam D → D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (exc : FamilyRepresentationConstants.RhoFam D → Finset ℕ) (I : TwIn D), ∃ X : KillingConditions.HubData D, GlobalTheory.HubX.Canon L HW R X ∧ X.e' = e' X.r X.ρ ∧ X.exc = exc X.ρ ∧ X.I = I ∧ (∀ i, GoodR D.nd i (X.r i)) ∧ (0 ≤ L.etaSz → (X.eta : ℝ) ≤ 2 * L.etaSz) ∧ ∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i := by
  intro hC D L HW R h2 h41 e' exc I
  obtain ⟨r, ρ, h⟩ := GlobalTheory.PtCore.exists_ptFam hC D (_root_.GlobalTheory.T.galoisRepsCusp_of_adm2 D h2) (fun i => (h41 i).1.2)
  have hc := canon_ourX L HW R r ρ (e' r ρ) (exc ρ) I h
  refine ⟨ourX L HW R r ρ (e' r ρ) (exc ρ) I, hc, rfl, rfl, rfl, hc.fam.good, ?_, ?_⟩
  · intro hL
    rw [hc.eta]
    have := Nat.floor_le hL
    linarith
  · intro i
    rw [hc.cB]
    exact le_refl _
end GlobalTheory.HubX
end
