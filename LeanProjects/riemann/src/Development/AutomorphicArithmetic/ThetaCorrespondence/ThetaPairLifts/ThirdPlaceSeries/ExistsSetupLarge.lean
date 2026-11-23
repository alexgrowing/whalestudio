import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHubDataFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHubData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink
theorem exists_setup_large_alt : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C C₂ : ℝ) (CT : ℕ), TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) → ∀ exc : Finset ℕ, ∃ (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)), X.exc = exc ∧ _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt (Fm.L x i) ∧ _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ := by
  intro hP eps Fm C C₂ CT hTw hF
  obtain ⟨i0⟩ := Fm.Ix_zero
  have he : 0 < eps := Fm.L_eps 0 i0 ▸ (Fm.L 0 i0).sc.eps_pos
  obtain ⟨xa, hxa⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) he
  obtain ⟨xb, hxb⟩ := GlobalTheory.T.specialPrimes_small_along_family Fm 1 le_rfl
  obtain ⟨xc, hxc⟩ := hTw
  refine ⟨max xa (max xb xc), fun x hx hx1 i hsha exc => ?_⟩
  have hxa' : xa ≤ x := le_trans (le_max_left _ _) hx
  have hxb' : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxc' : xc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, N0, S, hgood⟩ := hxc x hxc' hx1 i
  obtain ⟨hfa, -⟩ := hF x hx1 i
  obtain ⟨HW, F, ⟨Cm⟩⟩ := GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze hP.bs (Fm.D x i)
  have hCLw : (Fm.params x hx1 i).CLw ≤ Fm.PK.getD 7 0 := by
    rw [← Fm.params_K x hx1 i]
    exact le_refl _
  have hsx : xa ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx1]; exact hxa'
  obtain ⟨hpar, hpar67⟩ := hxa (Fm.D x i) (Fm.L x i) (Fm.params x hx1 i) (Fm.L_eps x i) hCLw hsx
  obtain ⟨X, hcan, -, hexc, hI, -⟩ := _root_.GlobalTheory.HubX.exists_canonical_hubData_with_bounds GlobalTheory.Published.cheb_holds (Fm.D x i) (Fm.L x i) HW (rowC C₂)
    hfa.adm.1.1.2.2.2.1 hfa.Conclusion1.1 (fun _ _ _ _ => 0) (fun _ => exc) ⟨twE Fm x hx1 i, N0, S⟩
  obtain ⟨-, hbig, hsplit, -⟩ := hxb x hxb' hx1 i
  have hrow : GlobalTheory.PtCore.GoodPtRow (Fm.D x i) :=
    GlobalTheory.Proof.LocalGlobalAssembly.main _ hfa.adm.1.1.1 hfa.Conclusion1.2.2 hfa.Conclusion2.2.2
  have h6 := GlobalTheory.JointSix.main GlobalTheory.Published.cheb_holds (Fm.D x i) (Fm.ex x hx1 i).nch X.r X.ρ hcan.fam hfa.nct hfa.trip
    hfa.same hrow (GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred _ hfa.rhoBar)
  have hkill : KillingConditions.KillAt X.ρ := GlobalTheory.T.chosenTwist_annihilates_selmerGroups (Fm.D x i) (Fm.ex x hx1 i).nch X.I X.ρ hfa.nct (hI ▸ hgood) h6
  exact ⟨HW, F, Cm, X, hexc, hfa.admJ _ hpar, ⟨hfa, hcan, hpar, hpar67, hbig, hsplit, hkill, hsha⟩⟩
end GlobalTheory.NLink
end
