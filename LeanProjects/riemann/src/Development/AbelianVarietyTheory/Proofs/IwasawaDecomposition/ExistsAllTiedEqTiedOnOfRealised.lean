import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PetIntOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumNormEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureLeOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypAddOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicWeilRepresentationWithRulesExistsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealPlaceRecordTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilOnEqExOfKnownTheorem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftAutEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqualRankSplittingCharsAdmissibleMulRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealisedE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem exists_allTied_eqTied_on_of_realised {D : D7} (ht : TypAdd D)
    (hW : ∀ ψ, IsStdChar D ψ (-1) → ∃ Wf : WeilFun D ψ, Wf.EqRank) (hT : Nonempty (Tow D)) (hX : RealisedExE D)
    (hA : ∃ A : ProvA, ProvisionCompatibility D A) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E)
    (U : Set D.what₂.Tup) (hr : RealTied D) (hR : (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y))) :
    ∃ X : ThetaX D, X.TieIo ∧ (∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j,
      X.petY μ j ((X.rowAF μ j x : X.cusp _) : X.AF _) (X.rowAF μ j y) = inner ℂ x y) ∧
      ∃ (A : ProvA) (a : AllTied D X A), WeilThetaCompatibility a.W ∧
      ∀ (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Tp.xi = xi →
        ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, Formalism.IndefR.Links.ChrEq (a.T.eChr c) (H.eChr c) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.StdAdelicChar.existsUnique_isStdChar D (-1) (Or.inr rfl)
  obtain ⟨Wf, hE⟩ := hW ψ hψ
  obtain ⟨Tw⟩ := hT
  obtain ⟨Rc, hc, hio, hi⟩ := hR θ hθ ψ hψ Wf
  obtain ⟨X, T, W, B, rfl, h⟩ := hX θ hθ ψ hψ Wf hE Tw Rc
  obtain ⟨A, hA⟩ := hA
  obtain ⟨K, -⟩ := h.kfin
  refine ⟨X, h.tieIo hio, fun μ hμ j hj x y => ?_, A, ⟨T, h.afTiedSm, h.typTied ht, W, h.weilUnrTied, K, h.phiUp, B, hr, hA⟩,
    h.eqTied, fun nch Tp e => ?_⟩
  · obtain ⟨⟨m, hm⟩, h2⟩ := hi μ hμ j hj x y
    have e := T.pet _ (D.sp.Y_sig j) m.1 m.2 hm (X.rowAF μ j x) (X.rowAF μ j y)
    unfold ThetaX.petY
    rw [e, (h2 m hm).2, h.row, h.row, h.mY, ← h.petC_eq]
    simp only [ThetaTied.petC, Complex.ofReal_mul, mul_assoc]
  · exact GlobalTheory.TowerCharRead.exists_thetaChrTied D C nch Tp X T (e ▸ h.chrRead hc)

theorem exists_allTied_eqTied_on : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup), RealTied D → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) → ∃ X : ThetaX D, X.TieIo ∧ (∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, X.petY μ j ((X.rowAF μ j x : X.cusp _) : X.AF _) (X.rowAF μ j y) = inner ℂ x y) ∧ ∃ (A : ProvA) (a : AllTied D X A), WeilThetaCompatibility a.W ∧ ∀ (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Tp.xi = xi → ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, Formalism.IndefR.Links.ChrEq (a.T.eChr c) (H.eChr c) := by
  intro hW hC hex huniq hds D C xi U hr hR
  exact exists_allTied_eqTied_on_of_realised (GlobalTheory.TypeSum.typAdd_of_discreteSeries D hex huniq)
    (GlobalTheory.Mem.WeilEqRank.exists_weilFun_eqRank D (GlobalTheory.T.adelicWeilRepresentation_with_rules_exists hW D) (GlobalTheory.Mem.WeilEqRank.weilOnEqEx_of_weilRepresentation hW D)
      (GlobalTheory.Mem.WeilTwist.weilTwEq D))
    ((GlobalTheory.TowerSpaces.exists_tow D).elim fun Tw _ => ⟨Tw⟩)
    (GlobalTheory.Mem.TrueRecordEq.exists_realisedE D (petInt_of_cuspRapidDecay hC D) (GlobalTheory.Mem.TopIntegrand.topInt hC D)
      (GlobalTheory.Mem.BesselIntegrable.besInt hC D) (GlobalTheory.Mem.Lift.liftAut hC D) (GlobalTheory.Mem.Lift.liftAutEq hC D))
    (GlobalTheory.exists_realPlace_record_tied hds D) C xi U hr hR

end GlobalTheory.Mem.Th
