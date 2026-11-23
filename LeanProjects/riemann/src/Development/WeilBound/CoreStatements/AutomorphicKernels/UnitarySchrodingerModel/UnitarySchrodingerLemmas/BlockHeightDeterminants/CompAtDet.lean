import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.BlockHeightDeterminants.HWInfA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwsHeight

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC NumberField IsDedekindDomain

variable {D : D7}

theorem prod_absEw {θ : InfFam D} (hθ : IsInfFam θ) (x : (AE D)ˣ) :
    ((∏ w' : InfinitePlace D.host.F, absEw D.host.F D.host.E w' (unitInf D.host.F D.host.E w' x) : ℝ≥0) : ℝ) =
      ∏ τ, ‖θ τ (infPart D (x : AE D))‖ ^ 2 := by
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  haveI := hcm.1
  have hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (unitInf D.host.F D.host.E _ x) = ‖θ τ (infPart D (x : AE D))‖₊ ^ 2 := by
    intro τ
    let t' : GlobalTheory.AdelicU.EmbOver D.host.E (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) :=
      ⟨tauE D τ, (InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm⟩
    rw [absEw_eq_sq hcm t', GlobalTheory.AutFunCompare.isInfEmb_unique _ _ _ (hθ τ) (GlobalTheory.AdelicU.isInfEmb_infProj t')]
    exact congrArg (fun z : ℂ => ‖z‖₊ ^ 2) (GlobalTheory.HalfModTorus.compInf_eq _ t' _)
  rw [← (GlobalTheory.CMTypePlaces.places_bijective D).prod_comp
    (fun w => absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x))]
  simp only [hw]
  push_cast
  rfl

theorem compAt_det (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (a : GL (Fin n) (AE D)) :
    θ τ (infPart D ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D)) = (compAt θ τ a.1).det := by
  change ((θ τ).comp (infPart D)) a.1.det = _
  rw [RingHom.map_det]
  rfl

theorem hwInf : PositivityTheory.PfSWUS.SwFockk.HWInf := by
  intro D n θ hθ w hw nb hnb b p k hp hk hwk a ha
  obtain ⟨m, u, b0, rfl, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hp a ha
  have hloc : ∀ τ, ‖(compAt θ τ a.1).det‖ ^ 2 * (1 + compAt θ τ b.1 * compAt θ τ b.1).det.re = 1 := by
    intro τ
    have e : compAt θ τ (mat w * mat (nb b)) = compAt θ τ (mat m * mat u * mat k) := by
      have := congrArg (fun g => compAt θ τ (mat g)) hwk
      exact this
    rw [compAt_mul, compAt_mul, compAt_mul, hw, hnb b, hm, hu] at e
    simp only [component_block_matrix, compAt_zero, compAt_one, compAt_neg, GlobalTheory.VacKInf.LeviFix.compAt_adj' hθ] at e
    refine local_det (compAt θ τ a.1) (compAt θ τ (a⁻¹).1) (compAt θ τ b.1) (compAt θ τ b0) (compAt θ τ (mat k))
      (compAt_K_unitary θ hθ n k hk τ) ?_ ?_ e
    · rw [← compAt_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, compAt_one]
    · have hb : adj b.1 = b.1 := b.2
      rw [← GlobalTheory.VacKInf.LeviFix.compAt_adj' hθ, hb]
  rw [prod_absEw hθ]
  unfold PositivityTheory.SiegelWeilFormula.Gen.nuInf
  have hm' : ∀ τ, (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) = compAt θ τ b.1 := fun τ => by ext i j; rfl
  simp only [inv_one, Units.val_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, hm']
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun τ _ => by rw [compAt_det]; exact hloc τ

end PositivityTheory.PfSWUS.SwsHeight

end
