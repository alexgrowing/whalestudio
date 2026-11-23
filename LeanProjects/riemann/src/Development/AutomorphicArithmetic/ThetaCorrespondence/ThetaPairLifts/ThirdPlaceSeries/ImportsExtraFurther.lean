import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoCharacterOffsetUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisConditionFourOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cut
namespace GlobalTheory.UnrNoChi
variable {D : D7} (i : D.nd.Loc)
end GlobalTheory.UnrNoChi
theorem GlobalTheory.UnrNoChi.main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → NoChiOff i r Set.univ ∧ UnrOut i r Set.univ := by
  intro D L nch i r π ρ hF _ _ hHG hr _ hρ
  have hUnr := _root_.Formalism.MainNotions.N.admG4_of_goodR D i r hF.Conclusion1.1 hr
  have hSub := Formalism.MainNotions.N.galois_condition_six_of D i r hF.Conclusion2.2.1 hHG hr
  refine ⟨?_, ?_⟩
  · intro x _ hxZ u hu
    by_contra hu0
    refine hxZ (hSub x ⟨u, hu0, fun g => ?_⟩)
    have h := hu g
    rw [rTwO, GlobalTheory.UnrNoChi.mapM_twistM', Matrix.smul_mulVec] at h
    conv_rhs => rw [← h]
    rw [smul_smul, ← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
      one_smul]
  · intro v hvl hvS hvQ x _ γ hγ
    have hχ := GlobalTheory.UnrNoChi.chi_one_eq_one i r π ρ hρ (hUnr π v hvl hvS hvQ γ hγ)
    have hx : rO D.nd i r x γ = 1 := by simp [rO, hUnr x v hvl hvS hvQ γ hγ]
    rw [rTwO, twistM]
    simp [hx, hχ]
end
