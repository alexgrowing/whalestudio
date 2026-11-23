import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationExpUniqueFullLevelMarkingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearEquivIntertwiningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfMarkedPeriodsFamily

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU
open scoped Matrix

namespace UpperTheory.Gal.W2

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}

private theorem refl_marked {Λ : Type} (N : ℕ) (D : PLat O bar) (t : Λ → D.La) :
    IsMarkedIsom N D D t t (LinearEquiv.refl O D.La) :=
  ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩⟩

private theorem commutes_rho {D : PLat O bar} {P P' : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ρ P) (hP' : IsPeriod D ρ P') (w : D.La ≃ₗ[O] D.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hw : ∀ x, P' (w x) = h (P x)) (a : O) (z : Fin g → ℂ) :
    h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by
    rw [hP.2.2.2.1]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    rw [← hP.1, ← hw, ← hw, map_smul, hP'.1]
  | zero => simp
  | add x y _ _ hx hy => simp only [Matrix.mulVec_add, map_add, hx, hy]
  | smul c x _ hx =>
    have e : ∀ v : Fin g → ℂ, h (c • v) = c • h v := fun v =>
      (h.toLinearMap.restrictScalars ℝ).map_smul c v
    rw [Matrix.mulVec_smul, e, e, hx, Matrix.mulVec_smul]

theorem sheetOf_of : SheetOf := by
  intro O _ bar g ρ Λ F N Cl U i hN hfull
  have hN0 : 0 < N := by omega
  have key : ∀ (P P' : (U.Di i).La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsPeriod (U.Di i) ρ P' → (∀ x, P' x = h (P x)) →
      ∀ (y y' : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A))
        (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F.A)), y = y' →
      UnifAt F (RingHom.id ℂ) ρ N (U.Di i) (U.t i) P y e →
      UnifAt F (RingHom.id ℂ) ρ N (U.Di i) (U.t i) P' y' e' →
      ∀ z, (e' (h z)).left = (e z).left := by
    intro P P' h hP' hx y y' e e' hy a b z
    subst hy
    have h2 := GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N (U.Di i) (U.Di i) (U.t i) (U.t i) P P' y e
      (LinearEquiv.refl O _) h hN0 a (refl_marked N _ _) (fun x => hx x) hP'
    have h3 := congrFun (GlobalTheory.T.complexUniformisation_exp_unique_full_level_marking O bar g ρ ℂ (RingHom.id ℂ) Λ F N (U.Di i) (U.t i) P' y _ _ hN hfull h2 b) (h z)
    simp only [LinearEquiv.symm_apply_apply] at h3
    rw [← h3]
  refine ⟨{ u := U.u i, ex := U.ex i, ov := fun P hP => (U.unif i P hP).1,
            exp := fun P hP => (U.unif i P hP).2.2.1, ker := fun P hP => (U.unif i P hP).2.2.2.1,
            lin := ?_, hol := U.hol i, lift := ?_ }, fun _ => rfl, fun _ _ => rfl⟩
  · intro P P' h hP hP' hx z
    have e : U.u i P = U.u i P' :=
      (U.fibre i P P' hP hP').2 ⟨LinearEquiv.refl O _, h, refl_marked N _ _, fun x => hx x⟩
    exact key P P' h hP' hx _ _ _ _ e (U.unif i P hP) (U.unif i P' hP') z
  · intro m B y hB hy hhol b₀ hb₀ P₀ hP₀ hyb
    obtain ⟨B', i', P, hB', hb', hsub, hP, hu⟩ := U.lift m B y hB hy hhol b₀ hb₀
    have hPb := hP.1 b₀ hb'
    obtain rfl : i' = i := U.disj i' i (P b₀) P₀ hPb hP₀ ((hu b₀ hb').trans hyb)
    obtain ⟨w, h, hw, hwx⟩ := (U.fibre i' (P b₀) P₀ hPb hP₀).1 ((hu b₀ hb').trans hyb)
    have hc := commutes_rho hPb hP₀ w h hwx
    let P' : (Fin _ → ℂ) → ((U.Di i').La →+ (Fin g → ℂ)) := fun b =>
      (h.toLinearMap.toAddMonoidHom.comp (P b)).comp w.symm.toLinearMap.toAddMonoidHom
    have ev : ∀ b x, P' b x = h (P b (w.symm x)) := fun _ _ => rfl
    have hper : ∀ b ∈ B', IsPeriod (U.Di i') ρ (P' b) := fun b hb =>
      isPeriod_comp_isometry_symm _ _ w hw.1 _
        (GlobalTheory.T.comp_linearEquiv_intertwining O bar _ g ρ ρ (P b) h (hP.1 b hb) hc)
    refine ⟨B', P', hB', hb', hsub, ⟨hper, fun x => ?_⟩, ?_, fun b hb => ?_⟩
    · exact (LinearMap.toContinuousLinearMap h.toLinearMap).differentiable.comp_differentiableOn
        (hP.2 (w.symm x))
    · ext1 x
      rw [ev, ← hwx, LinearEquiv.apply_symm_apply]
    · rw [← hu b hb]
      exact ((U.fibre i' (P b) (P' b) (hP.1 b hb) (hper b hb)).2
        ⟨w, h, hw, fun x => by rw [ev, LinearEquiv.symm_apply_apply]⟩).symm

end UpperTheory.Gal.W2
