import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecTw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartSemilinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistIsConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistChartAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistSemilinearSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistFixesIntegralFamilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFramePullbackMumfordFrameGaloisTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorRelationPullbackGaloisAutomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLiftGaloisTwistOfConjugatePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionPullbackThetaSectionsGaloisTwistStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Mum GlobalTheory.Mum.Conj in

theorem GlobalTheory.Mum.exists_eqv_conj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ τ : Kb R →ₐ[FractionRing R] Kb R, LabExt τ lab lab) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ E', Eqv D.toPre A (Kb R) N lab E' ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre N) s, F₀.Over s → SecTw σ (E s) (E' s) := by
  intro R _ _ _ _ D A N _ lab E hE hlab σ
  have hσ : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let σe : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective σ hσ
  let τ : Kb R →ₐ[FractionRing R] Kb R := σe.symm.toAlgHom
  have hστ : σ.comp τ = AlgHom.id _ _ := AlgHom.ext fun x => σe.apply_symm_apply x
  have hστ' : ∀ x, σ (τ x) = x := fun x => σe.apply_symm_apply x
  refine ⟨fun s => secTw A N σ (E (famTw D.toPre N τ s)), ⟨?_, ?_, ?_, hE.onto, hE.frame, hE.lift, ?_⟩, ?_⟩
  · exact (GlobalTheory.T.pullbackThetaSectionsGaloisTwist_bijective R A N σ).comp (hE.bij.comp (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_bijective R D.toPre N τ))
  · intro s s' s'' h j
    exact GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add R A N σ _ _ _ (hE.add _ _ _ (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_chart_add R D.toPre N τ _ _ _ h)) j
  · intro c s s' h j
    have := GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_semilinear R A N σ (τ c) _ _ (hE.smul (τ c) _ _ (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_semilinear_smul R D.toPre N τ c _ _ h)) j
    rwa [hστ'] at this
  · intro p w θ s s' hw hθ hφ
    obtain ⟨p₀, hp₀⟩ := qkExtExists R D.toPre (Kb R) (Kb R) τ.toRingHom (fun r => τ.commutes r) N p
    have hx := hlab τ p p₀ hp₀
    exact GlobalTheory.T.thetaGroupAction_pullbackThetaSectionsGaloisTwist R A N σ τ hστ θ _ _ (hE.act p₀ (frTw D.toPre τ hp₀ w) (thTw A N τ θ) _ _
      (GlobalTheory.T.isSymmetricFrame_pullbackMumfordFrameGaloisTwist R D.toPre N τ p p₀ hp₀ w hw) (GlobalTheory.T.symmetricLift_galoisTwist_of_conjugatePoint R A N τ _ _ θ hθ hx) (GlobalTheory.T.operator_relation_pullback_galois_automorphism R D.toPre N τ p p₀ hp₀ w s s' hφ))
  · intro F₀ s hs
    show SecTw σ (E s) (secTw A N σ (E (famTw D.toPre N τ s)))
    rw [GlobalTheory.T.pullbackThetaFamilyGaloisTwist_fixes_integralFamily R _ D.toPre N τ F₀ s hs]
    exact GlobalTheory.T.pullbackThetaSectionsGaloisTwist_isConjugate R A N σ (E s)
