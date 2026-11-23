import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPhiEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPmFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModularDeformationQuotientRegularAtPoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWinPm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PmAutO
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnPmDown
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.Gal.projectedFormsSystemPart.promodular_existence_of_local_zero (U : _root_.UpperTheory.V.Ws.UnramifiedInputs)
    (hS : ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeedAlt ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
      X.LocZero J (y : X.A →+* PadicAlgCl l)) : _root_.UpperTheory.V.Ws.PMExAlt := by
  intro Ω _ _ _ l _ c D T hF hD ι
  obtain ⟨c₁, hc₁⟩ := _root_.UpperTheory.Gal.projectedFormsSystemPart.exists_two_links_same_kappa_not_dvd_of_fit_deep U D T hF hD
  refine ⟨c₁, fun c' h h₁ X => ?_⟩
  obtain ⟨K, K', hκ, hp⟩ := hc₁ c' h h₁
  obtain ⟨⟨B, -⟩, hφ⟩ := _root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link U D T hF hD c' h K X 0
  obtain ⟨φ, hφ⟩ := hφ B
  obtain ⟨Λ, -⟩ := U.lam l T.L Ω K.s K.V c' 4 K.r
  obtain ⟨J₀, hJ⟩ := U.modU l T.L Ω K.s K.V K.hV K.noMu c' K.large 4 (by norm_num) K.r B Λ ι
  obtain ⟨⟨B', -⟩, hφ'⟩ := _root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link U D T hF hD c' h K' X 0
  obtain ⟨φ', hφ'⟩ := hφ' B'
  obtain ⟨Λ', -⟩ := U.lam l T.L Ω K'.s K'.V c' 4 K'.r
  obtain ⟨J₀', hJ'⟩ := U.modU l T.L Ω K'.s K'.V K'.hV K'.noMu c' K'.large 4 (by norm_num) K'.r B' Λ' ι
  have hl : ∀ {b}, b ∈ J₀.map φ → b ∈ J₀.map φ ⊔ J₀'.map φ' := fun hb => Ideal.mem_sup_left hb
  have hr : ∀ {b}, b ∈ J₀'.map φ' → b ∈ J₀.map φ ⊔ J₀'.map φ' := fun hb => Ideal.mem_sup_right hb
  refine ⟨J₀.map φ ⊔ J₀'.map φ', ?_, fun k _ _ _ y y1 y2 y3 y4 q hq hy => sup_le ?_ ?_, fun y y1 q hq hy => sup_le ?_ ?_,
    fun y y1 => _root_.UpperTheory.V.Ws.pmPur_w_alt U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl y fun b hb => y1 b (hl hb),
    fun y y1 y2 r r1 r2 r3 r4 => ?_⟩
  · obtain ⟨n, hn⟩ := _root_.UpperTheory.V.Ws.exists_pow_maximalIdeal_le_of_modular_phi U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl
    exact ⟨n, hn.trans (sup_le_sup_right (sup_le_sup_right le_sup_left _) _)⟩
  · exact _root_.UpperTheory.V.Ws.modular_deformation_quotient_regular_at_point_alt U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl k y y1 (fun b hb => y2 b (hl hb)) y3 y4 q hq hy
  · exact _root_.UpperTheory.V.Ws.modular_deformation_quotient_regular_at_point_alt U D T hF hD c' h K' X B' Λ' ι J₀' hJ' φ' hφ' _ rfl k y y1 (fun b hb => y2 b (hr hb)) y3 y4 q hq hy
  · exact hS D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl y y1 q hq hy
  · exact hS D T hF hD c' h K' X B' Λ' ι J₀' hJ' φ' hφ' _ rfl y y1 q hq hy
  · have a := _root_.UpperTheory.Gal.projectedFormsSystemPart.pmAutO_alt U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl y (fun b hb => y1 b (hl hb)) y2 r r1 r2 r3 r4
    have b := _root_.UpperTheory.Gal.projectedFormsSystemPart.pmAutO_alt U D T hF hD c' h K' X B' Λ' ι J₀' hJ' φ' hφ' _ rfl y (fun b hb => y1 b (hr hb)) y2 r r1 r2 r3 r4
    rw [hκ] at b
    exact _root_.UpperTheory.V.Z.Win.Dn.pmDown_alt U D T hF hD c' h K X ι y y2 r r1 r2 r3 r4
      (_root_.UpperTheory.Gal.projectedFormsSystemPart.glueN (by norm_num) (UpperTheory.Gal.projectedFormsSystemPart.v0_ne hp) a b)
end
