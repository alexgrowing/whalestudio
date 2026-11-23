import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPairAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.AcClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.FormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.HasFlagPush
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.RedPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.RedDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.IneTriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondA
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondC
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondDRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TraceOfCp
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.MapsPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.ContinuousLinearClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.H4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
attribute [local instance high] DivisionSemiring.to_moduleIsTorsionFree
theorem UpperTheory.V.Ws.modular_deformation_quotient_regular_at_point_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ (k : Type) [Field k] [Finite k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
        (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
        (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
        Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
        X.LocZero J (y : X.A →+* PowerSeries k) := by
  intro _ Ω _ _ _ l _ c D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ k _ _ _ y hy hyJ hU hI q hq hqy
  have hQ := P1.psPair D T c' h X k y hy
  haveI : IsLocalHom (algebraMap c'.O k) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero (hQ.loc a hn)⟩
  letI : Algebra (ResidueField c'.O) k := (ResidueField.lift (algebraMap c'.O k)).toAlgebra
  haveI : IsScalarTower c'.O (ResidueField c'.O) k := IsScalarTower.of_algebraMap_eq fun a => rfl
  obtain ⟨hfin, hchar, -⟩ := P1.coefRes c'
  obtain ⟨ρ, hρ, hρc⟩ := P1.rhoEx D T c' h K (PowerSeries k) _ (maximalIdeal _) (fun a ha => by
    rw [PowerSeries.algebraMap_apply, hQ.loc a ha, map_zero]; exact zero_mem _) hQ.pair hQ.cont
  obtain ⟨P, hP, hform⟩ := P1.formEx D T hF hD c' h K _ _ ρ hQ.pair hρ
  obtain ⟨ψ, hψ, hflag⟩ := P1.psiEx D T c' h K _ _ ρ hQ.pair hρ
  obtain ⟨hψr, hψc⟩ := P1.redPsi D T c' h K k _ hQ ψ hψ
  let x : W.Point K.r :=
    { K := k, ρ := ρ, cont := hρc, P := P, symm := hP, form := hform, red := P1.redDet D T c' h K k _ hQ ρ hρ
      ine := P1.ineTriv D T c' h K _ _ ρ hQ.pair hρ, ψ := ψ, ψ_red := hψr, flag := fun v => hflag _ _ v }
  obtain ⟨hne, hA⟩ := P1.condA D T hF hD c' h K _ _ ψ hψ (fun v i j hij => by
    obtain ⟨s, hs, hne⟩ := hU v i j hij
    have e := (sxPdMap (Φ := T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) (y : X.A →+* PowerSeries k) X.P).1
    exact ⟨s, hs, fun hh => hne ((e v i s).symm.trans (hh.trans (e v j s)))⟩)
  obtain ⟨n1, n2, n3⟩ := h4 l K.s.odd K.V.frame c'.O K.r x hne hψc hA
    (P1.irrL D T c' h K x _ hQ hρ hI) (P1.condC D T hF hD c' h K) (P1.condD D T hF hD c' h K)
  let f : B.B →ₐ[c'.O] x.A := (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)).comp φ
  have hf : B.IsPt x f := P1.mapsPt D T c' h K X B φ hφ _ y ρ ψ hρ hψ
  have key := hM.p1 x f ⟨n1, n2, n3, P1.n4V0 l _ _ 4 K.r K.v0 x⟩ hf
    (fun b hb => hyJ _ (hJ ▸ Ideal.mem_map_of_mem φ hb)) ⟨q.comap φ, hq.comap φ⟩ (fun b hb => hqy _ hb)
  rw [hJ]
  exact Ideal.map_le_iff_le_comap.2 key
end
