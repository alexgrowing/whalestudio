import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.CharpolySmulScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PsiCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.IrrOfStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PairJAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.SupComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuKap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistInvarianceAutomorphic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyDescentSolvableCMToImaginaryQuadraticA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.pmDown_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (ι : PadicAlgCl l ≃+* ℂ) (y : X.A →ₐ[c'.O] PadicAlgCl l),
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
        ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
          Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)) → _root_.UpperTheory.V.Aut.IsAut4Alt ι r := by
  intro U Ω _ _ _ l _ c D T hF _ c' h K X ι y hW r hr hc hm hi h1
  have hG : D.Good := hF.2.elim (fun a => a.1.1) (fun a => a.1.1)
  obtain ⟨hi1, -⟩ := auIrr _ (r.comp (resQ T.L)) hi fun g =>
    ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩
  have h2 := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida U.pr T.L Ω l ι 4 _).2.2 h1
  have hκ := _root_.UpperTheory.V.Ws.isAlgChar_pushCh_link_kappa U.pr D T c' h K ι
  have hN := _root_.UpperTheory.GalN.V.csdN'_alt U.pr.toClassicalTheorems (by norm_num) h1
  have hκc : Continuous (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ) := hκ.choose_spec.1
  have hcr : Continuous r.toHomUnits := Units.continuous_iff.2 ⟨hc, hc.comp continuous_inv⟩
  have hW3 := _root_.UpperTheory.V.Z.Win.Dn.twist'_alt U.pr.toClassicalTheorems ((_root_.UpperTheory.V.Af.algOfCyc_s U.pr T.L Ω l ι).2.1 _ _ hκ hκ).2 hκc.inv
    (hN.2 (Af.Bc.irrBasic.2 _ _ _ _ _ (hcr.comp (Af.continuous_restrictScalarsHom ℚ T.L Ω)) hκc))
  have h3 := _root_.UpperTheory.V.Af.twist_invariance_automorphic U.pr T.L Ω l ι 4 _ _ h2 ((_root_.UpperTheory.V.Af.algOfCyc_s U.pr T.L Ω l ι).2.1 _ _ hκ hκ).2
  have h4 : Af.tw (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ))
      (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)⁻¹ = r.toHomUnits.comp (Af.resG ℚ T.L Ω) := by
    ext g : 2
    rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.inv_apply, Units.inv_mul, one_smul]
    rfl
  rw [h4] at h3 hW3
  obtain ⟨hgal, hsol⟩ := auGal D T
  obtain ⟨P, hP⟩ := auPair r (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) hm 1
  have h0 := _root_.UpperTheory.GalN.V.isAutomorphicOverImagQuad_of_restriction_aut_irr U.pr (Z.Bc.solC_of_solDescent (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida U.pr)) Ω T.K T.L (T.hL ▸ le_sup_right) T.degK hgal hsol l ι 4
    (by norm_num) r.toHomUnits (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th)
    (Units.continuous_iff.2 ⟨hc, hc.comp continuous_inv⟩) (_root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι)
    ⟨P, fun s => by simpa using hP s⟩ hi1 h3
  obtain ⟨hI, hFl, hU⟩ := UpperTheory.V.Keep.ptLaws D T hG hF.1 hF.1.locL c' h X y hW r hr
  have hle : T.K ≤ T.L := T.hL ▸ le_sup_right
  letI : Algebra T.K T.L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower T.K T.L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ T.K T.L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois T.K T.L := IsGalois.tower_top_of_isGalois ℚ T.K T.L
  haveI : Group.IsSolvable (T.L ≃ₐ[ℚ] T.L) := hsol
  have s2 : Group.IsSolvable (T.L ≃ₐ[T.K] T.L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (T.L ≃ₐ[T.K] T.L) →* (T.L ≃ₐ[ℚ] T.L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  have e : (r.toHomUnits.comp (Af.resG ℚ T.K Ω)).comp (Af.resG T.K T.L Ω) = r.toHomUnits.comp (Af.resG ℚ T.L Ω) := rfl
  have i2 : Af.IsIrr ((r.toHomUnits.comp (Af.resG ℚ T.K Ω)).comp (Af.resG T.K T.L Ω)) := e ▸ hi1
  have i1 : Af.IsIrr (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) := (Af.Bc.irrBasic.1 _ _ _ 4 _).1 _ i2
  have hcK : Continuous (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) := hcr.comp (Af.continuous_restrictScalarsHom ℚ T.K Ω)
  obtain ⟨Q, hQ⟩ := auPair r (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) hm D.cc
  have hpol : Af.Sol.Pol ι (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, _, D.cc, Q, _root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι, auSign _, hG.isCC, fun s s' h => by
        have h' : Af.resG ℚ T.K Ω s' = D.cc * Af.resG ℚ T.K Ω s * D.cc⁻¹ := h
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h']
        exact hQ _⟩
  have fl := (flagLaws ℚ Ω l 4 r.toHomUnits).2.2.2 T.K
  have hWK : _root_.UpperTheory.V.Z.Win.WitA ι (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) :=
    _root_.UpperTheory.V.Z.Win.Dn.down'_alt T.L U.pr s2 (by norm_num) hcK i2 hpol (h0 hcr T.K T.degK i1) (fl.2.1 hFl) (fl.1 hI) (fun w hw _ => hU w hw) (e ▸ hW3)
  exact _root_.UpperTheory.GalN.V.isAutQA_of_isAutomorphicOverImagQuad_of_witAQ h0 fun _ => _root_.UpperTheory.V.Z.Win.Dn.across'_alt U.pr T.K Ω T.degK (by norm_num)
    (fun A hA g hg x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hF.1.split l hG.l_mem A hA hg) x x.2) hcr h0
    ⟨_, _root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι, P, fun s => by simpa using hP s⟩ hI hFl i1 hWK
end
