import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLinkEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWAutKQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RRFreeW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicOfGsp4RigidSolvableGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointVanishingGsp4RigidPoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private factor_abs irr_conj free_up par' from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ExistsPlaceAbovePrime
open UpperTheory.GalN.V
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.exists_cm_field_twist_h1 (hU : _root_.UpperTheory.V.Ws.UnramifiedInputs) (hAd : _root_.UpperTheory.V.Th.AdjointLiftingTheorem) (D : Raw Ω c) (hD : Ctx2 D ∨ Ctx3 D) (N : ℕ) (hN : 1 ≤ N) (h1 : Af.KillsMu N D.ψ)
    (h2 : Af.KillsMu N D.ξ) (h3 : Af.KillsMu N D.om) (ι : PadicAlgCl l ≃+* ℂ) (r : G ℚ Ω →* M4 (PadicAlgCl l)) (hr : D.EPt r)
    (hirr : Irr r) (haut : _root_.UpperTheory.V.Aut.IsAut4Alt ι r) :
    ∃ (K : IntermediateField ℚ Ω) (_ : NumberField K) (_ : IsCMField K) (θ : G ℚ Ω →* (Qbar l)ˣ), Module.finrank ℚ K = 2 ∧
      (∀ g, IsGSp (θ g : PadicAlgCl l) (r g)) ∧
      ∀ R : Representation (Qbar l) (G ℚ Ω) (M4 (Qbar l)),
        Af.IsAdOf (r.toHomUnits.comp (resQ K)) (θ.comp (resQ K)) R → Af.BlochKatoSelmerVanishes l R := by
  have hG : D.Good := hD.elim (·.1) (·.1)
  obtain ⟨hlev, θ, hθ, hdual, hθv⟩ := level D hG N hN h1 h2 h3 r hr
  have hmul : D.Mult r := (ptIn D hG _ r hr).1
  have hm : ∀ g, IsGSp (θ g : PadicAlgCl l) (r g) := fun g => by
    rw [hθv]
    exact hmul g
  obtain ⟨T, hF, hDp, hT⟩ := spPt hU.coh Ω l c D hD r hr hirr
  obtain ⟨c₁, hc₁⟩ := _root_.UpperTheory.V.Ws.nonempty_link_of_fit_deep_unramified hU D T hF hDp
  obtain ⟨c', h, X, y, r₁, hle, hconj, -, hres, hw, hi₁⟩ := hT c₁
  obtain ⟨K⟩ := hc₁ c' h hle
  have hKL : T.K ≤ T.L := T.hL ▸ le_sup_right
  have hi : Irr (r.comp T.L.fixingSubgroup.subtype) := by
    obtain ⟨u, hu⟩ := hconj
    refine irr_conj ⟨u⁻¹, fun g => ?_⟩ hi₁
    simp only [MonoidHom.comp_apply, hu, inv_inv, ← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]
  have hiL : Af.IsIrr (r.toHomUnits.comp (resQ T.L)) :=
    (auIrr _ (r.comp (resQ T.L)) hi fun g => ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩).1
  have hiK : Af.IsIrr (r.toHomUnits.comp (resQ T.K)) :=
    (auIrr _ (r.comp (resQ T.K)) hi fun g =>
      ⟨IntermediateField.fixingSubgroupEquiv T.K ⟨g, IntermediateField.fixingSubgroup_le hKL g.2⟩, rfl⟩).1
  have hanti : StrictAnti ![(D.e : ℤ) + 1, D.e, 1, 0] := by
    have := hG.two_le
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    fin_cases i <;> simp <;> omega
  have hcK : Continuous (r.toHomUnits.comp (resQ T.K)) := hlev.cont.comp (Af.continuous_restrictScalarsHom ℚ T.K Ω)
  have hP := _root_.UpperTheory.GalN.V.autKQ0_alt hU.pr T.K Ω T.degK l ι 4 (by norm_num) r.toHomUnits _ hlev.cont (_root_.UpperTheory.GalN.V.isAutomorphicOverImagQuad_of_isAutQA haut) ⟨θ, hθ, hdual⟩ hiK
  have hf := _root_.UpperTheory.V.Z.Win.RR.freePUA_alt hU.pr T.K Ω T.degK l hG.l_odd ι 4 (by norm_num) _ N _ hN hanti hcK hP
    (_root_.UpperTheory.GalN.V.autQN'_alt hU.pr.toClassicalTheorems (by norm_num) ⟨θ, hθ, hdual⟩ haut hlev.cont T.K T.degK hiK).2
    ((unlRes T.K Ω l 4 N _ r.toHomUnits hN).1 (fun A hA g hg =>
      ⟨IntermediateField.fixingSubgroupEquiv T.K ⟨g, hF.1.split l hG.l_mem A hA hg⟩, rfl⟩) (spUnl D hG N hN h1 h2 h3 r hr))
  obtain ⟨π, hreg, -, hatt⟩ := hP
  obtain ⟨hgal, hsol⟩ := auGal D T
  have hL := _root_.automorphic_of_gsp4_rigid_solvable_galois hU.pr T.K T.L hKL T.degK hgal hsol ι r _ hlev.cont (_root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good hU.pr D hG ι) hmul D.cc hG.isCC hiL
    ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hU.pr T.K Ω l ι 4 _).2.1.2 ⟨π, hreg, hatt⟩)
  have hWit : _root_.UpperTheory.V.Z.Win.WitA ι (r.toHomUnits.comp (resQ T.L)) := by
    letI : Algebra T.K T.L := (IntermediateField.inclusion hKL).toAlgebra
    haveI : IsScalarTower T.K T.L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsGalois T.K T.L := IsGalois.tower_top_of_isGalois ℚ T.K T.L
    have hsol' : IsSolvable (T.L ≃ₐ[T.K] T.L) :=
      @solvable_of_solvable_injective _ _ _ _ (hf := (AlgEquiv.restrictScalarsHom_injective ℚ)) hsol
        (f := (AlgEquiv.restrictScalarsHom ℚ : (T.L ≃ₐ[T.K] T.L) →* (T.L ≃ₐ[ℚ] T.L)))
    obtain ⟨Q, hQ⟩ := auPair r (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) hmul D.cc
    have hpol : Af.Sol.Pol ι (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) :=
      ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, _, D.cc, Q, _root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good hU.pr D hG ι, auSign _, hG.isCC, fun s s' h => by
          have h' : Af.resG ℚ T.K Ω s' = D.cc * Af.resG ℚ T.K Ω s * D.cc⁻¹ := h
          rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h']
          exact hQ _⟩
    exact _root_.UpperTheory.V.Z.Win.Dn.automorphy_up_base_change (r := r.toHomUnits.comp (resQ T.K)) T.L hU.pr hsol' (by norm_num) hcK hiL hpol ⟨π, hreg, hatt⟩
      (((flagLaws ℚ Ω l 4 r.toHomUnits).2.2.2 T.K).2.1 ((flagLaws ℚ Ω l 4 r.toHomUnits).2.2.1 N _ hN hlev).2)
      (_root_.UpperTheory.GalN.V.autQN'_alt hU.pr.toClassicalTheorems (by norm_num) ⟨θ, hθ, hdual⟩ haut hlev.cont T.K T.degK hiK).2
  obtain ⟨ρ, hρ, hz⟩ := _root_.adjoint_vanishing_gsp4_rigid_point hU hAd hG hF hDp K X y ι r r₁ hconj hres hw (Units.continuous_val.comp hlev.cont) hmul hi hL hWit hf
  refine ⟨T.K, inferInstance, inferInstance, θ, T.degK, hm, fun R hR => ?_⟩
  refine adDown Ω l T.K T.L T.degK (fun σ hσ x => hσ ⟨x.1, hKL x.2⟩) K.s K.V 4 _ _ R hcK hR ρ (K.twc 0)
    (fun g t e => ?_) (fun g g' t e e' => ?_) hz
  · refine (congrArg Units.val (DFunLike.congr_fun hρ g)).trans ((K.rho_val _ _ _).trans ?_)
    exact congrArg (fun σ => (K.twc 0 g : PadicAlgCl l) • r σ) e
  · have a1 := congrArg (algebraMap c'.O (PadicAlgCl l)) (K.conj g g' e).1
    rw [map_mul, map_mul, map_mul, map_pow, map_one] at a1
    have a2 : (θ.comp (resQ T.K) t : PadicAlgCl l) = algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.L g))) :=
      (congrArg (fun σ => (θ σ : PadicAlgCl l)) e'.symm).trans (hθv _)
    have a3 : (cycBar T.L Ω l g : PadicAlgCl l) = algebraMap c'.O (PadicAlgCl l) (chiO T.L Ω l c'.O g) := rfl
    have a4 : K.twc 0 g * K.twc 0 g' * θ.comp (resQ T.K) t * cycBar T.L Ω l g ^ 3 = 1 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, K.twc_val, pow_zero, mul_one, Units.val_one]
      rw [a2, a3]
      exact a1
    rw [eq_inv_of_mul_eq_one_left a4, ← zpow_natCast, ← zpow_neg]
    rfl
end
