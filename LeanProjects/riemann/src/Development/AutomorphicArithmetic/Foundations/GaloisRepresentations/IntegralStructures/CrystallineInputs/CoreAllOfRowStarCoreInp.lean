import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.OfInputs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedGoodOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoldsSGoodDROfCsd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoldsCsdCrysOfHoldsS
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusGoodOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoldsSDRAllOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineAllOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusAllOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExAllOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoreAllOfCore
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootLinesWeightBoundOfFree

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.UnrTwist

end GlobalTheory.RoadU.UnrTwist

namespace GlobalTheory.RoadU
open GlobalTheory.RoadU.UnrTwist in
theorem _root_.UpperTheory.Gal.Int.Inp.holdsS_good_unr : UpperTheory.Gal.Int.Inp.Inp → SphericalLevelCondition .csd .unr → SphericalLevelCondition .good .unr := by
  intro _ hcsd E Ω _ _ _ _ _ _ l _ ι a ha π χ hS r hr w hw B hB hl
  obtain ⟨κ, m, hκ, hu, hS'⟩ := GlobalTheory.GoodCsdTwist.exists_goodCsd_twist GlobalTheory.automorphicFormsFiniteGL E l a ha π χ hS w hw
  obtain ⟨art, hart, H⟩ := GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter GlobalTheory.globalArtinReciprocity_holds E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := H l ι κ m (isAlgPos_of_isAlg hκ)
  have hrv : Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) :=
    Units.continuous_val.comp hr.1
  have htv : Continuous fun g => ((UpperTheory.V.Af.tw r μ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    simp only [UpperTheory.V.Af.tw_val]
    exact (Units.continuous_val.comp hμc).smul hrv
  have htc : Continuous (UpperTheory.V.Af.tw r μ) := by
    refine Units.continuous_iff.2 ⟨htv, ?_⟩
    simp only [← map_inv]
    exact htv.comp continuous_inv
  have hT : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ) :=
    ⟨htc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hμ⟩
  have hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w)) := by
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E a π κ w B hu hB
  have hc : UpperTheory.V.Af.FrobEig ι (UpperTheory.V.Af.tw r μ) w
      (UpperTheory.V.Af.algSat a (normV w) (B.map (· * κ.val w))) :=
    hcsd E Ω l ι a ha (π.twist κ) (quadChar E ^ a) hS' (UpperTheory.V.Af.tw r μ) hT w hw _ hB' hl
  have hce : UpperTheory.V.Af.Bc.CharEig ι μ⁻¹ w ((κ.val w : ℂ))⁻¹ := by
    refine fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · rw [MonoidHom.inv_apply, (hμ.unr_iff hart (Or.inl hl) hA).2 hu s hs, inv_one]
    · rw [MonoidHom.inv_apply, map_inv, inv_inv, hμ.frob_unr hart (Or.inl hl) hu hA hσ, map_inv₀, RingEquiv.apply_symm_apply]
  have h2 := UpperTheory.frobenius_eigenvalues_twist E Ω l ι a _ μ⁻¹ w _ _ hc hce
  rw [tw_tw_inv] at h2
  convert h2 using 1
  simp only [algSat_eq', Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  field_simp

end GlobalTheory.RoadU
end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem _root_.UpperTheory.Gal.Int.Inp.holdsS_good_dR_of_csd : UpperTheory.Gal.Int.Inp.Inp → SphericalLevelCondition .csd .dR → SphericalLevelCondition .good .dR := by
  intro hI hC E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw B hB
  have hF := GlobalTheory.automorphicFormsFiniteGL
  have hA := hI.hk
  obtain ⟨κ, m, hκ, hu, hcs⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hF E l a ha π χ hs w hw
  obtain ⟨art, hart, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  have hκp : GlobalTheory.HeckeGal.IsAlgPos κ m := GlobalTheory.HeckeGal.isAlgPos_of_isAlg hκ
  obtain ⟨μ, ⟨hμc, hL⟩, -⟩ := hμ l ι κ m hκp
  have htc : Continuous (UpperTheory.V.Af.tw r μ) := UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a r μ hr.1 hμc
  have hW : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ) :=
    ⟨htc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hL⟩
  have hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w)) := by
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E a π κ w B hu hB
  have hcl : ClauseAt .dR (π.twist κ) ι (UpperTheory.V.Af.tw r μ) w :=
    hC E Ω l ι a ha (π.twist κ) _ hcs (UpperTheory.V.Af.tw r μ) hW w hw _ hB'
  show ClauseAt .dR π ι r w
  intro P AI hT A hAw O _ _ _ Bw hj
  obtain ⟨hdR', hJ'⟩ := hcl P AI hT A hAw O Bw hj
  have hμic : Continuous (μ⁻¹) := hμc.inv
  have hch := GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hA E Ω l P AI hT ι art hart κ⁻¹ (-m) μ⁻¹
    (GlobalTheory.GalChar.isAlgPos_inv hκp) hμic hL.inv w A hAw O Bw hj
  have key := GlobalTheory.TwistAbove.twist_above l P AI hT E Ω (Dec (F := E) A) O Bw a
    ((UpperTheory.V.Af.tw r μ).comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype)
    (μ⁻¹.comp (Dec (F := E) A).subtype) (fun g => by
      change ((r g.1 : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) =
        (((μ g.1)⁻¹ : (Qbar l)ˣ) : Qbar l) • ((UpperTheory.V.Af.tw r μ g.1 : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))
      rw [UpperTheory.V.Af.tw_val, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul])
  refine ⟨key.1 hdR' hch.1, fun τ LL' τ' hτ J hJ => ?_⟩
  set m0 := m (ι.toRingHom.comp τ) with hm0
  have e : expo κ (ι.toRingHom.comp τ) = m0 := (GlobalTheory.CuspRep.InfType.expo_of_infType E κ).1 m hκ _
  have hinf : (CG.mk (π.twist κ)).infChar (ι.toRingHom.comp τ) =
      ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (· + (m0 : ℂ)) := by
    rw [← e]
    exact ((GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) _).twist κ).infChar_eq
  have h1 := hJ' τ LL' τ' hτ (J.map (· - m0)) (by
    rw [hinf, Multiset.map_map, Multiset.map_map]
    have e1 : ((CG.mk π).infChar (ι.toRingHom.comp τ)).map ((fun z : ℂ => ((a : ℂ) - 1) / 2 - z) ∘ (· + (m0 : ℂ))) =
        (((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z : ℂ => ((a : ℂ) - 1) / 2 - z)).map (· - (m0 : ℂ)) := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]
      ring
    rw [e1, ← hJ, Multiset.map_map]
    refine Multiset.map_congr rfl fun n _ => ?_
    simp only [Function.comp_apply]
    push_cast
    ring)
  have h2 := key.2.2.2 τ _ _ h1 (hch.2.2.2 τ LL' τ' hτ)
  have e2 : (J.map (· - m0)).map (· + -((-m) (ι.toRingHom.comp τ))) = J := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id J]
    refine Multiset.map_congr rfl fun n _ => ?_
    simp only [Function.comp_apply, Pi.neg_apply, neg_neg, id, hm0]
    ring
  rw [e2] at h2
  exact h2

end GlobalTheory.RoadU

end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem _root_.UpperTheory.Gal.Int.Inp.holdsS_good_crys : UpperTheory.Gal.Int.Inp.Inp → SphericalLevelCondition .csd .crys → SphericalLevelCondition .good .crys := by
  intro hI hC
  have hG := GlobalTheory.CrysTwistBack.holds_good_crys GlobalTheory.automorphicFormsFiniteGL hI.hk (holds_csd_crys_of_holdsS hC)
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw B _
  exact hG E Ω l ι a ha π χ hs r hr w hw

end GlobalTheory.RoadU

end

end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.PhiTwist

open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut7.IwahoriTwist UpperTheory.V UpperTheory.V.Af ValuativeRel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

end GlobalTheory.RoadU.PhiTwist

namespace GlobalTheory.RoadU
open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut7.IwahoriTwist GlobalTheory.RoadU.PhiTwist UpperTheory.V UpperTheory.V.Af in

theorem _root_.UpperTheory.Gal.Int.Inp.holdsS_good_phi : UpperTheory.Gal.Int.Inp.Inp → SphericalLevelCondition .csd .crys → SphericalLevelCondition .csd .phi → SphericalLevelCondition .good .phi := by
  intro hI Hc Hp E Ω _ _ _ _ _ _ l _ ι a ha π χ hS r hr w hw B hB
  intro P AI hT A h O _ _ _ Bw hj g
  obtain ⟨κ, m, hκ, hu, hS'⟩ := GlobalTheory.GoodCsdTwist.exists_goodCsd_twist GlobalTheory.automorphicFormsFiniteGL E l a ha π χ hS w hw
  obtain ⟨art, hart, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  have hκ' := isAlgPos_of_isAlg hκ
  obtain ⟨μ, ⟨hμc, hL⟩, -⟩ := hμ l ι κ m hκ'
  have hcont : Continuous (tw r μ) := UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a r μ hr.1 hμc
  have hr' : Weak (π.twist κ) ι (tw r μ) := ⟨hcont, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hL⟩
  have hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w)) := CG.HasSat.twist hB hu
  have C : (wdAt P ι Bw h hj ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)).charPol g =
      (satWD h a (B.map (· * κ.val w))).charPol g :=
    Hp E Ω l ι a ha (π.twist κ) _ hS' (tw r μ) hr' w hw _ hB' P AI hT A h O Bw hj g
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E a π w
  have hsph : SmGL.IsSpherical σ.ρ :=
    GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.isSpherical_of_hasSatGL w a (((GlobalTheory.Cong.satake_locComp E a π w σ hσ).1 B).1 hB)
  have c1 : IsCrysAt P Bw ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    Hc E Ω l ι a ha (π.twist κ) _ hS' (tw r μ) hr' w hw _ hB' P AI hT A h O Bw hj _ (hσ.twist κ)
      (GlobalTheory.CrysTwistBack.isSpherical_twist_of_unr a w σ κ hu hsph)
  obtain ⟨T⟩ := hT
  have c1s : IsSstAt P Bw ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI ⟨T⟩ E Ω _ O Bw a _ c1
  have hμi : IsCrysAt P Bw ((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hI.hk E Ω l P AI ⟨T⟩ ι art hart κ⁻¹ (-m) μ⁻¹
      (GlobalTheory.GalChar.isAlgPos_inv hκ') hμc.inv hL.inv w A h O Bw hj).2.2.1 hu.inv
  have hrr : r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype = Formalism.MainNotions.SumRepresentations.At.twGL ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
      (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, tw_val, GlobalTheory.TripleGal.rk1, Matrix.det_unique, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_apply]
  have hct : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) :=
    Units.continuous_val.comp (hcont.comp continuous_subtype_val)
  have hcμi : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) :
        Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i; fin_cases j
    have := Units.continuous_val.comp (hμc.inv.comp (continuous_subtype_val (p := fun x => x ∈ ReciprocityTheory.Gal.Dec (F := E) A)))
    simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
  have hsst : IsSstAt P Bw (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    rw [hrr]
    exact isSstAt_twist hI.pst P AI ⟨T⟩ Bw _ _ hct hcμi c1s hμi
  obtain ⟨a', ha'⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  have hc := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) κ
  have hdet : Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
      = μ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype := by
    ext g
    simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
  have htw : (tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.twGL (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
        (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by
    rw [hdet]
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  have hcR : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      ((r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) :=
    Units.continuous_val.comp (hr.1.comp continuous_subtype_val)
  have hcμ : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) :
        Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i; fin_cases j
    have := Units.continuous_val.comp (hμc.comp (continuous_subtype_val (p := fun x => x ∈ ReciprocityTheory.Gal.Dec (F := E) A)))
    simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
  have hdR := (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hI.hk E Ω l P AI ⟨T⟩ ι art hart κ m μ hκ' hμc hL w A h O Bw hj).1
  have hPμ := GlobalTheory.Published.DeRhamPotSemistable.isPstAt hI.pst T Bw _ hcμ hdR
  have hP := isPstAt_of_isSstAt P AI ⟨T⟩ Bw _ hsst
  have hP' := isPstAt_of_isSstAt P AI ⟨T⟩ Bw _ c1s
  rw [htw] at hP'
  have hWD : wdAt P ι Bw h hj ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) =
      (wdAt P ι Bw h hj (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)).lpTwist ((κ.loc w).comp a') (ha'.smooth hc.1) := by
    rw [htw, GlobalTheory.TwistParamAbove.wdAt_twist l P AI ⟨T⟩ ι E Ω A w h O Bw hj a _ _ hcR hcμ hP hPμ hP',
      hI.alg E Ω l P AI ⟨T⟩ ι art hart κ m μ hκ' hμc hL w A h O Bw hj _ hc a' ha', lpChar_lpOfChar]
  have hsat : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth (ξ.comp a')),
      ξ = SmGL.unrChar (w.adicCompletion E) (κ.val w) →
      satWD h a (B.map (· * κ.val w)) = (satWD h a B).lpTwist _ hξ := by
    rintro ξ hξ rfl
    exact satWD_map_mul h a B (κ.val w) ha' hξ
  rw [hWD, hsat (κ.loc w) (ha'.smooth hc.1) (loc_eq_unrChar κ hu)] at C
  exact (charPol_lpTwist_iff _ _ _ _ g).1 C

end GlobalTheory.RoadU
end

end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnrDescent

theorem _root_.UpperTheory.Gal.Int.Inp.holdsS_all_unr : UpperTheory.Gal.Int.Inp.Inp → SphericalLevelCondition .good .unr → SphericalLevelCondition .all .unr := by
  intro hI hG E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc r hr w _ B hB hl A h
  have hAF := GlobalTheory.automorphicFormsFiniteGL
  obtain ⟨Q, hQdec, hQsplit, hQram, hQgood⟩ := (GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π w).nonempty
  obtain ⟨P, hP⟩ := GlobalTheory.QuadLiftBridge.quadLift hI.ac hI.js E Q.K Q.two a ha π hQram
  obtain ⟨⟨χ', hsc'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hI.js hI.gk E Q.K l a ha π χ P hP hsc.all
  have hscG : InScope .good l P χ' := ⟨hsc'.1, hsc'.2.1, hQgood P hP⟩
  have hrP : Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) := GlobalTheory.GalCut.weak_comp_res E Q.K Ω l ι a π P hP r hr
  obtain ⟨w', hunder, h', hN⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A h (hQdec A h)
  have hB' : (CG.mk P).HasSat w' B := by
    have e := hP.sat w' 1 B (by rw [pow_one, hunder, hN]) (hunder ▸ hB)
    simpa using e
  have hlw : ((l : ℕ) : 𝓞 Q.K) ∉ w'.asIdeal := by
    intro hw
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 E))
    have e2 := (h' ((l : ℕ) : 𝓞 Q.K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have hcl := hG Q.K Ω l ι a ha P χ' hscG (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) hrP w' (hQsplit w' hunder) B hB' hlw A h'
  rw [hN] at hcl
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨s', rfl⟩ := hQdec A h (Ine_le_Dec A hs)
    exact hcl.1 s' hs
  · obtain ⟨σ', rfl⟩ := hQdec A h hσ.1
    have e := hcl.2 σ' hσ
    rw [← map_inv]
    exact e

end GlobalTheory.UnrDescent

end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

set_option maxHeartbeats 1000000 in

theorem _root_.UpperTheory.Gal.Int.Inp.holdsS_dR_all_of_good : UpperTheory.Gal.Int.Inp.Inp → SphericalLevelCondition .good .dR → SphericalLevelCondition .all .dR := by
  intro hI hG E Ω _ _ _ _ _ _ l _ ι a ha π χ hS r hr w _ B hB
  have hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL := GlobalTheory.automorphicFormsFiniteGL
  have hQL : QuadLift := GlobalTheory.QuadLiftBridge.quadLift hI.ac hI.js
  obtain ⟨Q, hdec, hsplit, hram, hgood⟩ := (GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π w).nonempty
  obtain ⟨P, hP⟩ := hQL E Q.K Q.two a ha π hram
  obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hI.js hI.gk E Q.K l a ha π χ P hP hS.all
  have hrP := GlobalTheory.GalCut.weak_comp_res E Q.K Ω l ι a π P hP r hr
  show ClauseAt .dR π ι r w
  intro Pr AI hT A hA O _ _ _ Bw hj
  have hdA := hdec A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdA
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', hu, hw', hn⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A hA hdA
  have hBP : (CG.mk P).HasSat w' (B.map (· ^ 1)) :=
    hP.sat w' 1 B (by rw [hu, pow_one]; exact hn) (by rw [hu]; exact hB)
  have hc : ClauseAt .dR P ι _ w' :=
    hG Q.K Ω l ι a ha P χ' ⟨hχ'.1, hχ'.2.1, hgood P hP⟩ _ hrP w' (hsplit w' hu) _ hBP
  have hc' := hc Pr AI hT A hw' O Bw' hj'
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  refine ⟨D.1 hc'.1, fun τ LL' τ' hτ J hJ => ?_⟩
  obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.induced_embedding_extends E Ω Q.K l A O Bw Bw' e1 e2 τ LL' τ' hτ
  have hJK : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk P).infChar (ι.toRingHom.comp τK)).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
    rw [hP.inf, RingHom.comp_assoc, hτK]
    exact hJ
  have hres := D.2.2.2.2 τK J (hc'.2 τK LL' τ'' hind J hJK)
  rwa [hτK] at hres

end GlobalTheory.RoadU

end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem _root_.UpperTheory.Gal.Int.Inp.holdsS_all_crys : UpperTheory.Gal.Int.Inp.Inp → SphericalLevelCondition .good .crys → SphericalLevelCondition .all .crys := by
  intro hIn hgood E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc r hr w _ B hB
  have hAF := GlobalTheory.automorphicFormsFiniteGL
  have hQL : QuadLift := GlobalTheory.QuadLiftBridge.quadLift hIn.ac hIn.js
  intro Pr AI hT A hA O _ _ _ Bw hj σ hσ hsph
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := (GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π w).nonempty
  obtain ⟨Pc, hPc⟩ := hQL E Q.K Q.two a ha π hQ3
  have hres := GlobalTheory.GalCut.weak_comp_res E Q.K Ω l ι a π Pc hPc r hr
  obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hIn.js hIn.gk E Q.K l a ha π χ Pc hPc hsc
  have hin : InScope .good l Pc χ' := ⟨hχ'.1, hχ'.2.1, hQ4 Pc hPc⟩
  have hdec := hQ1 A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A hA hdec
  have hund : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'
    ext1
    exact this.over.symm
  obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w hA Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk Pc).HasSat w' B := by
    have := hPc.sat w' 1 B (by rw [pow_one, hund, hq]) (by rw [hund]; exact hB)
    simpa using this
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp hAF Q.K a Pc w'
  obtain ⟨e, he⟩ := hPc.loc w w' i hi.cont hi.loc σ σ' hσ hσ'
  have hsph' := (GlobalTheory.CompletionIso.iwahori_spherical_transfer E Q.K w w' i hi.cont a σ σ' e he).2 hsph
  have hcr : ClauseAt .crys Pc ι (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) w' :=
    hgood Q.K Ω l ι a ha Pc χ' hin _ hres w' (hQ2 w' hund) B hB'
  exact (GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r).2.2.1
    (hcr Pr AI hT A h' O Bw' hj' σ' hσ' hsph')

end GlobalTheory.RoadU
end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.PhiDescent

end GlobalTheory.RoadU.PhiDescent

namespace GlobalTheory.RoadU
open GlobalTheory.RoadU.PhiDescent in

theorem _root_.UpperTheory.Gal.Int.Inp.holdsS_all_phi : UpperTheory.Gal.Int.Inp.Inp → SphericalLevelCondition .good .crys → SphericalLevelCondition .good .phi → SphericalLevelCondition .all .phi := by
  intro hIn _ hgood E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc r hr w _ B hB Pr AI hT A h O _ _ _ Bw hj g
  have hF := GlobalTheory.automorphicFormsFiniteGL
  have hQ := GlobalTheory.QuadLiftBridge.quadLift hIn.ac hIn.js
  obtain ⟨Q, hQdec, hQsplit, hQram, hQgood⟩ := (GlobalTheory.T.infinite_quadraticCM_goodBaseChange_split hF E Ω l a π w).nonempty
  obtain ⟨P, hP⟩ := hQ E Q.K Q.two a ha π hQram
  obtain ⟨⟨χ', hsc'⟩, -⟩ := GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight hF hIn.js hIn.gk E Q.K l a ha π χ P hP hsc.all
  have hsc'' : InScope .good l P χ' := ⟨hsc'.1, hsc'.2.1, hQgood P hP⟩
  have hr' := GlobalTheory.T.weaklyAttachedGaloisRepresentation_baseChange_restrict E Q.K Ω l ι a π P hP r hr
  have hdec := hQdec A h
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A h hdec
  have hunder : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver h h'
    ext1
    exact this.over.symm
  obtain ⟨c, hc, hdegc, hq, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  obtain ⟨S, hS, -, -, -, -, hTw, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk P).HasSat w' B := by
    have := hP.sat w' 1 B (by rw [pow_one, hunder, hq]) (by rw [hunder]; exact hB)
    simpa using this
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  have hrel : WDRel (RingEquiv.refl Ω) (wdAt Pr ι Bw h hj (r.comp (Dec (F := E) A).subtype))
      (wdAt Pr ι Bw' h' hj' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype)) := by
    by_cases hp : IsPstAt Pr Bw (r.comp (Dec (F := E) A).subtype)
    · exact GlobalTheory.RealGal.wdRelRes_gen E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r hp ι w w' h h' hj hj' i hi
    · have hp' : ¬ IsPstAt Pr Bw' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype) :=
        fun H => hp (D.2.2.2.1 H)
      rw [wdAt_of_not_isPstAt _ _ _ _ hp, wdAt_of_not_isPstAt _ _ _ _ hp']
      exact wdRel_trivWD h h' _ a
  have hsat : WDRel (RingEquiv.refl Ω) (satWD h a B) (satWD h' a B) := by
    have h0 := GlobalTheory.RSGam.Transport.wdRel_lpUnr c hc hdegc (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))
    unfold satWD
    rw [hS, hTw, (hS _ _).mp h0]
  have hgc : WeilRel (RingEquiv.refl Ω) g (c g) := (hc g (c g)).2 rfl
  have hcl := hgood Q.K Ω l ι a ha P χ' hsc'' _ hr' w' (hQsplit w' hunder) B hB' Pr AI hT A h' O Bw' hj' (c g)
  rw [charPol_eq hrel hgc, charPol_eq hsat hgc]
  exact hcl

end GlobalTheory.RoadU
end

end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.RoadU

open UpperTheory.V.Af in

theorem _root_.UpperTheory.Gal.Int.Inp.ex_all_of_good : UpperTheory.Gal.Int.Inp.Inp → Ex .good → SphericalLevelCondition .good .unr → Ex .all := by
  intro hIn hEx hHolds E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc
  have hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL := GlobalTheory.automorphicFormsFiniteGL
  have hQL : QuadLift := GlobalTheory.QuadLiftBridge.quadLift hIn.ac hIn.js
  obtain ⟨hreg, hpol, -⟩ := hsc
  let S : Set (GlobalTheory.RealGal.QCM E Ω) := {Q | ∃ P : CuspSub ↥Q.K a, IsLift π P ∧ Good l P}
  have fam := GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π
  have famS : ∀ (Q : GlobalTheory.RealGal.QCM E Ω),
      (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) →
      (∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P) → Q ∈ S := by
    intro Q hram hgood
    obtain ⟨P, hP⟩ := hQL E ↥Q.K Q.two a ha π hram
    exact ⟨P, hP, hgood P hP⟩
  obtain ⟨v0⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩⟩
  have hS : S.Infinite := (fam v0).mono fun Q hQ => famS Q hQ.2.2.1 hQ.2.2.2
  choose P hP using fun Q : ↥S => Q.2
  have key : ∀ Q : ↥S, ∃ (χ' : HChar (maximalRealSubfield ↥Q.1.K)) (r : G ↥Q.1.K Ω →* GL (Fin a) (Qbar l)),
      InScope .good l (P Q) χ' ∧ Weak (P Q) ι r := fun Q => by
    obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hIn.js hIn.gk E ↥Q.1.K l a ha π χ (P Q) (hP Q).1 ⟨hreg, hpol, trivial⟩
    have hs : InScope .good l (P Q) χ' := ⟨hχ'.1, hχ'.2.1, (hP Q).2⟩
    obtain ⟨r, hr⟩ := hEx ↥Q.1.K Ω l ι a ha (P Q) χ' hs
    exact ⟨χ', r, hs, hr⟩
  choose χ' r hχ' hr using key
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.CMBasePatch.main hAF E Ω l ι a π S hS P r fun Q => ⟨(hP Q).1, hr Q⟩
  refine ⟨ρ, hρc, hρs, ?_⟩
  haveI : Infinite ↥S := hS.to_subtype
  obtain ⟨Q0, hQ0⟩ := hev.exists
  have hunr := GlobalTheory.RealGal.ConjUnr.unr_of_conj_res E Ω Q0.1 l a ρ (r Q0) hQ0 ((hr Q0).2.2.mono fun w' hw' A hA => by
    obtain ⟨B, -, hF⟩ := hw'
    exact (hF A hA).1)
  have hlf : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hsat := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hAF E a π
  have hpick : ∀ w : HeightOneSpectrum (𝓞 E), ∃ Q : ↥S,
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → Dec (F := E) A ≤ (Bc.res E Ω ↥Q.1.K).range) ∧
      (∀ w' : HeightOneSpectrum (𝓞 ↥Q.1.K), w'.under (𝓞 E) = w → GlobalTheory.UnitaryBC.IsSplitAt w') ∧
      RepIso (r Q) (ρ.comp (Bc.res E Ω ↥Q.1.K)) := by
    intro w
    have hfin := (Filter.eventually_cofinite.1 hev).image Subtype.val
    obtain ⟨Q, hQ, hQn⟩ := ((fam w).diff hfin).nonempty
    have hQS : Q ∈ S := famS Q hQ.2.2.1 hQ.2.2.2
    refine ⟨⟨Q, hQS⟩, hQ.1, hQ.2.1, ?_⟩
    by_contra hc
    exact hQn ⟨⟨Q, hQS⟩, hc, rfl⟩
  filter_upwards [hlf, hsat, hunr] with w hl hB hu
  obtain ⟨B, hB⟩ := hB
  refine ⟨B, hB, ?_⟩
  obtain ⟨Q, hdec, hsplit, hiso⟩ := hpick w
  exact frobEig_of_dec ι π Q.1 (P Q) (r Q) ρ w B hl hdec
    (fun w' hw' hB' => hHolds ↥Q.1.K Ω l ι a ha (P Q) (χ' Q) (hχ' Q) (r Q) (hr Q) w' (hsplit w' hw') B hB')
    (hP Q).1 hB hiso hu

end GlobalTheory.RoadU
end

end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem _root_.UpperTheory.Gal.Int.Inp.coreAll_of_core_inp : UpperTheory.Gal.Int.Inp.Inp → Core → CoreAll := by
  intro hI hC
  obtain ⟨hex, hh⟩ := hC
  have exg : Ex .good := GlobalTheory.GalCut.ex_good_of_ex_csd GlobalTheory.automorphicFormsFiniteGL hex
  have unrg : SphericalLevelCondition .good .unr := UpperTheory.Gal.Int.Inp.holdsS_good_unr hI (hh .unr)
  have crysg : SphericalLevelCondition .good .crys := UpperTheory.Gal.Int.Inp.holdsS_good_crys hI (hh .crys)
  refine ⟨UpperTheory.Gal.Int.Inp.ex_all_of_good hI exg unrg, ?_⟩
  intro c
  cases c with
  | unr => exact UpperTheory.Gal.Int.Inp.holdsS_all_unr hI unrg
  | dR => exact UpperTheory.Gal.Int.Inp.holdsS_dR_all_of_good hI (UpperTheory.Gal.Int.Inp.holdsS_good_dR_of_csd hI (hh .dR))
  | crys => exact UpperTheory.Gal.Int.Inp.holdsS_all_crys hI crysg
  | phi => exact UpperTheory.Gal.Int.Inp.holdsS_all_phi hI crysg (UpperTheory.Gal.Int.Inp.holdsS_good_phi hI (hh .crys) (hh .phi))

end GlobalTheory.RoadU

end

end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open GlobalTheory.RoadU

namespace GlobalTheory.Row9

theorem _root_.UpperTheory.Gal.Int.Inp.coreAll_of_rowStarCore_inp : UpperTheory.Gal.Int.Inp.Inp → GlobalTheory.RoadW.RowStarCore → CoreAll :=
  fun hI hR => UpperTheory.Gal.Int.Inp.coreAll_of_core_inp hI (GlobalTheory.RoadW.core_of_rowStarCore hR)

end GlobalTheory.Row9

end
