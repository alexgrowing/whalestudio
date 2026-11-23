import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.LocalConditionRankThreeLinkOfInertiaOrdinary
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.FlagAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.IneOfKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigEnd3
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutCsdIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UpCsd0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private tf cyc_conj isIrr_of_matIrr matIrr_tw pair_of cont_hom lc_of_ker ad_down left_conj from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.IsIrrOfMatIrr
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
namespace UpperTheory.V.Th.End3
open UpperTheory.V.U3 UpperTheory.V.Base
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing
attribute [local instance] tf
open UpperTheory.V.Z.Win
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {K L : Type} [Field K] [NumberField K]
  [IsCMField K] [Algebra K Ω] [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {σ : G ℚ Ω} {R : G ℚ Ω →* GG 3 (PadicAlgCl l)} {ρ : G K Ω →* GL (Fin 3) (Qbar l)}
theorem isAutCsdA_twist_comp_galEmb_of_repIso_of_flagged (hH : _root_.UpperTheory.V.Af.HypothesesH') (hab : IsAbelianGalois ℚ L) (ι : Qbar l ≃+* ℂ) (hσ : Sd.IsCC σ)
    (hρ : ∀ s, ρ s = (R (galEmb ℚ K Ω s)).left) (hK : ∀ s, (R (galEmb ℚ K Ω s)).right = 1)
    (hc : (R σ).right = -1) (hatc : (R σ).mat = 1) (hρc : Continuous ρ)
    (hiL : MatIrr ⊤ fun g => (ρ.comp (galEmb K L Ω) g).val) {ρ₀ : G K Ω →* GL (Fin 3) (Qbar l)} (hiso : Af.RepIso ρ₀ ρ) (hFl : Flagged ρ)
    (haut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw ρ₀ (cycBar K Ω l)⁻¹)) :
    _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (ρ.comp (galEmb K L Ω)) (cycBar L Ω l)⁻¹) := by
  obtain ⟨_, hsol⟩ := Db.galKL K L hab
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := hsol
  obtain ⟨h', hiso⟩ := hiso
  have et : Af.tw (ρ.comp (galEmb K L Ω)) (cycBar L Ω l)⁻¹ = (Af.tw ρ (cycBar K Ω l)⁻¹).comp (galEmb K L Ω) :=
    MonoidHom.ext fun s => Units.ext <| by
      rw [Af.tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, Af.tw_val]
      rfl
  have hiT := isIrr_of_matIrr _ (matIrr_tw _ (cycBar L Ω l)⁻¹ hiL)
  rw [et] at hiT ⊢
  haveI := algClo K Ω
  have hcT : Continuous (Af.tw ρ (cycBar K Ω l)⁻¹) := Af.Bc.irrBasic.2 _ _ _ _ _ hρc (cyc_cont K Ω l).inv
  have hisoT : Af.RepIso (Af.tw ρ₀ (cycBar K Ω l)⁻¹) (Af.tw ρ (cycBar K Ω l)⁻¹) := ⟨h', fun s => Units.ext (by
    rw [Af.tw_val, hiso, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Af.tw_val, Matrix.mul_smul,
      Matrix.smul_mul])⟩
  have hN := _root_.UpperTheory.GalN.V.autCsd_iso_alt hisoT (_root_.UpperTheory.GalN.V.csdN'_alt hH.toClassicalTheorems (by norm_num) haut)
  have hpr : Sd.IsPair σ (Af.tw ρ (cycBar K Ω l)⁻¹) (cycBar K Ω l ^ (1 - ((3 : ℕ) : ℤ))) (Jgl _ 3) := fun s s' hs => by
    have h1 : cycBar K Ω l s' = cycBar K Ω l s := by
      show cycBar ℚ Ω l (galEmb ℚ K Ω s') = cycBar ℚ Ω l (galEmb ℚ K Ω s)
      rw [hs, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    have h3 : (cycBar K Ω l ^ (1 - ((3 : ℕ) : ℤ))) s = (cycBar K Ω l s)⁻¹ * (cycBar K Ω l s)⁻¹ := by
      rw [MonoidHom.zpow_apply, show (1 - ((3 : ℕ) : ℤ)) = -1 + -1 by norm_num, _root_.zpow_add, _root_.zpow_neg_one]
    rw [Af.tw_val, Af.tw_val, MonoidHom.inv_apply, MonoidHom.inv_apply, h1, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul, h3]
    exact congrArg _ (pair_of hρ hK hc hatc s s' hs)
  have halg : Af.IsAlgChar ι (cycBar ℚ Ω l ^ (1 - ((3 : ℕ) : ℤ))) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hH ℚ Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, 1 - ((3 : ℕ) : ℤ), 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, _root_.zpow_neg, mul_inv_cancel]
  suffices h0 : AutCsd0 ι ((Af.tw ρ (cycBar K Ω l)⁻¹).comp (galEmb K L Ω)) from
    _root_.UpperTheory.GalN.V.mkCsd'_alt h0 fun _ => _root_.UpperTheory.V.Z.Win.Dn.automorphy_up_base_change L hH hsol (by norm_num) hcT hiT
      ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _, σ, Jgl _ 3, halg,
        Ws.auSign _, hσ, hpr⟩ hN.1.c0 (((flagLaws K Ω l 3 ρ).2.1 _).2.1 hFl) (hN.2 hcT)
  refine _root_.UpperTheory.V.Th.End3.autCsd0_comp_galEmb_of_isPair_of_isIrr_of_isAut hH K L Ω l ι 3 (by norm_num) (Af.tw ρ (cycBar K Ω l)⁻¹) σ hσ
    (Af.Bc.irrBasic.2 _ _ _ _ _ hρc (cyc_cont K Ω l).inv) (Jgl _ 3) hpr hiT
    (isAut_iso ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hH K Ω l ι 3 _).2.2 haut) ⟨h', fun s => Units.ext ?_⟩
      ((Af.Bc.irrBasic.1 _ _ _ 3 _).1 _ hiT))
  rw [Af.tw_val, hiso, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Af.tw_val, Matrix.mul_smul,
      Matrix.smul_mul]
end UpperTheory.V.Th.End3
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing
open UpperTheory.V.Z.Win
set_option maxHeartbeats 400000 in
open UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Th.End3 in
theorem UpperTheory.V.Z.Win.Dn.rigEnd3_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Th.RigEnd3Alt := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H hΨ hF A _ _ r hr hirr K _ _ _ _ hK2 hker ρ hρ haut hfree
  obtain ⟨L, _, _, _, _, g₂, Φ, C₀, ⟨k⟩, hok, hbig, hseed⟩ := hF
  haveI := algClo K Ω
  haveI := algClo L Ω
  obtain ⟨hcpl, hloc, hcont⟩ := sub_facts c A
  have hl : l ∣ M := (dvd_mul_right l N).trans H.dvd
  have hσ : σ * σ = 1 := Db.cc_sq H.cc
  have hM := Pr.marks_of_link k hok hl hσ hΨ
  have h2 : IsUnit (2 : c.O) := by
    rw [← residue_ne_zero_iff_isUnit, map_ofNat]
    intro h0
    exact hok.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
      ((CharP.cast_eq_zero_iff (ResidueField c.O) l 2).1 (by exact_mod_cast h0)))
  obtain ⟨h, -, hr'⟩ := ordPt_renorm hr (lc_of_ker η (hker ▸ (galEmbTop ℚ K Ω).2.1)) h2 hM
  let h' : GL (Fin 3) (Qbar l) := Matrix.GeneralLinearGroup.map (A.val : A →+* PadicAlgCl l) h
  have eR : UnitaryThreeInertia.push A.val (conjBy h r) = conjBy h' (UnitaryThreeInertia.push A.val r) := map_conjBy _ h r
  refine h1fZero_conjBy _ h' ?_
  rw [← eR]
  have hmat : ∀ g ∈ η.ker, (UnitaryThreeInertia.push A.val (conjBy h r) g).left = h' * (UnitaryThreeInertia.push A.val r g).left * h'⁻¹ := fun g hg => by
    rw [eR, conjBy_left, show (UnitaryThreeInertia.push A.val r g).right = 1 from (hr.red.mult g).trans hg, sgnAct_one]
  have hmem : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ η.ker := fun s => hker ▸ galEmb_mem ℚ K Ω s
  let ρ' : G K Ω →* GL (Fin 3) (Qbar l) := (MulAut.conj h').toMonoidHom.comp ρ
  have hiso : ∀ s, ρ' s = h' * ρ s * h'⁻¹ := fun _ => rfl
  have hρ' : ∀ s, ρ' s = (UnitaryThreeInertia.push A.val (conjBy h r) (galEmb ℚ K Ω s)).left := fun s => by
    rw [hmat _ (hmem s), hiso, show ρ s = _ from Units.ext (hρ s)]
  have hLη : galOf ℚ L Ω ≤ η.ker := Db.galL_le k
  have hirr' : MatIrr (galOf ℚ L Ω) (mats (UnitaryThreeInertia.push A.val (conjBy h r))) :=
    matIrr_conj (hirr _ (galEmbTop ℚ L Ω).2.1 hLη) h' fun g hg => congrArg Units.val (hmat g (hLη hg))
  generalize conjBy h r = r' at hr' hρ' hirr'
  have hFl : Flagged ρ' := (Dn.localConditionRankThreeLink_of_inertia_ordinary Dn.ineOfKer_of Dn.flagAll_of Ω l c N e ψ η σ g₂ B M H L Φ C₀ k hok A r' hr' K hker ρ'
    fun s => congrArg Units.val (hρ' s)).2
  have hright : ∀ g, (UnitaryThreeInertia.push A.val r' g).right = η g := hr'.red.mult
  have hatc : (UnitaryThreeInertia.push A.val r' σ).mat = 1 := by
    rw [MonoidHom.comp_apply, GG.map_mat, hr'.norm.atc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc : (UnitaryThreeInertia.push A.val r' σ).right = -1 := (hright σ).trans hM.ηc
  have hK : ∀ s, (UnitaryThreeInertia.push A.val r' (galEmb ℚ K Ω s)).right = 1 := fun s => (hright _).trans (hmem s)
  have hρc : Continuous ρ' := by
    refine cont_hom _ (continuous_matrix fun a b => ?_)
    simp only [hρ']
    exact (hcont _ (fun g => (r' g).mat a b) fun n => (hr'.cont n).comp fun X => X a b).comp (galEmbTop ℚ K Ω).1.continuous
  obtain ⟨_, _⟩ := Db.algKL K L Ω (hLη.trans hker.le)
  have hiL : MatIrr ⊤ fun g => (ρ'.comp (galEmb K L Ω) g).val := fun W hW => hirr' W fun g hg => by
    rw [← range_galEmb] at hg
    obtain ⟨s, rfl⟩ := hg
    have := hW s trivial
    beta_reduce at this
    rwa [MonoidHom.comp_apply, hρ'] at this
  have hautL := _root_.UpperTheory.V.Th.End3.isAutCsdA_twist_comp_galEmb_of_repIso_of_flagged hH k.ab ι H.cc hρ' hK hc hatc hρc hiL ⟨h', hiso⟩ hFl haut
  obtain ⟨ν, n1, n2, n3⟩ := Pr.exists_nrep3 k hok hl hσ r' hr'
  have key := (_root_.UpperTheory.V.Th.linked_rigid_of_printed_adjoint_lifting hH hAd Ω l ι c N e ψ η σ g₂ B M H L Φ C₀ k hok hbig hseed).1
  have n4 : ∀ s, (ρ'.comp (galEmb K L Ω) s).val = (ν.r (k.p0 s)).map A.val := fun s => by
    rw [n2, MonoidHom.comp_apply, hρ']
    rfl
  have n5 : ∀ v i, ∀ g ∈ Φ.Iv v, (ν.ψ v i g).val =
      algebraMap c.O A (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val := fun v i g hg => by
    rw [n3 v i g hg, Fr.w, if_pos rfl]
    rfl
  exact ad_down hK2 H.cc hρ' hK hc hatc hρc
    (key A ν n1 n5 _ n4 (isIrr_of_matIrr _ hiL) hautL (freeAt_res (freeAt_iso hfree ⟨h', hiso⟩)))
end
