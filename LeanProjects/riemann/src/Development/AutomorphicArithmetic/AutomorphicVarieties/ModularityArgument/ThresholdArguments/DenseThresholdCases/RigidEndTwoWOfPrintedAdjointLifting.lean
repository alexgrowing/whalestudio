import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.LocalConditionRankThreeLinkOfInertiaOrdinary
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.FlagAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigidityEndomorphismWeightTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistInvarianceAutomorphic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private irr2 pair2 freeRes from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.CharpolyPowTwoByTwo
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.rigid_end_two_w_of_printed_adjoint_lifting :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.GalN.V.RigidityEndomorphismWeightTwo := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H hΨσ hF A _ _ r hr hII h11 K _ _ _ _ hK2 hK W hWc hW hdet haut hWit hfree θ hθ R hR
  obtain ⟨L, _, _, _, _, g₂, Φ, C₀, ⟨k⟩, hok, hbig, hseed⟩ := hF
  haveI := Db.algClo L Ω
  haveI := Db.algClo K Ω
  obtain ⟨-, ka, hka, hrig⟩ := _root_.UpperTheory.V.Th.linked_rigid_of_printed_adjoint_lifting hH hAd Ω l ι c N e ψ η σ g₂ B M H L Φ C₀ k hok hbig hseed
  have hof := UpperTheory.V.Z.Keep.ordFlag2 Ω l c N e ψ η σ g₂ B M H L Φ C₀ k hok A r
  generalize Chr.Psi l e (Chr.dirG ℚ Ω ψ) = Ψ at *
  have hl : l ∣ M := (dvd_mul_right l N).trans H.dvd
  have hσ : σ * σ = 1 := Db.cc_sq H.cc
  have hmk := Pr.marks_of_link k hok hl hσ hΨσ
  have hLη := Db.galL_le k
  obtain ⟨_, _⟩ := Db.algKL K L Ω (hK ▸ hLη)
  obtain ⟨_, hsol⟩ := Db.galKL K L k.ab
  haveI := Db.locHom c A
  haveI := (isNoetherianRing_iff_ideal_fg A).2 fun I => (IsPrincipalIdealRing.principal I).fg
  haveI : Normal ℚ L := k.ab.toIsGalois.to_normal
  have hb : U3.Block η r := fun g hg a b hab => Subtype.ext (hII.1 g hg a b hab)
  have hg₂ : g₂ ∈ η.ker := hmk.ηg
  have hgs : U3.gstar σ g₂ ∈ η.ker := by
    show η (σ * g₂⁻¹ * σ) = 1
    rw [map_mul, map_mul, map_inv, hmk.ηg, hmk.ηc]
    simp
  have hr' : Pr.OrdPt l η Ψ σ g₂ B r :=
    ⟨hr.red, hr.cont, ⟨hr.norm.atc,
      by rw [U3.zmat, Matrix.sub_apply, hb _ hg₂ _ _ (by decide), hb _ hgs _ _ (by decide), sub_zero],
      by rw [U3.zmat, Matrix.sub_apply, hb _ hg₂ _ _ (by decide), hb _ hgs _ _ (by decide), sub_zero]⟩, hr.away, hr.ord⟩
  have hFl : Flagged (W.comp (Base.galEmb ℚ K Ω)) := Dn.flagAll_of K Ω l 2 _ fun w hw =>
    let ⟨A', a1, κ, a2⟩ := hof hr' hb h11 K hK _ (fun s => hW _ (hK.ge (Base.galEmb_mem ℚ K Ω s))) w hw
    ⟨A', a1, κ, a2.choose_spec.2.1⟩
  obtain ⟨ρ', h1, h2, h3⟩ := Pr.exists_nrep2 k hok hl hσ r hr' hb
  have hηL : ∀ s : G L Ω, η (Base.galEmb ℚ L Ω s) = 1 := fun s => hLη (Base.galEmb_mem ℚ L Ω s)
  have hηK : ∀ s : G K Ω, η (Base.galEmb ℚ K Ω s) = 1 := fun s => hK.ge (Base.galEmb_mem ℚ K Ω s)
  let χ : G ℚ Ω →* (ResidueField A)ˣ := (Units.map ((residue A).comp (algebraMap c.O A)).toMonoidHom).comp Ψ
  have hU : U3.MatIrr ((Base.galOf ℚ L Ω).subgroupOf η.ker) (Pr.gm (W.comp η.ker.subtype)) := by
    refine irr2 (W.comp η.ker.subtype) (fun V hV => hII.2 V fun g hg v hv => ?_) (A.val : A →+* PadicAlgCl l)
      Subtype.val_injective (residue A) (χ.comp η.ker.subtype) (fun g => (r g).mat 0 0 + (r g).mat 2 2) (fun g => ?_) (fun g => ?_)
      _ (u := ⟨g₂, hg₂⟩) ?_ ?_ ?_
    · have := hV ⟨g, hg⟩ trivial v hv
      beta_reduce
      rw [← hW g hg]
      exact this
    · show _ = (W g).val.trace
      rw [hW g g.2, Matrix.trace_fin_two, map_add]
      rfl
    · have e2 : ∀ i, residue A ((r g).mat i i) = residue A (algebraMap c.O A ((U3.r0 η Ψ g).mat i i)) := fun i =>
        Ideal.Quotient.eq.2 (hr.red.red g i i)
      rw [map_add, e2, e2, ← map_inv]
      show _ = residue A (algebraMap c.O A (Ψ g : c.Oˣ)) + residue A (algebraMap c.O A (Ψ (g : G ℚ Ω)⁻¹ : c.Oˣ))
      simp [U3.GG.mat, U3.tor_val, U3.wt1]
    · rw [Subgroup.mem_subgroupOf, k.gal]
      exact ⟨k.g0.1, hg₂⟩
    · show (W g₂).val.det = 1
      rw [hdet, hmk.ηg]
      simp
    · intro h
      refine (hmk.Ψg.map ((residue A).comp (algebraMap c.O A))).ne_zero ?_
      rw [map_sub, map_pow, map_one, sub_eq_zero]
      have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val] at h'
      exact h'
  have hirr : Af.IsIrr (W.comp (Base.galEmb ℚ L Ω)) :=
    Db.irr_of_matIrr (by norm_num) (Base.galOf ℚ L Ω) (fun g => (W g).val)
      (fun V hV => hU V fun g hg v hv => hV g hg v hv) (Base.galEmb ℚ L Ω) (Base.range_galEmb ℚ L Ω).ge _ fun _ => rfl
  obtain ⟨J, hJ⟩ := pair2 (κ := Qbar l)
  have hpair : ∀ s : G ℚ Ω, η s = 1 →
      (W s).val.transpose * (J * (W σ)⁻¹).val * (W (σ * s * σ⁻¹)).val = (J * (W σ)⁻¹).val := fun s hs => by
    have e1 : J * (W σ)⁻¹ * W (σ * s * σ⁻¹) = J * W s * (W σ)⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    rw [Matrix.mul_assoc, ← Units.val_mul, e1, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, hdet,
      hs, Units.val_mul]
    simp
  have halg : Af.IsAlgChar ι (1 : G ℚ Ω →* (Qbar l)ˣ) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hH ℚ Ω l ι).1 _ continuous_const fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, 1, one_pos, fun s _ => by simp⟩
  have hautL : Af.IsAut ι (W.comp (Base.galEmb ℚ L Ω)) :=
    (Z.Bc.solC_of_solDescent (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida hH) ℚ K L Ω hsol ⟨inferInstance, Or.inr ⟨hK2, inferInstance⟩⟩ inferInstance
      inferInstance l ι 2 (by norm_num) (W.comp (Base.galEmb ℚ K Ω)) 1 (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hirr halg
      (fun _ _ _ _ => rfl) ⟨σ, J * (W σ)⁻¹, H.cc, fun s s' hs => by
        have hs' : Base.galEmb ℚ K Ω s' = σ * Base.galEmb ℚ K Ω s * σ⁻¹ := hs
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hs', hpair _ (hηK s)]
        simp⟩).1 ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hH K Ω l ι 2 _).2.1.2 haut)
  have hcsd : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (W.comp (Base.galEmb ℚ L Ω)) ka) := by
    obtain ⟨hc, art, χ, a, h'⟩ := hka.alg
    have hCL := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hH L Ω l ι 2 _).2.1.1 hautL
    have hWL : _root_.UpperTheory.V.Z.Win.WitA ι (W.comp (Base.galEmb ℚ L Ω)) :=
      _root_.UpperTheory.V.Z.Win.Dn.automorphy_up_base_change (r := W.comp (Base.galEmb ℚ K Ω)) L hH hsol (by norm_num) (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hirr
        ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, 1, σ, J * (W σ)⁻¹, halg,
          fun _ _ _ _ => rfl, H.cc, fun s s' hs => by
            have hs' : Base.galEmb ℚ K Ω s' = σ * Base.galEmb ℚ K Ω s * σ⁻¹ := hs
            rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hs', hpair _ (hηK s)]
            simp⟩ haut hFl hWit
    refine _root_.UpperTheory.GalN.V.mkCsd'_alt ?_ fun _ => _root_.UpperTheory.V.Z.Win.Dn.twist'_alt hH.toClassicalTheorems ⟨χ, hc, art, a, h'⟩ hc hWL
    refine _root_.UpperTheory.GalN.V.csdOf0_alt hH ℚ L Ω inferInstance l ι 2 (by norm_num) _ σ (J * (W σ)⁻¹) H.cc
      (_root_.UpperTheory.V.Af.twist_invariance_automorphic hH L Ω l ι 2 _ ka hautL ⟨χ, hc, art, a, h'⟩) fun s s' hs => ?_
    have hs' : Base.galEmb ℚ L Ω s' = σ * Base.galEmb ℚ L Ω s * σ⁻¹ := hs
    have hp := hpair _ (hηL s)
    rw [← hs'] at hp
    rw [MonoidHom.zpow_apply, ← hka.conj s s' hs', Units.val_mul (ka s)]
    simp only [Af.tw_val, MonoidHom.comp_apply, Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, hp]
    rw [mul_comm, mul_smul]
  obtain ⟨s, V, ρ, a1, a2, a3⟩ := hrig A ρ' h1 h3 (W.comp (Base.galEmb ℚ L Ω))
    (fun s => by rw [h2, MonoidHom.comp_apply, hW _ (hηL s)]; rfl) hirr hcsd (freeRes L W hfree)
  refine adDown Ω l K L hK2 (hK ▸ hLη) s V 2 _ _ R (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hR ρ ka
    (fun g t ht => ?_) (fun g g' t hg ht => ?_) a3
  · rw [a1]
    show _ • (W (Base.galEmb ℚ L Ω g)).val = _ • (W (Base.galEmb ℚ K Ω t)).val
    rw [ht]
  · have : θ (Base.galEmb ℚ K Ω t) = 1 := Units.ext (by rw [hθ, hηK]; simp)
    rw [← a2 g g' hg]
    exact mul_eq_left.2 this
end
