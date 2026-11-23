import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevChiFlagLEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfAdjointIdempotentPosType

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.ProjectorAdjoint

open Formalism.IndefR.Lev

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G] {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem isLiftFlagGroup_inv {g : G0 L.Pg L.r} {κ : GA D V} (h : IsLevelLift V β L g κ) : IsLevelLift V β L g⁻¹ κ⁻¹ := by
  refine ⟨(GfC V).inv_mem h.1, ?_, ?_⟩
  · rw [map_inv]; exact Subgroup.inv_mem _ h.2.1
  · rw [map_inv, rTup_inv h.2.1, h.2.2]

theorem levChi_inv {g : G0 L.Pg L.r} {κ : GA D V} (h : IsLevelLift V β L g κ) :
    (levChi V β (flagL L) κ⁻¹)⁻¹ = star (levChi V β (flagL L) κ)⁻¹ := by
  have h1 : κ ∈ levG V β (flagL L) := ⟨h.1, h.2.1, Subgroup.mem_top _⟩
  have hn := GlobalTheory.norm_levChi_flagL_eq_one V β L κ h1
  have h2 : levChi V β (flagL L) κ⁻¹ * levChi V β (flagL L) κ = 1 := by
    have a := levFn_flag_mul (V := V) (β := β) (L := L) (isLiftFlagGroup_inv h).2.1 h.2.1
    have b := levFn_flag_mul (V := V) (β := β) (L := L) (Subgroup.one_mem _) (Subgroup.one_mem _)
    rw [mul_one, left_eq_mul] at b
    rw [← map_mul, inv_mul_cancel, map_one, b] at a
    unfold levChi
    rw [← Units.val_mul, ← a, Units.val_one]
  rw [inv_eq_of_mul_eq_one_right h2, Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

theorem integral_act (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (g : G0 L.Pg L.r) {φ ψ : GA D V → ℂ}
    (hφ : ∀ γ ∈ GQ V, ∀ x, φ (γ * x) = φ x) (hψ : ∀ γ ∈ GQ V, ∀ x, ψ (γ * x) = ψ x) (ht : HasType V β (flag1L L) ψ) :
    ∫ x in 𝓕, star (actG0 V β L g φ x) * ψ x ∂μ = ∫ x in 𝓕, star (φ x) * actG0 V β L g⁻¹ ψ x ∂μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : SecondCountableTopology (GA D V) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  by_cases hk : ∃ κ, IsLevelLift V β L g κ
  · have hκ := hk.choose_spec
    have h1 := level_action_spec ht ⟨_, isLiftFlagGroup_inv hκ⟩ _ (isLiftFlagGroup_inv hκ)
    have h2 := (GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (φ x) * actG0 V β L g⁻¹ ψ x) hk.choose h𝓕
      fun γ hγ x => by rw [h1, h1, mul_assoc γ, hφ γ hγ, hψ γ hγ]).2
    rw [← h2]
    refine integral_congr_ae (.of_forall fun x => ?_)
    show star (actG0 V β L g φ x) * ψ x = star (φ (x * hk.choose)) * actG0 V β L g⁻¹ ψ (x * hk.choose)
    rw [h1, levChi_inv hκ, mul_inv_cancel_right, actG0, dif_pos hk, star_mul']
    ring
  · have hk' : ¬ ∃ κ, IsLevelLift V β L g⁻¹ κ := fun ⟨κ, h⟩ => hk ⟨κ⁻¹, by simpa using isLiftFlagGroup_inv h⟩
    simp [actG0, dif_neg hk, dif_neg hk']

theorem ipM_gaL (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hc : ∀ g, c g⁻¹ = star (c g)) {X Y : MMap M}
    (hX : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)))
    (hY : Y ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    ipM M μ 𝓕 (postOn M (gaL V β L eG c) X) Y = ipM M μ 𝓕 X (postOn M (gaL V β L eG c) Y) := by
  have hs := GlobalTheory.MultFinite.schurMult (θ := θ) (M := M) (J := (levG V β (flag1L L) : Set (GA D V))) (χ := levChi V β (flag1L L))
    hP μ 𝓕 hθ hμ h𝓕
  have ha : ∀ g, ∀ Z ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)),
      postOn M (actL V β L g) Z ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) :=
    fun g Z hZ => GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity θ M hθ β L g Z hZ _ fun _ => rfl
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D _ _ M)
  have h1 := (ipM_spec M μ 𝓕 _ _ (hs _ (GlobalTheory.ProjectedLift.postOn_gaL_mem hθ eG c hX) _ hY) v v).2
  have h2 := (ipM_spec M μ 𝓕 _ _ (hs _ hX _ (GlobalTheory.ProjectedLift.postOn_gaL_mem hθ eG c hY)) v v).2
  refine mul_right_cancel₀ hv (h1.symm.trans (Eq.trans ?_ h2))
  have e1 : ∀ x, star (postOn M (gaL V β L eG c) X v x) * Y v x =
      ∑ g, c g⁻¹ * (star (actG0 V β L (eG g) (X v) x) * Y v x) := fun x => by
    simp only [gaL, postOn_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum,
      star_mul', Finset.sum_mul, hc, mul_assoc]
    rfl
  have e2 : ∀ x, star (X v x) * postOn M (gaL V β L eG c) Y v x =
      ∑ g, c g⁻¹ * (star (X v x) * actG0 V β L (eG g)⁻¹ (Y v) x) := fun x => by
    simp only [gaL, postOn_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
    rw [Equiv.inv_apply, inv_inv, map_inv, inv_inv, mul_left_comm]
    rfl
  have hX' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ X).1 hX
  have hY' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ Y).1 hY
  simp only [e1, e2]
  rw [integral_finsetSum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [integral_const_mul, integral_const_mul, integral_act hμ h𝓕 _ (hX'.aut v).left (hY'.aut v).left
      (GlobalTheory.hasType_of_mem_mult θ M β _ Y hY v)]
  · exact fun g _ => ((hs _ hX _ (ha (eG g)⁻¹ _ hY)).choose_spec v v).1.const_mul _
  · exact fun g _ => ((hs _ (ha (eG g) _ hX) _ hY).choose_spec v v).1.const_mul _

end Act

theorem eC_inv {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hr : R.grp_record) (g : G) :
    RealDat.eC (A := A) D.what₂.embLL g⁻¹ = star (RealDat.eC (A := A) D.what₂.embLL g) := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  have : Finite (G0g D.nd) := Finite.of_equiv G eR.toEquiv
  obtain ⟨h1, h2⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D
  unfold RealDat.eC
  rw [h, h, map_inv]
  exact GlobalTheory.RowLev.GroupAlgPos.isSA_central _ h2 (fun a => (Subalgebra.mem_center_iff.1 h1 a).symm) _

theorem ipM_e0 : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ U ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (Formalism.IndefR.Lev.levChi _ (R.βY 0) (R.dat0 R.triv)), ∀ U' ∈ R.EEat R.triv, ipM (R.MY 0) R.ν0 R.fd0 (postOn (R.MY 0) R.e0 U) U' = ipM (R.MY 0) R.ν0 R.fd0 U U' := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F _ hG hM U hU U' hU'
  have h : postOn (R.MY 0) R.e0 U' = U' := sub_eq_zero.1 (LinearMap.mem_ker.1 hU'.2)
  exact (ipM_gaL (L := R.dat0 R.triv) hP hM.inf hM.ν0.1.1 hM.ν0.2 R.eG _ (eC_inv R hG.record) hU hU'.1).trans
    (congrArg (ipM (R.MY 0) R.ν0 R.fd0 U) h)

end GlobalTheory.ProjectorAdjoint

end
