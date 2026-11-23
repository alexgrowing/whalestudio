import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasFr

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem upq_mat_mul {p q : ℕ} (a b : UpqT p q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := rfl

theorem upq_mat_one {p q : ℕ} : UpqT.mat (1 : UpqT p q) = 1 := rfl

theorem upq_mat_inv_mul {p q : ℕ} (a : UpqT p q) : UpqT.mat a⁻¹ * UpqT.mat a = 1 := by
  rw [← upq_mat_mul, inv_mul_cancel, upq_mat_one]

theorem upq_mat_mul_inv {p q : ℕ} (a : UpqT p q) : UpqT.mat a * UpqT.mat a⁻¹ = 1 := by
  rw [← upq_mat_mul, mul_inv_cancel, upq_mat_one]

variable {D : D7} {V : HSp D}

set_option quotPrecheck false in
local notation "ρv" v => (Formalism.L2.Host.tauPl D).symm v

theorem cond_change {p q : ℕ} (A₀ A : Matrix (Fin p ⊕ Fin q) (Fin V.rank) ℂ) (u : UpqT p q)
    (hu : A = UpqT.mat u * A₀) (B : Set (UpqT p q)) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (∃ b ∈ B, UpqT.mat b * A = A * X) ↔ ∃ c ∈ (fun c => u * c * u⁻¹) ⁻¹' B, UpqT.mat c * A₀ = A₀ * X := by
  subst hu
  constructor
  · rintro ⟨b, hb, hbx⟩
    refine ⟨u⁻¹ * b * u, ?_, ?_⟩
    · show u * (u⁻¹ * b * u) * u⁻¹ ∈ B
      simpa [mul_assoc] using hb
    · calc UpqT.mat (u⁻¹ * b * u) * A₀ = UpqT.mat u⁻¹ * (UpqT.mat b * (UpqT.mat u * A₀)) := by
            simp only [upq_mat_mul, Matrix.mul_assoc]
        _ = UpqT.mat u⁻¹ * (UpqT.mat u * A₀ * X) := by rw [hbx]
        _ = A₀ * X := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, upq_mat_inv_mul, Matrix.one_mul]
  · rintro ⟨c, hc, hcx⟩
    refine ⟨u * c * u⁻¹, hc, ?_⟩
    calc UpqT.mat (u * c * u⁻¹) * (UpqT.mat u * A₀) = UpqT.mat u * (UpqT.mat c * A₀) := by
          simp only [upq_mat_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (UpqT.mat u⁻¹), upq_mat_inv_mul, Matrix.one_mul]
      _ = UpqT.mat u * A₀ * X := by rw [hcx, Matrix.mul_assoc]

theorem isMeasLevW_exists
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hgH : ∀ ρ m, good ρ m → m.IsHaarMeasure) (hex : ∀ ρ, ∃ m, good ρ m)
    (huq : ∀ ρ m m', good ρ m → good ρ m' → m' = m) (hS : V.SigOK)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hK : IsLevelA V K) : ∃ μ, Lev.IsMeasLevW V K good μ := by
  obtain ⟨F⟩ := MF.frA_nonempty hS
  choose m0 hm0 using hex
  haveI : ∀ ρ, (m0 ρ).IsHaarMeasure := fun ρ => hgH ρ _ (hm0 ρ)
  obtain ⟨g1, g2, g3⟩ := gf_facts (MF.toFrames F)
  obtain ⟨h1, h2, h3, h4, h5⟩ := ga_facts D V
  obtain ⟨hkc, hko⟩ := kf_isCompact_isOpen_of_levelA (MF.toFrames F) K hK
  set νf : Measure (UI.instV (MF.toFrames F)).Gf := Measure.haar
  have hk0 : νf (kf (MF.toFrames F) K) ≠ 0 := (hko.measure_pos νf ⟨1, K.one_mem⟩).ne'
  have hkt : νf (kf (MF.toFrames F) K) ≠ ⊤ := hkc.measure_lt_top.ne
  set μf := (νf (kf (MF.toFrames F) K))⁻¹ • νf
  haveI hμf : μf.IsHaarMeasure := by
    exact Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr hkt) (ENNReal.inv_ne_top.mpr hk0)
  haveI hmv : ∀ v, ((m0 (ρv v)).map (MF.phiR F v)).IsHaarMeasure := fun v =>
    (MF.phiR F v).toMulEquiv.isHaarMeasure_map (m0 (ρv v)) (MF.phiR F v).continuous (MF.phiR F v).symm.continuous
  set μi := Measure.pi fun v => (m0 (ρv v)).map (MF.phiR F v)
  have hμi : μi.IsHaarMeasure := Measure.pi.isHaarMeasure _
  have hsi : SFinite μi := inferInstance
  have hsf : SFinite μf := inferInstance
  have hmm : MeasurableMul (UI.instV (MF.toFrames F)).Gf := inferInstance
  have hmi : MeasurableMul ((v : InfinitePlace D.host.F) → Formalism.REAL.UJ ((MF.toFrames F).ε v)) := inferInstance
  have hprod : (μi.prod μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure μi μf
  let μA : Measure (UI.instV (MF.toFrames F)).GA := μi.prod μf
  haveI hμA : μA.IsHaarMeasure := hprod
  refine ⟨μA.map (UI.brg (MF.toFrames F)), ?_, ?_⟩
  · exact (UI.brg (MF.toFrames F)).toMulEquiv.isHaarMeasure_map μA (UI.brg (MF.toFrames F)).continuous
      (UI.brg (MF.toFrames F)).symm.continuous
  refine ⟨⟨thetaC D, isInfFam_thetaC D⟩, fun θ hθ => ?_⟩
  rw [eq_thetaC D hθ]
  refine ⟨⟨F.A, F.hA⟩, fun A hA => ?_⟩
  refine ⟨⟨m0, hm0⟩, fun m hm => ?_⟩
  have hmm : m = m0 := funext fun ρ => huq ρ _ _ (hm0 ρ) (hm ρ)
  subst hmm
  intro B hB
  choose u hu using fun ρ => MF.frame_change (F.e ρ) (gramAt D V ρ) (isUnit_iff_ne_zero.mpr (MF.gramAt_det ρ))
    (MF.gramAt_herm ρ) (F.A ρ) (A ρ) (F.hA ρ) (hA ρ)
  set B' := fun ρ => (fun c => u ρ * c * (u ρ)⁻¹) ⁻¹' B ρ
  have hB' : ∀ ρ, m ρ (B' ρ) = m ρ (B ρ) := by
    intro ρ
    have hc : Continuous (fun c => u ρ * c * (u ρ)⁻¹) := (continuous_const.mul continuous_id).mul continuous_const
    show m ρ ((fun c => u ρ * c * (u ρ)⁻¹) ⁻¹' B ρ) = _
    rw [← Measure.map_apply hc.measurable (hB ρ)]
    have := MU.map_conj_upq (m ρ) (u ρ)⁻¹
    simp only [inv_inv] at this
    rw [this]
  have hset : {h : GA D V | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ b ∈ B ρ,
      UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (thetaC D ρ) h} =
      {h : GA D V | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ c ∈ B' ρ,
      UpqT.mat c * F.A ρ = F.A ρ * infMat D.sp.cm.sig V.gram (thetaC D ρ) h} := by
    ext h
    simp only [Set.mem_setOf_eq]
    refine and_congr Iff.rfl (forall_congr' fun ρ => ?_)
    exact cond_change (F.A ρ) (A ρ) (u ρ) (hu ρ) (B ρ) _
  rw [hset, ← Finset.prod_congr rfl fun ρ _ => hB' ρ]
  have hpre : (UI.brg (MF.toFrames F)) ⁻¹' {h : GA D V | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ c ∈ B' ρ,
      UpqT.mat c * F.A ρ = F.A ρ * infMat D.sp.cm.sig V.gram (thetaC D ρ) h} =
      (Set.univ.pi fun v => MF.phiR F v '' B' (ρv v)) ×ˢ kf (MF.toFrames F) K := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ_pi]
    rw [finE_brg, and_comm]
    refine and_congr ?_ Iff.rfl
    constructor
    · intro h v _
      exact (MF.cond_iff F x v (B' (ρv v))).mp (h (ρv v))
    · intro h ρ
      have := (MF.cond_iff F x (Formalism.L2.Host.tauPl D ρ) (B' (ρv (Formalism.L2.Host.tauPl D ρ)))).mpr
        (h (Formalism.L2.Host.tauPl D ρ) (Set.mem_univ _))
      rw [Equiv.symm_apply_apply] at this
      exact this
  have hmap := (UI.brg (MF.toFrames F)).toHomeomorph.toMeasurableEquiv.map_apply
    (μ := μi.prod μf) {h : GA D V | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ c ∈ B' ρ,
      UpqT.mat c * F.A ρ = F.A ρ * infMat D.sp.cm.sig V.gram (thetaC D ρ) h}
  refine Eq.trans hmap ?_
  refine Eq.trans (congrArg (μi.prod μf) hpre) ?_
  rw [Measure.prod_prod, Measure.pi_pi]
  have hf1 : μf (kf (MF.toFrames F) K) = 1 := by
    show ((νf (kf (MF.toFrames F) K))⁻¹ • νf) (kf (MF.toFrames F) K) = 1
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hk0 hkt]
  rw [hf1, mul_one]
  have hv : ∀ v, ((m (ρv v)).map (MF.phiR F v)) (MF.phiR F v '' B' (ρv v)) = m (ρv v) (B' (ρv v)) := by
    intro v
    rw [show ((m (ρv v)).map (MF.phiR F v)) = (m (ρv v)).map (MF.phiR F v).toHomeomorph.toMeasurableEquiv from rfl,
      MeasurableEquiv.map_apply]
    congr 1
    exact Set.preimage_image_eq _ (MF.phiR F v).injective
  simp only [hv]
  exact Fintype.prod_equiv (Formalism.L2.Host.tauPl D).symm _ _ fun v => rfl

variable (D)

theorem measLevExists_holds : MeasLevExists D := fun V hS K hK =>
  isMeasLevW_exists (V := V) (fun _ m => Lev.IsMinf m) (fun _ _ h => h.1) (fun _ => MU.isMinf_exists _ _)
    (fun _ _ _ h h' => MU.isMinf_unique h h') hS K hK

theorem measLevDefExists_holds : MeasLevDefExists D := fun V hS hD K hK =>
  isMeasLevW_exists (V := V) (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) (fun _ _ h => h.1)
    (fun ρ => by
      rcases hD (tauE D ρ) with h | h
      · haveI : CompactSpace (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) := by rw [h]; infer_instance
        exact MU.prob_exists
      · haveI : CompactSpace (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) := by rw [h]; infer_instance
        exact MU.prob_exists)
    (fun _ _ _ h h' => MU.prob_unique h h') hS K hK

theorem measFDExists_holds : MeasFDExists D := fun V hS K hK => by
  obtain ⟨μ, hμ⟩ := measLevExists_holds D V hS K hK
  obtain ⟨𝓕, -, h𝓕⟩ := fundDomExists_holds D V
  exact ⟨μ, 𝓕, hμ, h𝓕 μ⟩

end Formalism.IndefR.Eqv

end
