import Mathlib
import Formalism.PeriodIntegrals.BesselPeriodGGP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.FormalDegreeHaarQuotient
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NodeGapNoncompact

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselPeriodCompare

open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open Formalism.FourierDecayAlt.B2 (IsClosedSubgroup mulM invM)
open Formalism.FourierDecayAlt.P.B2x1
open GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient (Mat leviW IsClosedMatGroup)

variable {k r : ℕ}

theorem closedSubgroup_iff (U : Set (Mat k r)) : IsClosedMatGroup U ↔ IsClosedSubgroup U :=
  ⟨fun h => ⟨h.2.1, h.2.2.1, fun a ha => (h.2.2.2 a ha).2, fun a ha => (h.2.2.2 a ha).1, h.1⟩,
    fun h => ⟨h.closed, h.one_mem, h.mul_mem, fun a ha => ⟨h.unit a ha, h.inv_mem a ha⟩⟩⟩

theorem exists_pos_lt_top {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (h : μ ≠ 0) : ∃ t : Set X, μ t ≠ 0 ∧ μ t ≠ ⊤ := by
  have h0 : (0 : ℝ≥0∞) < μ Set.univ := by
    rw [pos_iff_ne_zero]; exact fun h' => h (Measure.measure_univ_eq_zero.mp h')
  obtain ⟨t, -, -, h1, h2⟩ := Measure.exists_subset_measure_lt_top MeasurableSet.univ h0
  exact ⟨t, h1.ne', h2.ne⟩

theorem haar_unique {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : PI.BesselPeriodGGP.IsHaarOn U ν) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  obtain ⟨m1, m2, m3, m4⟩ := hμ
  obtain ⟨n1, n2, n3, n4⟩ := hν
  have em : (pull hU μ).map inc = μ := map_pull μ m3
  have en : (pull hU ν).map inc = ν := map_pull ν n3
  have : (pull hU μ).IsMulLeftInvariant := pull_left μ m4
  have : (pull hU ν).IsMulLeftInvariant := pull_left ν n4
  have : SigmaFinite (pull hU μ) :=
    SigmaFinite.of_map _ inc_memb.measurable.aemeasurable (by rw [em]; exact m1)
  have : SigmaFinite (pull hU ν) :=
    SigmaFinite.of_map _ inc_memb.measurable.aemeasurable (by rw [en]; exact n1)
  obtain ⟨s, s0, s1⟩ := exists_pos_lt_top (pull hU ν) (by
    intro h; apply n2; rw [← en, h, Measure.map_zero])
  have e := measure_eq_div_smul (pull hU μ) (pull hU ν) s0 s1
  generalize pull hU μ s / pull hU ν s = c at e
  have e' : μ = c • ν := by rw [← em, e, Measure.map_smul, en]
  refine ⟨c, ?_, ?_, e'⟩
  · rintro rfl
    exact m2 (by rw [e', zero_smul])
  · rintro rfl
    obtain ⟨t, t0, t1⟩ := exists_pos_lt_top μ m2
    rw [e', Measure.smul_apply, smul_eq_mul] at t0 t1
    by_cases h : ν t = 0
    · exact t0 (by rw [h, mul_zero])
    · exact t1 (ENNReal.top_mul h)

theorem haar_of_compact {U : Set (Mat k r)} (hU : IsClosed U) {μ : Measure (Mt k r)}
    (hμ : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn U μ) : PI.BesselPeriodGGP.IsHaarOn U μ := by
  obtain ⟨m1, m2, m3, m4⟩ := hμ
  have : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hle : μ K ≤ μ (K ∩ amb U) := by
      refine measure_mono_ae ?_
      have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ U := by rw [ae_iff]; exact m1
      filter_upwards [hae] with x hx hK using ⟨hK, hx⟩
    exact lt_of_le_of_lt hle (m3 _ (hK.inter_right hU) fun x hx => hx.2)
  exact ⟨inferInstance, m4, m1, m2⟩

theorem exists_haar {U : Set (Mat k r)} (hU : IsClosedSubgroup U) :
    ∃ μ, GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn U μ := by
  let m : Measure (Gp U hU) := Measure.haar
  have hm : Measurable (inc : Gp U hU → Mt k r) := inc_memb.measurable
  refine ⟨m.map inc, ?_, ?_, ?_, ?_⟩
  · rw [inc_memb.map_apply]
    have : (inc : Gp U hU → Mt k r) ⁻¹' {x | Matrix.of x ∉ U} = ∅ := by
      ext x; simpa using inc_mem x
    rw [this, measure_empty]
  · intro a ha
    let g : Gp U hU := ⟨Matrix.of.symm a, ha⟩
    rw [Measure.map_map (lmulM_cont a).measurable hm]
    have : (lmulM a ∘ inc : Gp U hU → Mt k r) = inc ∘ (fun x => g * x) := rfl
    rw [this, ← Measure.map_map hm (continuous_const_mul g).measurable, map_mul_left_eq_self]
  · intro C hC _
    rw [inc_memb.map_apply]
    exact (inc_closedEmb.isCompact_preimage hC).measure_lt_top
  · intro h
    rw [Measure.map_eq_zero_iff hm.aemeasurable] at h
    exact NeZero.ne m h

theorem isHaarOn_iff {U : Set (Mat k r)} (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) :
    PI.BesselPeriodGGP.IsHaarOn U μ ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn U μ := by
  refine ⟨fun h => ?_, haar_of_compact hU.closed⟩
  obtain ⟨ν, hν⟩ := exists_haar hU
  obtain ⟨c, -, c1, e⟩ := haar_unique hU h (haar_of_compact hU.closed hν)
  refine ⟨h.2.2.1, h.2.2.2, fun C hC hCU => ?_, h.2.1⟩
  rw [e, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top c1.lt_top (hν.2.2.1 C hC hCU)

theorem isQuotRep_iff (G : Set (Mat k r)) (μG μS ν : Measure (Mt k r)) :
    GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsQuotRep G μG μS ν ↔
      ν {x | Matrix.of x ∉ G} = 0 ∧ PI.BesselPeriodGGP.IsQuotMeas μG μS ν := Iff.rfl

theorem isQuotMeas_iff {G S : Set (Mat k r)} (hG : IsClosedSubgroup G) (hSG : S ⊆ G)
    {μG μS : Measure (Mt k r)} (h1 : μG {x | Matrix.of x ∉ G} = 0)
    (h2 : μS {x | Matrix.of x ∉ S} = 0) (h3 : μS ≠ 0) (ν : Measure (Mt k r)) :
    PI.BesselPeriodGGP.IsQuotMeas μG μS ν ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsQuotRep G μG μS ν := by
  refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
  have hm : MeasurableSet {x : Mt k r | Matrix.of x ∉ G} :=
    (amb_closed hG).measurableSet.compl
  have e := h (Set.indicator {x : Mt k r | Matrix.of x ∉ G} 1) (measurable_one.indicator hm)
  rw [lintegral_indicator_one hm, h1] at e
  have hle : ∫⁻ x, Set.indicator {x : Mt k r | Matrix.of x ∉ G} (fun _ => μS Set.univ) x ∂ν ≤ 0 := by
    rw [e]
    refine lintegral_mono fun x => ?_
    by_cases hx : Matrix.of x ∈ G
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      exact bot_le
    · rw [Set.indicator_of_mem (by simpa using hx), ← lintegral_one]
      refine le_of_eq (lintegral_congr_ae ?_)
      have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ S := by rw [ae_iff]; exact h2
      filter_upwards [hae] with s hs
      rw [Set.indicator_of_mem]
      · rfl
      · intro hsx
        apply hx
        have h4 := hG.mul_mem _ (hG.inv_mem _ (hSG hs)) _ hsx
        have h5 : (Matrix.of s : Mat k r)⁻¹ * (Matrix.of s * Matrix.of x) = Matrix.of x :=
          Matrix.nonsing_inv_mul_cancel_left _ _ (hG.unit _ (hSG hs))
        exact h5 ▸ h4
  rw [lintegral_indicator_const hm, nonpos_iff_eq_zero, mul_eq_zero] at hle
  exact hle.resolve_left fun h' => h3 (Measure.measure_univ_eq_zero.mp h')

theorem psiGen_eq : @PI.BesselPeriodGGP.psiGen = @PI.BesselMapUniq.psiGen := rfl

theorem equivariant_iff {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (φ : Mat k r → Wp) :
    PI.BesselPeriodGGP.IsSPsiEquiv z (PI.BesselPeriodGGP.psiGen k r z c) π φ ↔
      GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsEquivariant k r z c π φ := Iff.rfl

theorem symmetricMeasure_l2Norm_eq_resolutionL2 {Wp : Type*} [NormedAddCommGroup Wp]
    (ν : Measure (Mt k r)) (φ : Mat k r → Wp) :
    PI.BesselPeriodGGP.l2SG ν φ = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.sectionL2NormSq ν φ := rfl

theorem fdeg_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure (Mt k r))
    (σ : Mat k r → (H →L[ℂ] H)) (w : H)
    (hm : AEStronglyMeasurable (fun x : Mt k r => ⟪w, σ (Matrix.of x) w⟫_ℂ) μ) :
    PI.BesselPeriodGGP.fdegH μ σ w = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt μ σ w := by
  unfold PI.BesselPeriodGGP.fdegH GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.coefNormSq
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (hm.norm.pow 2)]
  congr 3
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem continuousOn_of_isDSHpk {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (w : H) : ContinuousOn (fun g => σ g w) (UH (Hpk k r)) := by
  obtain ⟨P, ⟨⟨hP, hPH⟩, -⟩, -, -, hrep, -⟩ := hσ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hc : Continuous fun g : Mat k r => P * g * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h := (hrep.2.2 w).comp hc.continuousOn (s := UH (Hpk k r))
    fun g hg => (Formalism.QuantumDeterminants.uHConj _ ε (Hpk k r) P hd hPH g).mp hg
  refine h.congr fun g _ => ?_
  have : P⁻¹ * (P * g * P⁻¹) * P = g := by
    rw [Matrix.mul_assoc P, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
      Matrix.nonsing_inv_mul_cancel_right _ _ hd]
  simp only [Function.comp_apply, this]

theorem fdeg_eq_of_isDSHpk {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {μ : Measure (Mt k r)}
    (hμ : μ {x | Matrix.of x ∉ UH (Hpk k r)} = 0) (w : H) :
    PI.BesselPeriodGGP.fdegH μ σ w = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt μ σ w := by
  apply fdeg_eq
  have hG := Formalism.FourierDecayAlt.P.B2x2.closedG k r
  have hr : μ.restrict (amb (UH (Hpk k r))) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ)
  rw [← hr]
  have hc : ContinuousOn (fun x : Mt k r => ⟪w, σ (Matrix.of x) w⟫_ℂ) (amb (UH (Hpk k r))) :=
    continuousOn_const.inner (continuousOn_of_isDSHpk hσ w)
  exact hc.aestronglyMeasurable (amb_closed hG).measurableSet

def uinv (k r : ℕ) (h : Mat k r) : Mat k r := Hpk k r * hᴴ * Hpk k r

theorem uinv_eq {h : Mat k r} (hh : h ∈ UH (Hpk k r)) : uinv k r h = h⁻¹ := by
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh
  refine (Matrix.inv_eq_left_inv ?_).symm
  calc uinv k r h * h = Hpk k r * (hᴴ * Hpk k r * h) := by simp only [uinv, Matrix.mul_assoc]
    _ = 1 := by rw [hU, (Formalism.QuantumDeterminants.hpkFacts k r).2.1]

theorem continuous_uinv : Continuous (uinv k r) :=
  (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const

theorem continuous_leviW : Continuous (leviW k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold leviW
  split_ifs
  · exact continuous_id.matrix_elem i j
  · exact continuous_const
  · exact continuous_const

def split (k r : ℕ) (s : Mt k r) : Mt k r × Mt k r :=
  (leviW k r (Matrix.of s), uinv k r (leviW k r (Matrix.of s)) * Matrix.of s)

theorem continuous_split : Continuous (split k r) :=
  (continuous_leviW (k := k) (r := r)).prodMk
    (((continuous_uinv (k := k) (r := r)).comp continuous_leviW).matrix_mul continuous_id)

theorem split_mul {z : Fin (2 * r + k + 1) → ℂ} {h n : Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) : split k r (h * n) = (h, n) := by
  have e : leviW k r (h * n) = h := GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.leviW_mul hh hn
  refine Prod.ext e ?_
  show uinv k r (leviW k r (h * n)) * (h * n) = n
  rw [e, uinv_eq hh.1, Matrix.nonsing_inv_mul_cancel_left _ _
    ((Formalism.FourierDecayAlt.P.B2x3.closedW k r z).unit h hh)]

theorem closedS {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : IsClosedSubgroup (Sset k r z) := by
  obtain ⟨h1, h2, h3⟩ := Formalism.QuantumDeterminants.sGroup k r z hz
  have hW := Formalism.FourierDecayAlt.P.B2x3.closedW k r z
  have hN := Formalism.FourierDecayAlt.P.B2x2.closedN k r
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · rintro a ⟨h, hh, n, hn, rfl⟩
    rw [Matrix.det_mul]
    exact (hW.unit h hh).mul (hN.unit n hn)
  · have e : Sset k r z = split k r ⁻¹' (amb (UWset k r z) ×ˢ amb (Nset k r)) := by
      ext s
      constructor
      · rintro ⟨h, hh, n, hn, rfl⟩
        show split k r (h * n) ∈ amb (UWset k r z) ×ˢ amb (Nset k r)
        rw [split_mul hh hn]
        exact ⟨hh, hn⟩
      · rintro ⟨hh, hn⟩
        have hh' : leviW k r s ∈ UWset k r z := hh
        refine ⟨_, hh', uinv k r (leviW k r s) * s, hn, ?_⟩
        rw [uinv_eq hh'.1, Matrix.mul_nonsing_inv_cancel_left _ _ (hW.unit _ hh')]
    rw [e]
    exact ((amb_closed hW).prod (amb_closed hN)).preimage continuous_split

theorem ae_prod {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
  have := hW.1
  have := hN.1
  have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
  have h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := by rw [ae_iff]; exact hN.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)

theorem map_split {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) :
    ((μW.prod μN).map mulM).map (split k r) = μW.prod μN := by
  rw [Measure.map_map continuous_split.measurable mulM_cont.measurable]
  conv_rhs => rw [← Measure.map_id (μ := μW.prod μN)]
  refine Measure.map_congr ?_
  filter_upwards [ae_prod hW hN] with p hp
  exact split_mul hp.1 hp.2

theorem haar_prod {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW μN : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) :
    PI.BesselPeriodGGP.IsHaarOn (Sset k r z) ((μW.prod μN).map mulM) := by
  have := hW.1
  have := hN.1
  have cW := Formalism.FourierDecayAlt.P.B2x3.closedW k r z
  have hm : Measurable (mulM : Mt k r × Mt k r → Mt k r) := mulM_cont.measurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SigmaFinite.of_map _ continuous_split.measurable.aemeasurable
      (by rw [map_split hW hN]; infer_instance)
  · intro h
    rw [Measure.map_eq_zero_iff hm.aemeasurable] at h
    have h' := congrArg (fun m : Measure (Mt k r × Mt k r) => m (Set.univ ×ˢ Set.univ)) h
    simp only [Measure.prod_prod, Measure.coe_zero, Pi.zero_apply, mul_eq_zero,
      Measure.measure_univ_eq_zero] at h'
    exact h'.elim hW.2.1 hN.2.1
  · rw [← ae_iff]
    refine (ae_map_iff hm.aemeasurable (amb_closed (closedS hz)).measurableSet).mpr ?_
    filter_upwards [ae_prod hW hN] with p hp
    exact ⟨_, hp.1, _, hp.2, rfl⟩
  · rintro s ⟨h, hh, n, hn, rfl⟩
    let g : Mt k r → Mt k r → Mt k r := fun a x => lmulM (uinv k r (Matrix.of a) * n * Matrix.of a) x
    have hg : Continuous (Function.uncurry g) :=
      ((((continuous_uinv (k := k) (r := r)).comp continuous_fst).matrix_mul continuous_const).matrix_mul
        continuous_fst).matrix_mul continuous_snd
    have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
    have hp : MeasurePreserving (fun p : Mt k r × Mt k r => (lmulM h p.1, g p.1 p.2))
        (μW.prod μN) (μW.prod μN) := by
      refine MeasurePreserving.skew_product ⟨(lmulM_cont h).measurable, hW.2.2.2 h hh⟩ hg.measurable ?_
      filter_upwards [h1] with a ha
      refine hN.2.2.2 _ ?_
      have := (Formalism.QuantumDeterminants.uWNormal k r z hz _ (cW.inv_mem _ ha) n hn).1
      rwa [Matrix.nonsing_inv_nonsing_inv _ (cW.unit _ ha), ← uinv_eq ha.1] at this
    conv_rhs => rw [← hp.map_eq]
    rw [Measure.map_map (lmulM_cont _).measurable hm, Measure.map_map hm hp.measurable]
    refine Measure.map_congr ?_
    filter_upwards [ae_prod hW hN] with p hp
    show h * n * (Matrix.of p.1 * Matrix.of p.2) =
      h * Matrix.of p.1 * (uinv k r (Matrix.of p.1) * n * Matrix.of p.1 * Matrix.of p.2)
    rw [uinv_eq hp.1.1]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (cW.unit _ hp.1)]

theorem integral_map_of_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) (f : Mt k r → E) :
    ∫ s, f s ∂((μW.prod μN).map mulM) = ∫ p, f (mulM p) ∂(μW.prod μN) := by
  have hm : Measurable (mulM : Mt k r × Mt k r → Mt k r) := mulM_cont.measurable
  by_cases hf : AEStronglyMeasurable f ((μW.prod μN).map mulM)
  · exact integral_map hm.aemeasurable hf
  · rw [integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable]
    intro h
    apply hf
    rw [← map_split hW hN] at h
    refine (h.comp_measurable continuous_split.measurable).congr ?_
    have hc : Continuous fun s : Mt k r => mulM (split k r s) := mulM_cont.comp continuous_split
    have : ∀ᵐ s ∂((μW.prod μN).map mulM), mulM (split k r s) = s := by
      refine (ae_map_iff hm.aemeasurable (isClosed_eq hc continuous_id).measurableSet).mpr ?_
      filter_upwards [ae_prod hW hN] with p hp
      exact congrArg mulM (split_mul hp.1 hp.2)
    filter_upwards [this] with s hs
    exact congrArg f hs

theorem star_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (n : Mat k r) :
    star (PI.BesselPeriodGGP.psiGen k r z c n) = (PI.BesselMapUniq.psiGen k r z c n)⁻¹ := by
  rw [psiGen_eq]
  unfold PI.BesselMapUniq.psiGen
  rw [← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, neg_mul]

theorem period_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW μN μS : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN)
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn (Sset k r z) μS) :
    ∃ t : ℝ, 0 < t ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (c : Fin r → ℂ)
      (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Wp →L[ℂ] Wp)) (w v : H),
      GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.period k r z c σ π μS w v =
        t • ∫ p : Mt k r × Mt k r,
          (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ *
            star (PI.BesselPeriodGGP.psiGen k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
          ∂(μW.prod μN) := by
  obtain ⟨t, t0, t1, e⟩ := haar_unique (closedS hz) (haar_of_compact (closedS hz).closed hS)
    (haar_prod hz hW hN)
  refine ⟨t.toReal, ENNReal.toReal_pos t0 t1, fun H _ _ Wp _ _ c σ π w v => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.period
  rw [e, integral_smul_measure, integral_map_of_split hW hN]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_prod hW hN] with p hp
  have h := (GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.twist_mul c π hp.1 hp.2
    ((Formalism.FourierDecayAlt.P.B2x3.closedW k r z).unit _ hp.1)).2
  rw [star_psiGen, ← smul_smul, ← h]
  rfl

theorem isHCParam_of_interlaces {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hi : GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.Interlaces r k lam u)
    (hp : GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.Parity r k lam u) : Formalism.QuantumDeterminants.IsHCParam u := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have hlt : i.val < j.val := hij
    have hj := j.isLt
    have h1 := hi.1 i
    have h2 := hi.2 (j.val - 1) (by omega)
    have e : (⟨j.val - 1 + 1, by omega⟩ : Fin k) = j := Fin.ext (by simp only; omega)
    rw [e] at h2
    have h3 := hl.1.antitone (a := ⟨i.val, by omega⟩) (b := ⟨j.val - 1, by omega⟩)
      (by simp only [Fin.le_def]; omega)
    linarith
  · obtain ⟨m, hm⟩ := hl.2 0
    obtain ⟨j, hj⟩ := hp 0 a
    refine ⟨m - j + r, ?_⟩
    push_cast at hm ⊢
    linarith

theorem besselPeriod_iff :
    PI.BesselPeriodGGP.BesselPeriodGGP ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.BesselPeriodNeZero := by
  constructor
  · intro hA k r hk he v b u hl hi hp H _ _ σ hσ z hz hT Wp _ _ π hπ c hc μS hS x hx
    have hk1 : 1 ≤ k := by omega
    have hu := isHCParam_of_interlaces hl hi hp
    rw [← GlobalTheory.Proof.NodeGapNoncompact.interlace_iff k r hk1] at hi
    rw [← GlobalTheory.Proof.NodeGapNoncompact.parity_iff k r hk1] at hp
    rw [← GlobalTheory.Proof.NodeGapNoncompact.lam_eq k r hk1] at hl hσ hx
    rw [← GlobalTheory.Proof.NodeGapNoncompact.sign_eq k r hk1] at hσ hx
    have : CompleteSpace H := hσ.choose_spec.2.1
    have : FiniteDimensional ℂ Wp := hπ.choose_spec.2.2.1
    obtain ⟨μW, hW⟩ := exists_haar (Formalism.FourierDecayAlt.P.B2x3.closedW k r z)
    obtain ⟨μN, hN⟩ := exists_haar (Formalism.FourierDecayAlt.P.B2x2.closedN k r)
    have hW' := haar_of_compact (Formalism.FourierDecayAlt.P.B2x3.closedW k r z).closed hW
    have hN' := haar_of_compact (Formalism.FourierDecayAlt.P.B2x2.closedN k r).closed hN
    obtain ⟨g, y, hg, hy, h⟩ :=
      hA k r z c u v b hk he hz hT hc hu hl hi hp H σ hσ Wp π hπ x hx μW μN hW' hN'
    obtain ⟨t, ht, e⟩ := period_eq hz hW' hN' hS
    have hne : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.period k r z c σ π μS (σ g x) (σ y x) ≠ 0 := by
      rw [e]
      exact smul_ne_zero ht.ne' h
    exact ⟨g, hg, y, hy, Integrable.of_integral_ne_zero hne, hne⟩
  · intro hB k r z c u v b hk he hz hT hc _ hl hi hp H _ _ _ σ hσ Wp _ _ _ π hπ x hx μW μN hW hN
    have hk1 : 1 ≤ k := by omega
    rw [GlobalTheory.Proof.NodeGapNoncompact.interlace_iff k r hk1] at hi
    rw [GlobalTheory.Proof.NodeGapNoncompact.parity_iff k r hk1] at hp
    rw [GlobalTheory.Proof.NodeGapNoncompact.lam_eq k r hk1] at hl hσ hx
    rw [GlobalTheory.Proof.NodeGapNoncompact.sign_eq k r hk1] at hσ hx
    have hS := (isHaarOn_iff (closedS hz) _).mp (haar_prod hz hW hN)
    obtain ⟨g, hg, y, hy, -, h⟩ :=
      hB k r hk he v b u hl hi hp H σ hσ z hz hT Wp π hπ c hc _ hS x hx
    obtain ⟨t, -, e⟩ := period_eq hz hW hN hS
    refine ⟨g, y, hg, hy, fun h0 => h ?_⟩
    rw [e, h0, smul_zero]

theorem typings_equiv :
    (∀ (k r : ℕ) (U : Set (Mat k r)), IsClosedMatGroup U → ∀ μ : Measure (Mt k r),
      PI.BesselPeriodGGP.IsHaarOn U μ ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn U μ) ∧
    (∀ (k r : ℕ) (G S : Set (Mat k r)), IsClosedMatGroup G → S ⊆ G → ∀ μG μS ν : Measure (Mt k r),
      PI.BesselPeriodGGP.IsHaarOn G μG → PI.BesselPeriodGGP.IsHaarOn S μS →
      (PI.BesselPeriodGGP.IsQuotMeas μG μS ν ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsQuotRep G μG μS ν)) ∧
    (∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ),
      IsClosedMatGroup (UH (Hpk k r)) ∧ IsClosedMatGroup (UWset k r z) ∧ IsClosedMatGroup (Nset k r) ∧
        (inWb k r z → IsClosedMatGroup (Sset k r z))) ∧
    (∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
      (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (φ : Mat k r → Wp),
      PI.BesselPeriodGGP.IsSPsiEquiv z (PI.BesselPeriodGGP.psiGen k r z c) π φ ↔
        GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsEquivariant k r z c π φ) ∧
    (∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] (ν : Measure (Mt k r)) (φ : Mat k r → Wp),
      PI.BesselPeriodGGP.l2SG ν φ = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.sectionL2NormSq ν φ) ∧
    (∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure (Mt k r))
      (σ : Mat k r → (H →L[ℂ] H)) (w : H),
      AEStronglyMeasurable (fun x : Mt k r => ⟪w, σ (Matrix.of x) w⟫_ℂ) μ →
      PI.BesselPeriodGGP.fdegH μ σ w = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt μ σ w) ∧
    (∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (σ : Mat k r → (H →L[ℂ] H)),
      PI.UpqRep.IsDSHpk k r ε lam σ → ∀ μ : Measure (Mt k r),
      PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μ → ∀ w : H,
      PI.BesselPeriodGGP.fdegH μ σ w = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt μ σ w) ∧
    (PI.BesselPeriodGGP.BesselPeriodGGP ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.BesselPeriodNeZero) :=
  ⟨fun _ _ U hU μ => isHaarOn_iff ((closedSubgroup_iff U).mp hU) μ,
    fun _ _ G _ hG hSG _ _ ν h1 h2 =>
      isQuotMeas_iff ((closedSubgroup_iff G).mp hG) hSG h1.2.2.1 h2.2.2.1 h2.2.1 ν,
    fun k r z => ⟨(closedSubgroup_iff _).mpr (Formalism.FourierDecayAlt.P.B2x2.closedG k r),
      (closedSubgroup_iff _).mpr (Formalism.FourierDecayAlt.P.B2x3.closedW k r z),
      (closedSubgroup_iff _).mpr (Formalism.FourierDecayAlt.P.B2x2.closedN k r),
      fun hz => (closedSubgroup_iff _).mpr (closedS hz)⟩,
    fun _ _ _ _ _ z c π φ => equivariant_iff z c π φ,
    fun _ _ _ _ ν φ => symmetricMeasure_l2Norm_eq_resolutionL2 ν φ,
    fun _ _ _ _ _ μ σ w h => fdeg_eq μ σ w h,
    fun _ _ _ _ _ _ _ _ hσ _ hμ w => fdeg_eq_of_isDSHpk hσ hμ.2.2.1 w,
    besselPeriod_iff⟩

end GlobalTheory.BesselPeriodCompare

end
