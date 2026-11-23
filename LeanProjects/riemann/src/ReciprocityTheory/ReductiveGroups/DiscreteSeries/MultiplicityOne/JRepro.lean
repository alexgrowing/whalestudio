import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JReproB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSInt

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem second_joint_integrable (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hCG : IsClosedSubgroup (GV k r)) (hCW : IsClosedSubgroup (UWset k r D.z)) (hCN : IsClosedSubgroup (Nset k r))
    (hL : ∀ g ∈ GV k r, 1 ≤ gN g) (ha : 0 ≤ X.a)
    (hIG : Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG)
    (hIS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
      (D.μW.prod D.μN))
    {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2) (D.μG.prod (D.μW.prod D.μN)) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μG := ⟨fun _ hK => D.haarG.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  obtain ⟨Cu, hCu0, hCu⟩ := dec_adj X hCG hL ha hu
  obtain ⟨Cv, hCv0, hCv⟩ := dec_adj X hCG hL ha hv
  have hform : ∀ q ∈ EE k r D.z,
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2 =
        ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • ((⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ *
          star (psiD D (Matrix.of q.2.2))) • ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))) := by
    intro q hq
    obtain ⟨_, hh, _⟩ := hq
    simp only [beInt, mc]
    rw [pi_inv D hCW hh]
  have hcont : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2) (EE k r D.z) := by
    refine ContinuousOn.congr ?_ hform
    exact (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (cont_sig_fst X D.z X.w)).smul
      (((ContinuousOn.inner (𝕜 := ℂ) (cont_sig_fst X D.z X.w) (representation_continuousOn_product X D.z hCG u)).mul
        (cont_psi D).continuousOn).smul (cont_adj_pi D))
  have hmeas : AEStronglyMeasurable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2)
      (D.μG.prod (D.μW.prod D.μN)) := by
    have := hcont.aestronglyMeasurable (μ := D.μG.prod (D.μW.prod D.μN)) (EE_closed D.z hCG hCW hCN).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (ae_EE D)] at this
  have hbd : ∀ᵐ q ∂(D.μG.prod (D.μW.prod D.μN)),
      ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2‖ ≤
        Cv * Cu * KH k r ^ (X.a / 2) * KH k r ^ (X.a / 2) *
          (gN (Matrix.of q.1) ^ (-(X.a / 2)) * gN (Matrix.of q.2.2 * Matrix.of q.2.1) ^ (-(X.a / 2))) := by
    filter_upwards [ae_EE D] with q hq
    rw [hform q hq]
    obtain ⟨hy, hh, hn⟩ := hq
    have hs : Matrix.of q.2.2 * Matrix.of q.2.1 ∈ GV k r := hCG.mul_mem _ hn.1 _ hh.1
    have hsi := inv_mem_G hCG hs
    have A1 : ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ ≤ Cv * gN (Matrix.of q.1) ^ (-X.a) := hCv _ hy
    have e : ⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ =
        ⟪X.σ ((Matrix.of q.2.2 * Matrix.of q.2.1)⁻¹ * Matrix.of q.1) X.w, u⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← sig_inv X hCG hs, X.rep.1.2 _ hsi _ hy]; rfl
    have A2 : ‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ ≤
        Cu * gN ((Matrix.of q.2.2 * Matrix.of q.2.1)⁻¹ * Matrix.of q.1) ^ (-X.a) := by
      rw [e, norm_inner_symm]; exact hCu _ (hCG.mul_mem _ hsi _ hy)
    have B := second_pointwise_bound hCG hL ha hs hy A1 A2 (norm_nonneg _) (norm_nonneg _) hCv0 hCu0
    have hT : ‖ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact opNorm_le_one_of_iso (D.π_unitary _ hh)
    have hψ : ‖star (psiD D (Matrix.of q.2.2))‖ ≤ 1 := by rw [norm_star]; exact norm_psi_le _ _ _
    rw [norm_smul, norm_smul, norm_mul]
    calc ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ *
          (‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ *
          ‖star (psiD D (Matrix.of q.2.2))‖ * ‖ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))‖)
        ≤ ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ *
          (‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ * 1 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hψ (norm_nonneg _)) hT
            (norm_nonneg _) (by positivity)) (norm_nonneg _)
      _ = ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ *
          ‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ := by ring
      _ ≤ _ := B
  exact ((hIG.mul_prod hIS).const_mul (Cv * Cu * KH k r ^ (X.a / 2) * KH k r ^ (X.a / 2))).mono' hmeas hbd

theorem reproducing_snd (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hCG : IsClosedSubgroup (GV k r)) (hCW : IsClosedSubgroup (UWset k r D.z)) (hCN : IsClosedSubgroup (Nset k r))
    (hL : ∀ g ∈ GV k r, 1 ≤ gN g) (ha : 0 ≤ X.a)
    (hIG : Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG)
    (hIS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
      (D.μW.prod D.μN))
    {d : ℝ} (hd : IsFdegG D X d) {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    beOp D X u v = (d : ℂ) •
      ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beOp D X u (X.σ (Matrix.of y) X.w) ∂D.μG := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μG := ⟨fun _ hK => D.haarG.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  have hint := second_joint_integrable D X hCG hCW hCN hL ha hIG hIS hu hv
  have hpt : ∀ p : Mt k r × Mt k r,
      ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of y) X.w) p ∂D.μG =
        ((d : ℂ)⁻¹) • beInt D X u v p := by
    intro p
    simp only [beInt, smul_smul]
    rw [integral_smul_const]
    congr 1
    have e : ∀ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ *
        (mc X u (X.σ (Matrix.of y) X.w) (Matrix.of p.2 * Matrix.of p.1) * star (psiD D (Matrix.of p.2))) =
        ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of p.2 * Matrix.of p.1) u⟫_ℂ * ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ *
          star (psiD D (Matrix.of p.2)) := by
      intro y; rw [mc]; ring
    simp_rw [e]
    rw [integral_mul_const, schur_pt D X hd v (X.σ (Matrix.of p.2 * Matrix.of p.1) u), mc]
    ring
  have hsw := swap_smul D.μG (D.μW.prod D.μN) (fun y : Mt k r => ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ)
    (fun (y : Mt k r) (p : Mt k r × Mt k r) => beInt D X u (X.σ (Matrix.of y) X.w) p) hint
  have key : ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beOp D X u (X.σ (Matrix.of y) X.w) ∂D.μG =
      ((d : ℂ)⁻¹) • beOp D X u v := by
    simp only [beOp]
    rw [hsw]
    simp_rw [hpt]
    rw [integral_smul]
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  rw [key, smul_smul, mul_inv_cancel₀ hd0, one_smul]

end ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReproducingFormula

section

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem repro_setup (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (haM : aM k r ≤ X.a) :
    IsClosedSubgroup (GV k r) ∧ IsClosedSubgroup (UWset k r D.z) ∧ IsClosedSubgroup (Nset k r) ∧
      (∀ g ∈ GV k r, 1 ≤ gN g) ∧ 0 ≤ X.a ∧
      Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG ∧
      Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
        (D.μW.prod D.μN) := by
  have h' := h
  obtain ⟨hB2, -⟩ := h'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hGI, hGL, -, -, -, hCG, hCN, hCW, -⟩ := hB2
  have ha : 0 ≤ X.a := le_trans (by unfold aM nR; positivity) haM
  have hAB := AB_le_half k r haM
  exact ⟨hCG k r, hCW k r D.z, hCN k r, hGL k r, ha, int_G hGI D.μG D.haarG hAB,
    stSInt h k r Wp D hD (X.a / 2) hAB⟩

theorem stRepro_integrable (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D)
    (haM : aM k r ≤ X.a) {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v) D.μG := by
  obtain ⟨hCG, hCW, hCN, hL, ha, hIG, hIS⟩ := repro_setup h D X hD haM
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  refine (first_joint_integrable D X hCG hCW hCN hL ha hIG hIS hu hv).integral_prod_left.congr
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [beOp]
  exact integral_smul _ _

theorem stRepro_integrable₂ (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D)
    (haM : aM k r ≤ X.a) {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    Integrable (fun y : Mt k r => ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beOp D X u (X.σ (Matrix.of y) X.w)) D.μG := by
  obtain ⟨hCG, hCW, hCN, hL, ha, hIG, hIS⟩ := repro_setup h D X hD haM
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  refine (second_joint_integrable D X hCG hCW hCN hL ha hIG hIS hu hv).integral_prod_left.congr
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [beOp]
  exact integral_smul _ _

end

theorem stRepro (h : UnitaryGroupStructuralFacts) : StRepro := by
  intro k r Wp _ _ _ D X hD _ haM d hd u hu v hv
  obtain ⟨hCG, hCW, hCN, hL, ha, hIG, hIS⟩ := repro_setup h D X hD haM
  exact ⟨reproducing_fst D X hCG hCW hCN hL ha hIG hIS hd hu hv, reproducing_snd D X hCG hCW hCN hL ha hIG hIS hd hu hv⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
