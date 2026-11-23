import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorSingle
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirst
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagFrameAtGoodPointStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace PositivityTheory.Xgp.c_cov_self

open GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

def idCover (M : FlagModel y Ψ N j) : FlagCover M M where
  κ := id
  v := id
  block := ⟨Function.injective_id, Function.injective_id, fun _ => rfl, fun q _ => ⟨q, rfl⟩⟩
  φ := RingHom.id _
  x_eq _ := rfl
  deg_pos := by
    show 0 < IntermediateField.relfinrank (blockFnField M.x) (blockFnField M.x)
    rw [IntermediateField.relfinrank_self]; exact one_pos
  agree z hz F' F h' h g' g τ a b := ⟨all_mem hz h h' g g' τ a b, all_mem hz h' h g' g τ a b⟩

theorem trans_eq (M : FlagModel y Ψ N j) (F' F : FrameData ι Ψ N M.Ω M.blk) (zb) (τ : Ψ) :
    (idCover M).trans F' F zb τ = valMat M.x zb ((F.T τ)⁻¹ * F'.T τ) := rfl

theorem log_refNorm_congr {a : K → ℤ} {z z' : (Σ k, ι k) → ℂ}
    (h : ∀ k, a k ≠ 0 → ∀ m, z ⟨k, m⟩ = z' ⟨k, m⟩) : refNorm a z = refNorm a z' := by
  unfold refNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : a k = 0
  · simp [hk]
  · simp only [h k hk]

theorem metric_self [Fintype Ψ] [DecidableEq Ψ] (M : FlagModel y Ψ N j) (z : (Σ k, ι k) → ℂ)
    (hz : z ∈ mcPts (mCoordIdeal y)) (z₀ : (Σ k, ι k) → ℂ) (F' F : FrameData ι Ψ N M.Ω M.blk)
    (h' : M.IsFrame F') (h : M.IsFrame F) (g' : M.GoodAt F' (mCoordIdeal (basePart M.blk z)))
    (g : M.GoodAt F (mCoordIdeal (basePart M.blk z))) (ho : SameOrbit (basePart M.blk z₀) (basePart M.blk z))
    (p : Ψ × Fin N) (H : Matrix (Fin N) (Fin N) ℂ) (hH : IsBlockDiag j H) (e' : M.ExactAt F' p z H)
    (e : M.ExactAt F p z₀ ((idCover M).trans F' F (basePart M.blk z) p.1 * H)) :
    Real.log ((fsHerm ι (M.dy p)).h z) + M.upsLog F' p z =
      Real.log ((fsHerm ι (M.dy p)).h z₀) + M.upsLog F p z₀ +
        Real.log ‖detFac j p.2 ((idCover M).trans F' F (basePart M.blk z) p.1)‖ := by
  have hzb := CPts.base_mem M hz
  have hT := FibreCount.trans_unit (idCover M) hzb h' h g' g p.1
  have hd := CPts.detFac_ne_zero M.j_le p.2 hT.1 hT.2
  have hρ := rhoC_ne g g' p
  have hval : ∀ s, valAt M.x s (basePart M.blk z₀) = valAt M.x s (basePart M.blk z) := valAt_orbit ho hzb
  rw [trans_eq] at hd e ⊢
  set dd := detFac j p.2 (valMat M.x (basePart M.blk z) ((F.T p.1)⁻¹ * F'.T p.1)) with hdd
  set ρ := rhoC M F F' p (basePart M.blk z) with hρd
  obtain ⟨c, hc, hco⟩ := ho
  have hρc : ρ = ∏ k, c k ^ M.b p k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    have h1 := e.1 k
    rw [hco] at h1
    rw [e'.1 k, one_div, ← eq_inv_of_mul_eq_one_left h1]
  let t : K → ℂ := fun k => if hk : ∀ p', M.blk p' ≠ some k then c ⟨k, hk⟩ else
    if M.blk p = some k then ρ / dd else 1
  have ht : ∀ k, t k ≠ 0 := fun k => by
    simp only [t]
    split_ifs
    · exact hc _
    · exact div_ne_zero hρ hd
    · exact one_ne_zero
  have e1 : refNorm (M.dy p) z₀ = refNorm (M.dy p) fun q => t q.1 * z q := by
    refine log_refNorm_congr fun k hk m => ?_
    by_cases hb : ∀ p', M.blk p' ≠ some k
    · simp only [t, dif_pos hb]
      exact congrFun hco ⟨⟨k, hb⟩, m⟩
    · have hp : M.blk p = some k := by
        by_contra hp
        exact hk (by simp only [FlagModel.dy, dif_neg hb, if_neg hp])
      simp only [t, dif_neg hb, if_pos hp]
      have r := relC hzb h h' g g' hp H hH m
      rw [e.2 k hp m, e'.2 k hp m]
      simp only [hval]
      rw [← hdd, ← hρd] at r
      field_simp
      linear_combination r
  have e2 : (∏ k, ‖t k‖ ^ M.dy p k) = ‖ρ‖⁻¹ * (M.blk p).elim 1 fun _ => ‖ρ‖ / ‖dd‖ := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => ∀ p', M.blk p' ≠ some k)]
    congr 1
    · rw [hρc, norm_prod, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr (by congr; exact Subsingleton.elim _ _) fun k _ => ?_
      simp only [t, FlagModel.dy, dif_pos k.2, _root_.zpow_neg, norm_zpow]
    · cases hp : M.blk p with
      | none =>
        refine Finset.prod_eq_one fun k _ => ?_
        have : M.blk p ≠ some k.1 := by rw [hp]; simp
        simp only [FlagModel.dy, dif_neg k.2, if_neg this, _root_.zpow_zero]
      | some k₀ =>
        have hk₀ : ¬ ∀ p', M.blk p' ≠ some k₀ := fun e => e p hp
        rw [Finset.prod_eq_single ⟨k₀, hk₀⟩]
        · simp only [t, FlagModel.dy, dif_neg hk₀, if_pos hp, _root_.zpow_one, norm_div, Option.elim_some]
        · intro k _ hk
          have : M.blk p ≠ some k.1 := fun e => hk (Subtype.ext (Option.some.inj (e.symm.trans hp)))
          simp only [FlagModel.dy, dif_neg k.2, if_neg this, _root_.zpow_zero]
        · simp
  have e3 := (fsHerm ι (M.dy p)).smul t z ht
  have hpos := (fsHerm ι (M.dy p)).pos z hz.1
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ
  have hdn : 0 < ‖dd‖ := norm_pos_iff.2 hd
  have e4 : (fsHerm ι (M.dy p)).h z₀ =
      (‖ρ‖⁻¹ * (M.blk p).elim 1 fun _ => ‖ρ‖ / ‖dd‖) * (fsHerm ι (M.dy p)).h z := by
    rw [← e2]; exact e1.trans e3
  rw [e4]
  unfold FlagModel.upsLog
  cases hp : M.blk p with
  | none =>
    have r := congrArg (fun w => Real.log ‖w‖) (rel0C hzb h h' g g' hp)
    have u1 := norm_pos_iff.2 (ups_ne hzb g hp)
    have u2 := norm_pos_iff.2 (ups_ne hzb g' hp)
    simp only [← hdd, ← hρd, norm_mul] at r
    rw [Real.log_mul hdn.ne' u1.ne', Real.log_mul hρn.ne' u2.ne'] at r
    simp only [Option.elim_none, mul_one, hval]
    rw [Real.log_mul (inv_pos.2 hρn).ne' hpos.ne', Real.log_inv]
    linarith
  | some k =>
    simp only [Option.elim_some]
    rw [← mul_div_assoc, inv_mul_cancel₀ hρn.ne', Real.log_mul (one_div_pos.2 hdn).ne' hpos.ne', one_div,
      Real.log_inv]
    ring

theorem isImg_self [Fintype Ψ] [DecidableEq Ψ] (M : FlagModel y Ψ N j) (z : (Σ k, ι k) → ℂ)
    (hz : z ∈ mcPts (mCoordIdeal y)) (F' F : FrameData ι Ψ N M.Ω M.blk)
    (h' : M.IsFrame F') (h : M.IsFrame F) (g' : M.GoodAt F' (mCoordIdeal (basePart M.blk z)))
    (g : M.GoodAt F (mCoordIdeal (basePart M.blk z))) (H : Ψ → Matrix (Fin N) (Fin N) ℂ) (hH : M.IsFlagOf F' z H) :
    ∃ z₀, SameOrbit z₀ z ∧ SameOrbit (basePart M.blk z₀) (basePart M.blk z) ∧
      M.IsFlagOf F z₀ fun τ => (idCover M).trans F' F (basePart M.blk z) τ * H τ := by
  have hzb := CPts.base_mem M hz
  have hT := FibreCount.trans_unit (idCover M) hzb h' h g' g
  refine (GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F z _ h hzb g (fun τ => ⟨(hT τ).1.mul (hH.2.1 τ).1, by
    rw [det_mul]; exact mul_ne_zero (hT τ).2 (hH.2.1 τ).2⟩) fun p k hp => ?_).2
  obtain ⟨a, ha, hz'⟩ := hH.2.2 p k hp
  have hd := CPts.detFac_ne_zero M.j_le p.2 (hT p.1).1 (hT p.1).2
  have hρ := rhoC_ne g g' p
  refine ⟨a * detFac j p.2 ((idCover M).trans F' F (basePart M.blk z) p.1) / rhoC M F F' p (basePart M.blk z),
    div_ne_zero (mul_ne_zero ha hd) hρ, fun m => ?_⟩
  have r := relC hzb h h' g g' hp (H p.1) (hH.2.1 p.1).1 m
  rw [hz' m, plk, trans_eq, div_mul_eq_mul_div, mul_assoc, r]
  field_simp

end PositivityTheory.Xgp.c_cov_self
end

theorem PositivityTheory.Xgp.t_c_cov_self : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), ∃ (Cv : FlagCover M M) (CR : CovReal FA Cv), Cv.deg = 1 ∧ (∀ p, CR.Re.ref p = FA.Re.ref (some p)) ∧ ∀ p t, CR.Re.line p t = FA.Re.line (some p) t := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hJ : ∀ z, z ∉ mcPts FA.Re.J := fun z h => by
    rw [FA.J_top] at h
    simpa using h.2 1 trivial
  have hne : Nonempty FA.S.X := FA.Re.nonempty_base
  let ϖ : ((Σ k, ι k) → ℂ) → FA.S.X := fun z =>
    if h : ∃ x, SameOrbit (FA.Re.R.lift x x) z then FA.Re.π h.choose else hne.some
  have hϖ : ∀ z x, SameOrbit (FA.Re.R.lift x x) z → ϖ z = FA.Re.π x := by
    intro z x hx
    have h : ∃ x, SameOrbit (FA.Re.R.lift x x) z := ⟨x, hx⟩
    simp only [ϖ, dif_pos h]
    rw [FA.Re.R.inj _ x (hJ _) (Cj.sameOrbit_trans h.choose_spec (Cj.sameOrbit_symm hx))]
  have hinj : Function.Injective FA.Re.π := by
    intro x x' hx
    have h1 := FA.Re.degree.2.2.2.2.1 (FA.Re.π x') (by rw [FA.br_empty]; exact Set.notMem_empty _)
    rw [FA.deg_one, Set.ncard_eq_one] at h1
    obtain ⟨a, ha⟩ := h1
    have m1 : x ∈ FA.Re.π ⁻¹' {FA.Re.π x'} := hx
    have m2 : x' ∈ FA.Re.π ⁻¹' {FA.Re.π x'} := rfl
    rw [ha] at m1 m2
    exact m1.trans m2.symm
  have hdeg : (PositivityTheory.Xgp.c_cov_self.idCover M).deg = 1 := IntermediateField.relfinrank_self _
  refine ⟨PositivityTheory.Xgp.c_cov_self.idCover M,
    { Re := FA.Re.comap some
      deg_eq := FA.deg_one.trans hdeg.symm
      ref_deg := fun p => congrArg HermLine.a (FA.ref_some p)
      step := FA.step
      ϖ := ϖ
      ϖ_torus := ?_
      π_eq := fun x => (hϖ _ x (Cj.sameOrbit_refl _)).symm
      line_pt := ?_
      flags := ?_
      metric := ?_ }, hdeg, fun _ => rfl, fun _ _ => rfl⟩
  · intro z z' hz ho
    obtain ⟨x, hx⟩ := FA.Re.R.surj z hz (hJ z)
    rw [hϖ z x hx, hϖ z' x (Cj.sameOrbit_trans hx (Cj.sameOrbit_symm ho))]
  · intro p t h0 h1 z hz
    obtain ⟨x, hx⟩ := FA.Re.R.surj z hz (hJ z)
    have e1 := FA.Re.line_eq (some p) t h0 h1 x
    have e2 := Cj.log_sub_orbit _ _ (FA.Re.line_deg (some p) t) hz.1 hx
    rw [hϖ z x hx]
    show Real.log ((FA.Re.line (some p) t).h z) = Real.log ((FA.Re.ref (some p)).h z) + _
    linarith
  · intro z hz F' F h' h g' g H hH x₀ hx₀
    obtain ⟨x, hx⟩ := FA.Re.R.surj z hz (hJ z)
    rw [hϖ z x hx] at hx₀
    obtain rfl := hinj hx₀
    obtain ⟨z₀, o1, o2, fl⟩ := PositivityTheory.Xgp.c_cov_self.isImg_self M z hz F' F h' h g' g H hH
    exact ⟨z₀, Cj.sameOrbit_trans o1 (Cj.sameOrbit_symm hx), o2, fl⟩
  · intro z hz z₀ _ F' F h' h g' g ho p H hH _ e' e
    have := PositivityTheory.Xgp.c_cov_self.metric_self M z hz z₀ F' F h' h g' g ho p H hH e' e
    rw [← FA.ref_some p] at this
    rw [← FA.ref_some p]
    exact this
